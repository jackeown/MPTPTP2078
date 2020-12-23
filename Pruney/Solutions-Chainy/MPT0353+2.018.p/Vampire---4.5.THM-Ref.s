%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   91 (1097 expanded)
%              Number of leaves         :   13 ( 366 expanded)
%              Depth                    :   19
%              Number of atoms          :  123 (1742 expanded)
%              Number of equality atoms :   86 (1015 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7378,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f7377])).

fof(f7377,plain,(
    k6_subset_1(sK1,sK2) != k6_subset_1(sK1,sK2) ),
    inference(superposition,[],[f1075,f7246])).

fof(f7246,plain,(
    k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2)) = k6_subset_1(sK1,sK2) ),
    inference(forward_demodulation,[],[f7198,f3283])).

fof(f3283,plain,(
    ! [X1] : k6_subset_1(sK1,X1) = k9_subset_1(sK0,k5_xboole_0(sK0,X1),sK1) ),
    inference(superposition,[],[f2865,f1950])).

fof(f1950,plain,(
    ! [X18] : k9_subset_1(sK0,X18,sK1) = k5_xboole_0(X18,k6_subset_1(X18,sK1)) ),
    inference(resolution,[],[f1347,f23])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f21,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2))
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(f1347,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k5_xboole_0(X1,k6_subset_1(X1,X2)) ) ),
    inference(forward_demodulation,[],[f44,f593])).

fof(f593,plain,(
    ! [X0,X1] : k6_subset_1(X0,k6_subset_1(X0,X1)) = k5_xboole_0(X0,k6_subset_1(X0,X1)) ),
    inference(backward_demodulation,[],[f78,f428])).

fof(f428,plain,(
    ! [X0,X1] : k3_subset_1(X0,k6_subset_1(X0,X1)) = k5_xboole_0(X0,k6_subset_1(X0,X1)) ),
    inference(forward_demodulation,[],[f413,f48])).

fof(f48,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k3_subset_1(X0,k3_subset_1(X0,k6_subset_1(X0,X1))) ),
    inference(resolution,[],[f33,f27])).

fof(f27,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f413,plain,(
    ! [X0,X1] : k3_subset_1(X0,k6_subset_1(X0,X1)) = k5_xboole_0(X0,k3_subset_1(X0,k3_subset_1(X0,k6_subset_1(X0,X1)))) ),
    inference(superposition,[],[f266,f78])).

fof(f266,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k5_xboole_0(X0,k3_subset_1(X0,k6_subset_1(X0,X1))) ),
    inference(backward_demodulation,[],[f40,f78])).

fof(f40,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k5_xboole_0(X0,k6_subset_1(X0,k6_subset_1(X0,X1))) ),
    inference(definition_unfolding,[],[f30,f28,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f31,f28,f28])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f78,plain,(
    ! [X0,X1] : k6_subset_1(X0,k6_subset_1(X0,X1)) = k3_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(resolution,[],[f41,f27])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f28])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k6_subset_1(X1,k6_subset_1(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f2865,plain,(
    ! [X47] : k5_xboole_0(k5_xboole_0(sK0,X47),k6_subset_1(k5_xboole_0(sK0,X47),sK1)) = k6_subset_1(sK1,X47) ),
    inference(forward_demodulation,[],[f2864,f1961])).

fof(f1961,plain,(
    ! [X1] : k6_subset_1(sK1,X1) = k5_xboole_0(sK1,k9_subset_1(sK0,X1,sK1)) ),
    inference(superposition,[],[f594,f1950])).

fof(f594,plain,(
    ! [X2,X1] : k6_subset_1(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k6_subset_1(X2,X1))) ),
    inference(backward_demodulation,[],[f265,f428])).

fof(f265,plain,(
    ! [X2,X1] : k6_subset_1(X1,X2) = k5_xboole_0(X1,k3_subset_1(X2,k6_subset_1(X2,X1))) ),
    inference(backward_demodulation,[],[f63,f78])).

fof(f63,plain,(
    ! [X2,X1] : k6_subset_1(X1,X2) = k5_xboole_0(X1,k6_subset_1(X2,k6_subset_1(X2,X1))) ),
    inference(superposition,[],[f40,f39])).

fof(f39,plain,(
    ! [X0,X1] : k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f29,f37,f37])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f2864,plain,(
    ! [X47] : k5_xboole_0(k5_xboole_0(sK0,X47),k6_subset_1(k5_xboole_0(sK0,X47),sK1)) = k5_xboole_0(sK1,k9_subset_1(sK0,X47,sK1)) ),
    inference(forward_demodulation,[],[f2863,f110])).

fof(f110,plain,(
    sK1 = k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f99,f109])).

fof(f109,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f84,f89])).

fof(f89,plain,(
    sK1 = k6_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f87,f46])).

fof(f46,plain,(
    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f33,f23])).

fof(f87,plain,(
    k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k6_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f86,f41])).

fof(f86,plain,(
    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f27,f76])).

fof(f76,plain,(
    k3_subset_1(sK0,sK1) = k6_subset_1(sK0,sK1) ),
    inference(resolution,[],[f41,f23])).

fof(f84,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k6_subset_1(sK0,k3_subset_1(sK0,sK1))) ),
    inference(superposition,[],[f40,f76])).

fof(f99,plain,(
    sK1 = k5_xboole_0(sK0,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f96,f76])).

fof(f96,plain,(
    sK1 = k5_xboole_0(sK0,k6_subset_1(sK0,sK1)) ),
    inference(superposition,[],[f40,f89])).

fof(f2863,plain,(
    ! [X47] : k5_xboole_0(k5_xboole_0(sK0,X47),k6_subset_1(k5_xboole_0(sK0,X47),sK1)) = k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k9_subset_1(sK0,X47,sK1)) ),
    inference(forward_demodulation,[],[f2743,f1950])).

fof(f2743,plain,(
    ! [X47] : k5_xboole_0(k5_xboole_0(sK0,X47),k6_subset_1(k5_xboole_0(sK0,X47),sK1)) = k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k5_xboole_0(X47,k6_subset_1(X47,sK1))) ),
    inference(superposition,[],[f1980,f113])).

fof(f113,plain,(
    k6_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f76,f109])).

fof(f1980,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X2),k6_subset_1(k5_xboole_0(X0,X2),X1)) = k5_xboole_0(k5_xboole_0(X0,k6_subset_1(X0,X1)),k5_xboole_0(X2,k6_subset_1(X2,X1))) ),
    inference(forward_demodulation,[],[f1979,f593])).

fof(f1979,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X2),k6_subset_1(k5_xboole_0(X0,X2),X1)) = k5_xboole_0(k6_subset_1(X0,k6_subset_1(X0,X1)),k5_xboole_0(X2,k6_subset_1(X2,X1))) ),
    inference(forward_demodulation,[],[f1978,f593])).

fof(f1978,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k6_subset_1(X0,k6_subset_1(X0,X1)),k6_subset_1(X2,k6_subset_1(X2,X1))) = k5_xboole_0(k5_xboole_0(X0,X2),k6_subset_1(k5_xboole_0(X0,X2),X1)) ),
    inference(forward_demodulation,[],[f42,f593])).

fof(f42,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k6_subset_1(X0,k6_subset_1(X0,X1)),k6_subset_1(X2,k6_subset_1(X2,X1))) = k6_subset_1(k5_xboole_0(X0,X2),k6_subset_1(k5_xboole_0(X0,X2),X1)) ),
    inference(definition_unfolding,[],[f34,f37,f37,f37])).

fof(f34,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f7198,plain,(
    k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2)) = k9_subset_1(sK0,k5_xboole_0(sK0,sK2),sK1) ),
    inference(superposition,[],[f3096,f130])).

fof(f130,plain,(
    k6_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) ),
    inference(backward_demodulation,[],[f77,f126])).

fof(f126,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f90,f95])).

fof(f95,plain,(
    sK2 = k6_subset_1(sK0,k3_subset_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f93,f47])).

fof(f47,plain,(
    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) ),
    inference(resolution,[],[f33,f24])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f93,plain,(
    k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = k6_subset_1(sK0,k3_subset_1(sK0,sK2)) ),
    inference(resolution,[],[f92,f41])).

fof(f92,plain,(
    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f27,f77])).

fof(f90,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k6_subset_1(sK0,k3_subset_1(sK0,sK2))) ),
    inference(superposition,[],[f40,f77])).

fof(f77,plain,(
    k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2) ),
    inference(resolution,[],[f41,f24])).

fof(f3096,plain,(
    ! [X21,X20] : k9_subset_1(sK0,k6_subset_1(X20,X21),sK1) = k9_subset_1(X20,sK1,k6_subset_1(X20,X21)) ),
    inference(superposition,[],[f1945,f1954])).

fof(f1954,plain,(
    ! [X1] : k5_xboole_0(sK1,k6_subset_1(sK1,X1)) = k9_subset_1(sK0,X1,sK1) ),
    inference(superposition,[],[f1950,f999])).

fof(f999,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k6_subset_1(X2,X3)) = k5_xboole_0(X3,k6_subset_1(X3,X2)) ),
    inference(superposition,[],[f884,f593])).

fof(f884,plain,(
    ! [X4,X5] : k6_subset_1(X5,k6_subset_1(X5,X4)) = k5_xboole_0(X4,k6_subset_1(X4,X5)) ),
    inference(superposition,[],[f593,f39])).

fof(f1945,plain,(
    ! [X8,X7,X9] : k9_subset_1(X7,X8,k6_subset_1(X7,X9)) = k5_xboole_0(X8,k6_subset_1(X8,k6_subset_1(X7,X9))) ),
    inference(resolution,[],[f1347,f27])).

fof(f1075,plain,(
    k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2)) != k6_subset_1(sK1,sK2) ),
    inference(backward_demodulation,[],[f132,f1067])).

fof(f1067,plain,(
    ! [X2] : k7_subset_1(sK0,sK1,X2) = k6_subset_1(sK1,X2) ),
    inference(resolution,[],[f43,f23])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2) ) ),
    inference(definition_unfolding,[],[f35,f28])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f132,plain,(
    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f25,f126])).

fof(f25,plain,(
    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:33:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (13474)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (13477)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (13475)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (13472)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (13484)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (13488)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (13478)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (13482)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (13476)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (13479)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (13480)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (13483)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (13473)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (13483)Refutation not found, incomplete strategy% (13483)------------------------------
% 0.21/0.49  % (13483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (13483)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (13483)Memory used [KB]: 10618
% 0.21/0.49  % (13483)Time elapsed: 0.062 s
% 0.21/0.49  % (13483)------------------------------
% 0.21/0.49  % (13483)------------------------------
% 0.21/0.50  % (13486)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (13481)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (13487)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (13489)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.51  % (13485)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.53  % (13474)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f7378,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f7377])).
% 0.21/0.53  fof(f7377,plain,(
% 0.21/0.53    k6_subset_1(sK1,sK2) != k6_subset_1(sK1,sK2)),
% 0.21/0.53    inference(superposition,[],[f1075,f7246])).
% 0.21/0.53  fof(f7246,plain,(
% 0.21/0.53    k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2)) = k6_subset_1(sK1,sK2)),
% 0.21/0.53    inference(forward_demodulation,[],[f7198,f3283])).
% 0.21/0.53  fof(f3283,plain,(
% 0.21/0.53    ( ! [X1] : (k6_subset_1(sK1,X1) = k9_subset_1(sK0,k5_xboole_0(sK0,X1),sK1)) )),
% 0.21/0.53    inference(superposition,[],[f2865,f1950])).
% 0.21/0.53  fof(f1950,plain,(
% 0.21/0.53    ( ! [X18] : (k9_subset_1(sK0,X18,sK1) = k5_xboole_0(X18,k6_subset_1(X18,sK1))) )),
% 0.21/0.53    inference(resolution,[],[f1347,f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    (k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f21,f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ? [X2] : (k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 0.21/0.53    inference(negated_conjecture,[],[f12])).
% 0.21/0.53  fof(f12,conjecture,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).
% 0.21/0.53  fof(f1347,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k5_xboole_0(X1,k6_subset_1(X1,X2))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f44,f593])).
% 0.21/0.53  fof(f593,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k6_subset_1(X0,k6_subset_1(X0,X1)) = k5_xboole_0(X0,k6_subset_1(X0,X1))) )),
% 0.21/0.53    inference(backward_demodulation,[],[f78,f428])).
% 0.21/0.53  fof(f428,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_subset_1(X0,k6_subset_1(X0,X1)) = k5_xboole_0(X0,k6_subset_1(X0,X1))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f413,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k3_subset_1(X0,k3_subset_1(X0,k6_subset_1(X0,X1)))) )),
% 0.21/0.53    inference(resolution,[],[f33,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.53  fof(f413,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_subset_1(X0,k6_subset_1(X0,X1)) = k5_xboole_0(X0,k3_subset_1(X0,k3_subset_1(X0,k6_subset_1(X0,X1))))) )),
% 0.21/0.53    inference(superposition,[],[f266,f78])).
% 0.21/0.53  fof(f266,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k5_xboole_0(X0,k3_subset_1(X0,k6_subset_1(X0,X1)))) )),
% 0.21/0.53    inference(backward_demodulation,[],[f40,f78])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k5_xboole_0(X0,k6_subset_1(X0,k6_subset_1(X0,X1)))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f30,f28,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f31,f28,f28])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k6_subset_1(X0,k6_subset_1(X0,X1)) = k3_subset_1(X0,k6_subset_1(X0,X1))) )),
% 0.21/0.53    inference(resolution,[],[f41,f27])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f32,f28])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k6_subset_1(X1,k6_subset_1(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f36,f37])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.53  fof(f2865,plain,(
% 0.21/0.53    ( ! [X47] : (k5_xboole_0(k5_xboole_0(sK0,X47),k6_subset_1(k5_xboole_0(sK0,X47),sK1)) = k6_subset_1(sK1,X47)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f2864,f1961])).
% 0.21/0.53  fof(f1961,plain,(
% 0.21/0.53    ( ! [X1] : (k6_subset_1(sK1,X1) = k5_xboole_0(sK1,k9_subset_1(sK0,X1,sK1))) )),
% 0.21/0.53    inference(superposition,[],[f594,f1950])).
% 0.21/0.53  fof(f594,plain,(
% 0.21/0.53    ( ! [X2,X1] : (k6_subset_1(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k6_subset_1(X2,X1)))) )),
% 0.21/0.53    inference(backward_demodulation,[],[f265,f428])).
% 0.21/0.53  fof(f265,plain,(
% 0.21/0.53    ( ! [X2,X1] : (k6_subset_1(X1,X2) = k5_xboole_0(X1,k3_subset_1(X2,k6_subset_1(X2,X1)))) )),
% 0.21/0.53    inference(backward_demodulation,[],[f63,f78])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X2,X1] : (k6_subset_1(X1,X2) = k5_xboole_0(X1,k6_subset_1(X2,k6_subset_1(X2,X1)))) )),
% 0.21/0.53    inference(superposition,[],[f40,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f29,f37,f37])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.53  fof(f2864,plain,(
% 0.21/0.53    ( ! [X47] : (k5_xboole_0(k5_xboole_0(sK0,X47),k6_subset_1(k5_xboole_0(sK0,X47),sK1)) = k5_xboole_0(sK1,k9_subset_1(sK0,X47,sK1))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f2863,f110])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    sK1 = k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 0.21/0.53    inference(backward_demodulation,[],[f99,f109])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 0.21/0.53    inference(forward_demodulation,[],[f84,f89])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    sK1 = k6_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 0.21/0.53    inference(forward_demodulation,[],[f87,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 0.21/0.53    inference(resolution,[],[f33,f23])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k6_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 0.21/0.53    inference(resolution,[],[f86,f41])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.21/0.53    inference(superposition,[],[f27,f76])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    k3_subset_1(sK0,sK1) = k6_subset_1(sK0,sK1)),
% 0.21/0.53    inference(resolution,[],[f41,f23])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k6_subset_1(sK0,k3_subset_1(sK0,sK1)))),
% 0.21/0.53    inference(superposition,[],[f40,f76])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    sK1 = k5_xboole_0(sK0,k3_subset_1(sK0,sK1))),
% 0.21/0.53    inference(forward_demodulation,[],[f96,f76])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    sK1 = k5_xboole_0(sK0,k6_subset_1(sK0,sK1))),
% 0.21/0.53    inference(superposition,[],[f40,f89])).
% 0.21/0.53  fof(f2863,plain,(
% 0.21/0.53    ( ! [X47] : (k5_xboole_0(k5_xboole_0(sK0,X47),k6_subset_1(k5_xboole_0(sK0,X47),sK1)) = k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k9_subset_1(sK0,X47,sK1))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f2743,f1950])).
% 0.21/0.53  fof(f2743,plain,(
% 0.21/0.53    ( ! [X47] : (k5_xboole_0(k5_xboole_0(sK0,X47),k6_subset_1(k5_xboole_0(sK0,X47),sK1)) = k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k5_xboole_0(X47,k6_subset_1(X47,sK1)))) )),
% 0.21/0.53    inference(superposition,[],[f1980,f113])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    k6_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 0.21/0.53    inference(backward_demodulation,[],[f76,f109])).
% 0.21/0.53  fof(f1980,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X2),k6_subset_1(k5_xboole_0(X0,X2),X1)) = k5_xboole_0(k5_xboole_0(X0,k6_subset_1(X0,X1)),k5_xboole_0(X2,k6_subset_1(X2,X1)))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f1979,f593])).
% 0.21/0.53  fof(f1979,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X2),k6_subset_1(k5_xboole_0(X0,X2),X1)) = k5_xboole_0(k6_subset_1(X0,k6_subset_1(X0,X1)),k5_xboole_0(X2,k6_subset_1(X2,X1)))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f1978,f593])).
% 0.21/0.53  fof(f1978,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k5_xboole_0(k6_subset_1(X0,k6_subset_1(X0,X1)),k6_subset_1(X2,k6_subset_1(X2,X1))) = k5_xboole_0(k5_xboole_0(X0,X2),k6_subset_1(k5_xboole_0(X0,X2),X1))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f42,f593])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k5_xboole_0(k6_subset_1(X0,k6_subset_1(X0,X1)),k6_subset_1(X2,k6_subset_1(X2,X1))) = k6_subset_1(k5_xboole_0(X0,X2),k6_subset_1(k5_xboole_0(X0,X2),X1))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f34,f37,f37,f37])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 0.21/0.53  fof(f7198,plain,(
% 0.21/0.53    k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2)) = k9_subset_1(sK0,k5_xboole_0(sK0,sK2),sK1)),
% 0.21/0.53    inference(superposition,[],[f3096,f130])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    k6_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)),
% 0.21/0.53    inference(backward_demodulation,[],[f77,f126])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)),
% 0.21/0.53    inference(forward_demodulation,[],[f90,f95])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    sK2 = k6_subset_1(sK0,k3_subset_1(sK0,sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f93,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))),
% 0.21/0.53    inference(resolution,[],[f33,f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = k6_subset_1(sK0,k3_subset_1(sK0,sK2))),
% 0.21/0.53    inference(resolution,[],[f92,f41])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.21/0.53    inference(superposition,[],[f27,f77])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k6_subset_1(sK0,k3_subset_1(sK0,sK2)))),
% 0.21/0.53    inference(superposition,[],[f40,f77])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2)),
% 0.21/0.53    inference(resolution,[],[f41,f24])).
% 0.21/0.53  fof(f3096,plain,(
% 0.21/0.53    ( ! [X21,X20] : (k9_subset_1(sK0,k6_subset_1(X20,X21),sK1) = k9_subset_1(X20,sK1,k6_subset_1(X20,X21))) )),
% 0.21/0.53    inference(superposition,[],[f1945,f1954])).
% 0.21/0.53  fof(f1954,plain,(
% 0.21/0.53    ( ! [X1] : (k5_xboole_0(sK1,k6_subset_1(sK1,X1)) = k9_subset_1(sK0,X1,sK1)) )),
% 0.21/0.53    inference(superposition,[],[f1950,f999])).
% 0.21/0.53  fof(f999,plain,(
% 0.21/0.53    ( ! [X2,X3] : (k5_xboole_0(X2,k6_subset_1(X2,X3)) = k5_xboole_0(X3,k6_subset_1(X3,X2))) )),
% 0.21/0.53    inference(superposition,[],[f884,f593])).
% 0.21/0.53  fof(f884,plain,(
% 0.21/0.53    ( ! [X4,X5] : (k6_subset_1(X5,k6_subset_1(X5,X4)) = k5_xboole_0(X4,k6_subset_1(X4,X5))) )),
% 0.21/0.53    inference(superposition,[],[f593,f39])).
% 0.21/0.53  fof(f1945,plain,(
% 0.21/0.53    ( ! [X8,X7,X9] : (k9_subset_1(X7,X8,k6_subset_1(X7,X9)) = k5_xboole_0(X8,k6_subset_1(X8,k6_subset_1(X7,X9)))) )),
% 0.21/0.53    inference(resolution,[],[f1347,f27])).
% 0.21/0.53  fof(f1075,plain,(
% 0.21/0.53    k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2)) != k6_subset_1(sK1,sK2)),
% 0.21/0.53    inference(backward_demodulation,[],[f132,f1067])).
% 0.21/0.53  fof(f1067,plain,(
% 0.21/0.53    ( ! [X2] : (k7_subset_1(sK0,sK1,X2) = k6_subset_1(sK1,X2)) )),
% 0.21/0.53    inference(resolution,[],[f43,f23])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f35,f28])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2))),
% 0.21/0.53    inference(backward_demodulation,[],[f25,f126])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (13474)------------------------------
% 0.21/0.53  % (13474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13474)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (13474)Memory used [KB]: 9210
% 0.21/0.53  % (13474)Time elapsed: 0.122 s
% 0.21/0.53  % (13474)------------------------------
% 0.21/0.53  % (13474)------------------------------
% 0.21/0.53  % (13471)Success in time 0.175 s
%------------------------------------------------------------------------------
