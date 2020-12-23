%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0355+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:49 EST 2020

% Result     : Theorem 45.61s
% Output     : Refutation 45.61s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 918 expanded)
%              Number of leaves         :   23 ( 296 expanded)
%              Depth                    :   21
%              Number of atoms          :  236 (2341 expanded)
%              Number of equality atoms :  109 ( 858 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f84072,plain,(
    $false ),
    inference(subsumption_resolution,[],[f84071,f7331])).

fof(f7331,plain,(
    m1_subset_1(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f804,f7320])).

fof(f7320,plain,(
    k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f7304,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f7304,plain,(
    k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f7112,f66])).

fof(f66,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f7112,plain,(
    ! [X0] : k4_subset_1(sK0,k3_xboole_0(X0,sK1),sK2) = k2_xboole_0(sK2,k3_xboole_0(X0,sK1)) ),
    inference(backward_demodulation,[],[f701,f7110])).

fof(f7110,plain,(
    ! [X1] : k4_subset_1(sK0,sK2,k3_xboole_0(X1,sK1)) = k2_xboole_0(sK2,k3_xboole_0(X1,sK1)) ),
    inference(forward_demodulation,[],[f7109,f69])).

fof(f7109,plain,(
    ! [X1] : k4_subset_1(sK0,sK2,k3_xboole_0(X1,sK1)) = k2_xboole_0(k3_xboole_0(X1,sK1),sK2) ),
    inference(subsumption_resolution,[],[f7056,f57])).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( k3_subset_1(sK0,k5_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k9_subset_1(sK0,sK1,sK2),k9_subset_1(sK0,k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f52,f51])).

fof(f51,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k3_subset_1(X0,k5_subset_1(X0,X1,X2)) != k4_subset_1(X0,k9_subset_1(X0,X1,X2),k9_subset_1(X0,k3_subset_1(X0,X1),k3_subset_1(X0,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( k3_subset_1(sK0,k5_subset_1(sK0,sK1,X2)) != k4_subset_1(sK0,k9_subset_1(sK0,sK1,X2),k9_subset_1(sK0,k3_subset_1(sK0,sK1),k3_subset_1(sK0,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X2] :
        ( k3_subset_1(sK0,k5_subset_1(sK0,sK1,X2)) != k4_subset_1(sK0,k9_subset_1(sK0,sK1,X2),k9_subset_1(sK0,k3_subset_1(sK0,sK1),k3_subset_1(sK0,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( k3_subset_1(sK0,k5_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k9_subset_1(sK0,sK1,sK2),k9_subset_1(sK0,k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,k5_subset_1(X0,X1,X2)) != k4_subset_1(X0,k9_subset_1(X0,X1,X2),k9_subset_1(X0,k3_subset_1(X0,X1),k3_subset_1(X0,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => k3_subset_1(X0,k5_subset_1(X0,X1,X2)) = k4_subset_1(X0,k9_subset_1(X0,X1,X2),k9_subset_1(X0,k3_subset_1(X0,X1),k3_subset_1(X0,X2))) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k5_subset_1(X0,X1,X2)) = k4_subset_1(X0,k9_subset_1(X0,X1,X2),k9_subset_1(X0,k3_subset_1(X0,X1),k3_subset_1(X0,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_subset_1)).

fof(f7056,plain,(
    ! [X1] :
      ( k4_subset_1(sK0,sK2,k3_xboole_0(X1,sK1)) = k2_xboole_0(k3_xboole_0(X1,sK1),sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    inference(superposition,[],[f178,f701])).

fof(f178,plain,(
    ! [X23,X22] :
      ( k4_subset_1(sK0,k3_xboole_0(X22,sK1),X23) = k2_xboole_0(k3_xboole_0(X22,sK1),X23)
      | ~ m1_subset_1(X23,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f104,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f104,plain,(
    ! [X1] : m1_subset_1(k3_xboole_0(X1,sK1),k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f89,f90])).

fof(f90,plain,(
    ! [X2] : k9_subset_1(sK0,X2,sK1) = k3_xboole_0(X2,sK1) ),
    inference(resolution,[],[f56,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f56,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f53])).

fof(f89,plain,(
    ! [X1] : m1_subset_1(k9_subset_1(sK0,X1,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f56,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f701,plain,(
    ! [X0] : k4_subset_1(sK0,sK2,k3_xboole_0(X0,sK1)) = k4_subset_1(sK0,k3_xboole_0(X0,sK1),sK2) ),
    inference(resolution,[],[f125,f104])).

fof(f125,plain,(
    ! [X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,sK2,X14) = k4_subset_1(sK0,X14,sK2) ) ),
    inference(resolution,[],[f57,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

fof(f804,plain,(
    m1_subset_1(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f374,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f374,plain,(
    m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f92,f57])).

fof(f92,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(sK0))
      | m1_subset_1(k4_subset_1(sK0,sK1,X4),k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f56,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f84071,plain,(
    ~ m1_subset_1(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f83954,f28231])).

fof(f28231,plain,(
    k2_xboole_0(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) = k3_subset_1(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f26976,f68])).

fof(f68,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f26976,plain,(
    k3_subset_1(sK0,k5_xboole_0(sK1,sK2)) = k2_xboole_0(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK1)) ),
    inference(backward_demodulation,[],[f19986,f26950])).

fof(f26950,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f26949,f153])).

fof(f153,plain,(
    sK1 = k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f134,f87])).

fof(f87,plain,(
    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f56,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f134,plain,(
    k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f85,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f85,plain,(
    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f56,f70])).

fof(f26949,plain,(
    k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) = k3_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f26948,f68])).

fof(f26948,plain,(
    k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) = k3_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f26926,f62])).

fof(f62,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f26926,plain,(
    k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) = k3_xboole_0(sK1,k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f732,f63])).

fof(f63,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f732,plain,(
    ! [X1] : k4_xboole_0(sK0,k2_xboole_0(k3_subset_1(sK0,sK1),X1)) = k3_xboole_0(sK1,k4_xboole_0(sK0,X1)) ),
    inference(superposition,[],[f73,f153])).

fof(f73,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

fof(f19986,plain,(
    k3_subset_1(sK0,k5_xboole_0(sK1,sK2)) = k2_xboole_0(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK2,k3_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f19985,f6914])).

fof(f6914,plain,(
    k3_subset_1(sK0,k5_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f926,f6902])).

fof(f6902,plain,(
    k5_subset_1(sK0,sK1,sK2) = k5_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f6886,f67])).

fof(f67,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f6886,plain,(
    k5_subset_1(sK0,sK1,sK2) = k5_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f6667,f66])).

fof(f6667,plain,(
    ! [X0] : k5_subset_1(sK0,k3_xboole_0(X0,sK1),sK2) = k5_xboole_0(sK2,k3_xboole_0(X0,sK1)) ),
    inference(backward_demodulation,[],[f677,f6665])).

fof(f6665,plain,(
    ! [X1] : k5_subset_1(sK0,sK2,k3_xboole_0(X1,sK1)) = k5_xboole_0(sK2,k3_xboole_0(X1,sK1)) ),
    inference(forward_demodulation,[],[f6664,f67])).

fof(f6664,plain,(
    ! [X1] : k5_subset_1(sK0,sK2,k3_xboole_0(X1,sK1)) = k5_xboole_0(k3_xboole_0(X1,sK1),sK2) ),
    inference(subsumption_resolution,[],[f6613,f57])).

fof(f6613,plain,(
    ! [X1] :
      ( k5_subset_1(sK0,sK2,k3_xboole_0(X1,sK1)) = k5_xboole_0(k3_xboole_0(X1,sK1),sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    inference(superposition,[],[f176,f677])).

fof(f176,plain,(
    ! [X19,X18] :
      ( k5_subset_1(sK0,k3_xboole_0(X18,sK1),X19) = k5_xboole_0(k3_xboole_0(X18,sK1),X19)
      | ~ m1_subset_1(X19,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f104,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k5_subset_1(X0,X1,X2) = k5_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k5_subset_1(X0,X1,X2) = k5_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k5_subset_1(X0,X1,X2) = k5_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k5_subset_1(X0,X1,X2) = k5_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_subset_1)).

fof(f677,plain,(
    ! [X0] : k5_subset_1(sK0,sK2,k3_xboole_0(X0,sK1)) = k5_subset_1(sK0,k3_xboole_0(X0,sK1),sK2) ),
    inference(resolution,[],[f123,f104])).

fof(f123,plain,(
    ! [X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(sK0))
      | k5_subset_1(sK0,sK2,X12) = k5_subset_1(sK0,X12,sK2) ) ),
    inference(resolution,[],[f57,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k5_subset_1(X0,X1,X2) = k5_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k5_subset_1(X0,X1,X2) = k5_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k5_subset_1(X0,X1,X2) = k5_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k5_subset_1(X0,X1,X2) = k5_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_subset_1)).

fof(f926,plain,(
    k3_subset_1(sK0,k5_subset_1(sK0,sK1,sK2)) = k4_xboole_0(sK0,k5_subset_1(sK0,sK1,sK2)) ),
    inference(resolution,[],[f404,f71])).

fof(f404,plain,(
    m1_subset_1(k5_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f94,f57])).

fof(f94,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(sK0))
      | m1_subset_1(k5_subset_1(sK0,sK1,X6),k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f56,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k5_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k5_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k5_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k5_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_subset_1)).

fof(f19985,plain,(
    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) = k2_xboole_0(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK2,k3_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f19980,f68])).

fof(f19980,plain,(
    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) = k2_xboole_0(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)) ),
    inference(superposition,[],[f74,f7332])).

fof(f7332,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k3_subset_1(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f805,f7320])).

fof(f805,plain,(
    k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)) = k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)) ),
    inference(resolution,[],[f374,f71])).

fof(f74,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_xboole_1)).

fof(f83954,plain,
    ( k2_xboole_0(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) != k3_subset_1(sK0,k5_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f7347,f8525])).

fof(f8525,plain,(
    ! [X12,X13] :
      ( k4_subset_1(sK0,k3_xboole_0(X13,sK2),X12) = k2_xboole_0(X12,k3_xboole_0(X13,sK2))
      | ~ m1_subset_1(X12,k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f8523,f127])).

fof(f127,plain,(
    ! [X1] : m1_subset_1(k3_xboole_0(X1,sK2),k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f112,f113])).

fof(f113,plain,(
    ! [X2] : k9_subset_1(sK0,X2,sK2) = k3_xboole_0(X2,sK2) ),
    inference(resolution,[],[f57,f77])).

fof(f112,plain,(
    ! [X1] : m1_subset_1(k9_subset_1(sK0,X1,sK2),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f57,f76])).

fof(f8523,plain,(
    ! [X12,X13] :
      ( k4_subset_1(sK0,k3_xboole_0(X13,sK2),X12) = k2_xboole_0(X12,k3_xboole_0(X13,sK2))
      | ~ m1_subset_1(X12,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(k3_xboole_0(X13,sK2),k1_zfmisc_1(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f8506])).

fof(f8506,plain,(
    ! [X12,X13] :
      ( k4_subset_1(sK0,k3_xboole_0(X13,sK2),X12) = k2_xboole_0(X12,k3_xboole_0(X13,sK2))
      | ~ m1_subset_1(X12,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(X12,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(k3_xboole_0(X13,sK2),k1_zfmisc_1(sK0)) ) ),
    inference(superposition,[],[f226,f84])).

fof(f226,plain,(
    ! [X24,X25] :
      ( k4_subset_1(sK0,X24,k3_xboole_0(X25,sK2)) = k2_xboole_0(X24,k3_xboole_0(X25,sK2))
      | ~ m1_subset_1(X24,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f127,f82])).

fof(f7347,plain,(
    k4_subset_1(sK0,k3_xboole_0(sK1,sK2),k3_subset_1(sK0,k2_xboole_0(sK1,sK2))) != k3_subset_1(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f6930,f7332])).

fof(f6930,plain,(
    k4_subset_1(sK0,k3_xboole_0(sK1,sK2),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) != k3_subset_1(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f4246,f6902])).

fof(f4246,plain,(
    k3_subset_1(sK0,k5_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k3_xboole_0(sK1,sK2),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f131,f4231])).

fof(f4231,plain,(
    k3_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f237,f109])).

fof(f109,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f57,f71])).

fof(f237,plain,(
    ! [X1] : k4_xboole_0(sK0,k2_xboole_0(sK1,X1)) = k3_xboole_0(k3_subset_1(sK0,sK1),k4_xboole_0(sK0,X1)) ),
    inference(superposition,[],[f73,f86])).

fof(f86,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f56,f71])).

fof(f131,plain,(
    k3_subset_1(sK0,k5_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f129,f108])).

fof(f108,plain,(
    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f57,f70])).

fof(f129,plain,
    ( k3_subset_1(sK0,k5_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)))
    | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f107,f77])).

fof(f107,plain,(
    k3_subset_1(sK0,k5_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k3_xboole_0(sK1,sK2),k9_subset_1(sK0,k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2))) ),
    inference(forward_demodulation,[],[f106,f68])).

fof(f106,plain,(
    k3_subset_1(sK0,k5_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k3_xboole_0(sK2,sK1),k9_subset_1(sK0,k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f58,f105])).

fof(f105,plain,(
    ! [X3] : k9_subset_1(sK0,sK1,X3) = k3_xboole_0(X3,sK1) ),
    inference(forward_demodulation,[],[f91,f90])).

fof(f91,plain,(
    ! [X3] : k9_subset_1(sK0,X3,sK1) = k9_subset_1(sK0,sK1,X3) ),
    inference(resolution,[],[f56,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f58,plain,(
    k3_subset_1(sK0,k5_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k9_subset_1(sK0,sK1,sK2),k9_subset_1(sK0,k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f53])).

%------------------------------------------------------------------------------
