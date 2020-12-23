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
% DateTime   : Thu Dec  3 12:43:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 894 expanded)
%              Number of leaves         :   14 ( 222 expanded)
%              Depth                    :   28
%              Number of atoms          :  216 (4764 expanded)
%              Number of equality atoms :   71 ( 894 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f544,plain,(
    $false ),
    inference(subsumption_resolution,[],[f543,f91])).

fof(f91,plain,(
    sK0 != k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f90,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f90,plain,(
    sK0 != k2_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f66,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f66,plain,(
    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f65,f29])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f65,plain,
    ( sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f64,f60])).

fof(f60,plain,(
    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f57,f56])).

fof(f56,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f29,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f57,plain,(
    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f29,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f64,plain,
    ( sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f59,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f59,plain,(
    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f52,f56])).

fof(f52,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f30,f31])).

fof(f31,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f30,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f543,plain,(
    sK0 = k2_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f531,f445])).

fof(f445,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f416,f444])).

fof(f444,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = X1 ),
    inference(forward_demodulation,[],[f417,f33])).

fof(f33,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f417,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = k2_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f38,f412])).

fof(f412,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(X3,X3) ),
    inference(subsumption_resolution,[],[f409,f324])).

fof(f324,plain,(
    ! [X11] : ~ r2_hidden(X11,k1_xboole_0) ),
    inference(condensation,[],[f314])).

fof(f314,plain,(
    ! [X12,X11] :
      ( ~ r2_hidden(X11,X12)
      | ~ r2_hidden(X11,k1_xboole_0) ) ),
    inference(resolution,[],[f309,f50])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f309,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_xboole_0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f304,f49])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f304,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | r2_hidden(X0,k4_xboole_0(X1,k1_xboole_0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f286,f32])).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f286,plain,(
    ! [X17,X15,X16] :
      ( ~ r2_hidden(X15,k4_xboole_0(X16,sK0))
      | r2_hidden(X15,k4_xboole_0(X17,k1_xboole_0))
      | ~ r2_hidden(X15,X17) ) ),
    inference(resolution,[],[f279,f49])).

fof(f279,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,k1_xboole_0)
      | ~ r2_hidden(X6,k4_xboole_0(X7,sK0)) ) ),
    inference(resolution,[],[f272,f50])).

fof(f272,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(condensation,[],[f267])).

fof(f267,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0)
      | r2_hidden(X1,sK0) ) ),
    inference(superposition,[],[f183,f32])).

fof(f183,plain,(
    ! [X17,X18,X16] :
      ( ~ r2_hidden(X16,k4_xboole_0(X18,k4_xboole_0(X17,sK1)))
      | ~ r2_hidden(X16,X17)
      | r2_hidden(X16,sK0) ) ),
    inference(resolution,[],[f114,f50])).

fof(f114,plain,(
    ! [X10,X11] :
      ( r2_hidden(X10,k4_xboole_0(X11,sK1))
      | r2_hidden(X10,sK0)
      | ~ r2_hidden(X10,X11) ) ),
    inference(resolution,[],[f106,f49])).

fof(f106,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK1)
      | r2_hidden(X5,sK0) ) ),
    inference(superposition,[],[f51,f76])).

fof(f76,plain,(
    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f70,f58])).

fof(f58,plain,(
    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f55,f56])).

fof(f55,plain,(
    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f29,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f70,plain,(
    k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f60,f40])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f409,plain,(
    ! [X3] :
      ( k1_xboole_0 = k4_xboole_0(X3,X3)
      | r2_hidden(sK2(X3,X3,k1_xboole_0),k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f394])).

fof(f394,plain,(
    ! [X3] :
      ( k1_xboole_0 = k4_xboole_0(X3,X3)
      | k1_xboole_0 = k4_xboole_0(X3,X3)
      | r2_hidden(sK2(X3,X3,k1_xboole_0),k1_xboole_0) ) ),
    inference(resolution,[],[f327,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f327,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK2(X2,X3,k1_xboole_0),X2)
      | k1_xboole_0 = k4_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f324,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f416,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f37,f412])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f531,plain,(
    k2_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f37,f522])).

fof(f522,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f517])).

fof(f517,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f408,f328])).

fof(f328,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK2(X4,X5,k1_xboole_0),X5)
      | k1_xboole_0 = k4_xboole_0(X4,X5) ) ),
    inference(resolution,[],[f324,f47])).

fof(f408,plain,(
    ! [X39] :
      ( r2_hidden(sK2(sK1,X39,k1_xboole_0),sK0)
      | k1_xboole_0 = k4_xboole_0(sK1,X39) ) ),
    inference(resolution,[],[f327,f106])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:54:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.47  % (6189)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.47  % (6170)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (6166)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (6185)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.50  % (6163)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.50  % (6164)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (6167)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (6165)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (6180)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (6182)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.51  % (6166)Refutation not found, incomplete strategy% (6166)------------------------------
% 0.20/0.51  % (6166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (6166)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (6166)Memory used [KB]: 6268
% 0.20/0.51  % (6166)Time elapsed: 0.120 s
% 0.20/0.51  % (6166)------------------------------
% 0.20/0.51  % (6166)------------------------------
% 0.20/0.52  % (6173)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (6188)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.52  % (6168)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (6183)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (6179)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (6186)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.52  % (6172)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (6176)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (6171)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (6174)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (6184)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (6184)Refutation not found, incomplete strategy% (6184)------------------------------
% 0.20/0.53  % (6184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (6184)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (6184)Memory used [KB]: 10746
% 0.20/0.53  % (6184)Time elapsed: 0.104 s
% 0.20/0.53  % (6184)------------------------------
% 0.20/0.53  % (6184)------------------------------
% 0.20/0.53  % (6175)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (6178)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (6187)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (6181)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (6188)Refutation not found, incomplete strategy% (6188)------------------------------
% 0.20/0.54  % (6188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (6191)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (6190)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (6188)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (6188)Memory used [KB]: 10874
% 0.20/0.54  % (6188)Time elapsed: 0.137 s
% 0.20/0.54  % (6188)------------------------------
% 0.20/0.54  % (6188)------------------------------
% 0.20/0.54  % (6179)Refutation not found, incomplete strategy% (6179)------------------------------
% 0.20/0.54  % (6179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (6179)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (6179)Memory used [KB]: 10618
% 0.20/0.54  % (6179)Time elapsed: 0.122 s
% 0.20/0.54  % (6179)------------------------------
% 0.20/0.54  % (6179)------------------------------
% 0.20/0.55  % (6185)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % (6162)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.56  % (6169)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f544,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(subsumption_resolution,[],[f543,f91])).
% 0.20/0.57  fof(f91,plain,(
% 0.20/0.57    sK0 != k2_xboole_0(sK0,sK1)),
% 0.20/0.57    inference(superposition,[],[f90,f35])).
% 0.20/0.57  fof(f35,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f1])).
% 0.20/0.57  fof(f1,axiom,(
% 0.20/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.57  fof(f90,plain,(
% 0.20/0.57    sK0 != k2_xboole_0(sK1,sK0)),
% 0.20/0.57    inference(superposition,[],[f66,f38])).
% 0.20/0.57  fof(f38,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,axiom,(
% 0.20/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.57  fof(f66,plain,(
% 0.20/0.57    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 0.20/0.57    inference(subsumption_resolution,[],[f65,f29])).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.57    inference(cnf_transformation,[],[f23])).
% 0.20/0.57  fof(f23,plain,(
% 0.20/0.57    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f22])).
% 0.20/0.57  fof(f22,plain,(
% 0.20/0.57    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f16,plain,(
% 0.20/0.57    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f15])).
% 0.20/0.57  fof(f15,negated_conjecture,(
% 0.20/0.57    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 0.20/0.57    inference(negated_conjecture,[],[f14])).
% 0.20/0.57  fof(f14,conjecture,(
% 0.20/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 0.20/0.57  fof(f65,plain,(
% 0.20/0.57    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.57    inference(subsumption_resolution,[],[f64,f60])).
% 0.20/0.57  fof(f60,plain,(
% 0.20/0.57    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.20/0.57    inference(forward_demodulation,[],[f57,f56])).
% 0.20/0.57  fof(f56,plain,(
% 0.20/0.57    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.20/0.57    inference(resolution,[],[f29,f40])).
% 0.20/0.57  fof(f40,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f18])).
% 0.20/0.57  fof(f18,plain,(
% 0.20/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f10])).
% 0.20/0.57  fof(f10,axiom,(
% 0.20/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.57  fof(f57,plain,(
% 0.20/0.57    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.20/0.57    inference(resolution,[],[f29,f39])).
% 0.20/0.57  fof(f39,plain,(
% 0.20/0.57    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f17])).
% 0.20/0.57  fof(f17,plain,(
% 0.20/0.57    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f11])).
% 0.20/0.57  fof(f11,axiom,(
% 0.20/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.20/0.57  fof(f64,plain,(
% 0.20/0.57    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.57    inference(superposition,[],[f59,f42])).
% 0.20/0.57  fof(f42,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f21])).
% 0.20/0.57  fof(f21,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.57    inference(flattening,[],[f20])).
% 0.20/0.57  fof(f20,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.20/0.57    inference(ennf_transformation,[],[f13])).
% 0.20/0.57  fof(f13,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.20/0.57  fof(f59,plain,(
% 0.20/0.57    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))),
% 0.20/0.57    inference(backward_demodulation,[],[f52,f56])).
% 0.20/0.57  fof(f52,plain,(
% 0.20/0.57    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 0.20/0.57    inference(forward_demodulation,[],[f30,f31])).
% 0.20/0.57  fof(f31,plain,(
% 0.20/0.57    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f9])).
% 0.20/0.57  fof(f9,axiom,(
% 0.20/0.57    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.57  fof(f30,plain,(
% 0.20/0.57    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 0.20/0.57    inference(cnf_transformation,[],[f23])).
% 0.20/0.57  fof(f543,plain,(
% 0.20/0.57    sK0 = k2_xboole_0(sK0,sK1)),
% 0.20/0.57    inference(forward_demodulation,[],[f531,f445])).
% 0.20/0.57  fof(f445,plain,(
% 0.20/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.57    inference(backward_demodulation,[],[f416,f444])).
% 0.20/0.57  fof(f444,plain,(
% 0.20/0.57    ( ! [X1] : (k2_xboole_0(X1,X1) = X1) )),
% 0.20/0.57    inference(forward_demodulation,[],[f417,f33])).
% 0.20/0.57  fof(f33,plain,(
% 0.20/0.57    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f5])).
% 0.20/0.57  fof(f5,axiom,(
% 0.20/0.57    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.57  fof(f417,plain,(
% 0.20/0.57    ( ! [X1] : (k2_xboole_0(X1,X1) = k2_xboole_0(X1,k1_xboole_0)) )),
% 0.20/0.57    inference(superposition,[],[f38,f412])).
% 0.20/0.57  fof(f412,plain,(
% 0.20/0.57    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(X3,X3)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f409,f324])).
% 0.20/0.57  fof(f324,plain,(
% 0.20/0.57    ( ! [X11] : (~r2_hidden(X11,k1_xboole_0)) )),
% 0.20/0.57    inference(condensation,[],[f314])).
% 0.20/0.57  fof(f314,plain,(
% 0.20/0.57    ( ! [X12,X11] : (~r2_hidden(X11,X12) | ~r2_hidden(X11,k1_xboole_0)) )),
% 0.20/0.57    inference(resolution,[],[f309,f50])).
% 0.20/0.57  fof(f50,plain,(
% 0.20/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.20/0.57    inference(equality_resolution,[],[f44])).
% 0.20/0.57  fof(f44,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.57    inference(cnf_transformation,[],[f28])).
% 0.20/0.57  fof(f28,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).
% 0.20/0.57  fof(f27,plain,(
% 0.20/0.57    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f26,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.57    inference(rectify,[],[f25])).
% 0.20/0.57  fof(f25,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.57    inference(flattening,[],[f24])).
% 0.20/0.57  fof(f24,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.57    inference(nnf_transformation,[],[f3])).
% 0.20/0.57  fof(f3,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.57  fof(f309,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_xboole_0)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f304,f49])).
% 0.20/0.57  fof(f49,plain,(
% 0.20/0.57    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.20/0.57    inference(equality_resolution,[],[f45])).
% 0.20/0.57  fof(f45,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.57    inference(cnf_transformation,[],[f28])).
% 0.20/0.57  fof(f304,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,k4_xboole_0(X1,k1_xboole_0)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.57    inference(superposition,[],[f286,f32])).
% 0.20/0.57  fof(f32,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f7])).
% 0.20/0.57  fof(f7,axiom,(
% 0.20/0.57    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.20/0.57  fof(f286,plain,(
% 0.20/0.57    ( ! [X17,X15,X16] : (~r2_hidden(X15,k4_xboole_0(X16,sK0)) | r2_hidden(X15,k4_xboole_0(X17,k1_xboole_0)) | ~r2_hidden(X15,X17)) )),
% 0.20/0.57    inference(resolution,[],[f279,f49])).
% 0.20/0.57  fof(f279,plain,(
% 0.20/0.57    ( ! [X6,X7] : (~r2_hidden(X6,k1_xboole_0) | ~r2_hidden(X6,k4_xboole_0(X7,sK0))) )),
% 0.20/0.57    inference(resolution,[],[f272,f50])).
% 0.20/0.57  fof(f272,plain,(
% 0.20/0.57    ( ! [X1] : (r2_hidden(X1,sK0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 0.20/0.57    inference(condensation,[],[f267])).
% 0.20/0.57  fof(f267,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0) | r2_hidden(X1,sK0)) )),
% 0.20/0.57    inference(superposition,[],[f183,f32])).
% 0.20/0.57  fof(f183,plain,(
% 0.20/0.57    ( ! [X17,X18,X16] : (~r2_hidden(X16,k4_xboole_0(X18,k4_xboole_0(X17,sK1))) | ~r2_hidden(X16,X17) | r2_hidden(X16,sK0)) )),
% 0.20/0.57    inference(resolution,[],[f114,f50])).
% 0.20/0.57  fof(f114,plain,(
% 0.20/0.57    ( ! [X10,X11] : (r2_hidden(X10,k4_xboole_0(X11,sK1)) | r2_hidden(X10,sK0) | ~r2_hidden(X10,X11)) )),
% 0.20/0.57    inference(resolution,[],[f106,f49])).
% 0.20/0.57  fof(f106,plain,(
% 0.20/0.57    ( ! [X5] : (~r2_hidden(X5,sK1) | r2_hidden(X5,sK0)) )),
% 0.20/0.57    inference(superposition,[],[f51,f76])).
% 0.20/0.57  fof(f76,plain,(
% 0.20/0.57    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.20/0.57    inference(forward_demodulation,[],[f70,f58])).
% 0.20/0.57  fof(f58,plain,(
% 0.20/0.57    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))),
% 0.20/0.57    inference(backward_demodulation,[],[f55,f56])).
% 0.20/0.57  fof(f55,plain,(
% 0.20/0.57    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 0.20/0.57    inference(resolution,[],[f29,f41])).
% 0.20/0.57  fof(f41,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f19,plain,(
% 0.20/0.57    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f12])).
% 0.20/0.57  fof(f12,axiom,(
% 0.20/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.20/0.57  fof(f70,plain,(
% 0.20/0.57    k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.20/0.57    inference(resolution,[],[f60,f40])).
% 0.20/0.57  fof(f51,plain,(
% 0.20/0.57    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.20/0.57    inference(equality_resolution,[],[f43])).
% 0.20/0.57  fof(f43,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.57    inference(cnf_transformation,[],[f28])).
% 0.20/0.57  fof(f409,plain,(
% 0.20/0.57    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(X3,X3) | r2_hidden(sK2(X3,X3,k1_xboole_0),k1_xboole_0)) )),
% 0.20/0.57    inference(duplicate_literal_removal,[],[f394])).
% 0.20/0.57  fof(f394,plain,(
% 0.20/0.57    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(X3,X3) | k1_xboole_0 = k4_xboole_0(X3,X3) | r2_hidden(sK2(X3,X3,k1_xboole_0),k1_xboole_0)) )),
% 0.20/0.57    inference(resolution,[],[f327,f47])).
% 0.20/0.57  fof(f47,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f28])).
% 0.20/0.57  fof(f327,plain,(
% 0.20/0.57    ( ! [X2,X3] : (r2_hidden(sK2(X2,X3,k1_xboole_0),X2) | k1_xboole_0 = k4_xboole_0(X2,X3)) )),
% 0.20/0.57    inference(resolution,[],[f324,f46])).
% 0.20/0.57  fof(f46,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f28])).
% 0.20/0.57  fof(f416,plain,(
% 0.20/0.57    ( ! [X0] : (k2_xboole_0(X0,X0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.57    inference(superposition,[],[f37,f412])).
% 0.20/0.57  fof(f37,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f8])).
% 0.20/0.57  fof(f8,axiom,(
% 0.20/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.57  fof(f531,plain,(
% 0.20/0.57    k2_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k1_xboole_0)),
% 0.20/0.57    inference(superposition,[],[f37,f522])).
% 0.20/0.57  fof(f522,plain,(
% 0.20/0.57    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 0.20/0.57    inference(duplicate_literal_removal,[],[f517])).
% 0.20/0.57  fof(f517,plain,(
% 0.20/0.57    k1_xboole_0 = k4_xboole_0(sK1,sK0) | k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 0.20/0.57    inference(resolution,[],[f408,f328])).
% 0.20/0.57  fof(f328,plain,(
% 0.20/0.57    ( ! [X4,X5] : (~r2_hidden(sK2(X4,X5,k1_xboole_0),X5) | k1_xboole_0 = k4_xboole_0(X4,X5)) )),
% 0.20/0.57    inference(resolution,[],[f324,f47])).
% 0.20/0.57  fof(f408,plain,(
% 0.20/0.57    ( ! [X39] : (r2_hidden(sK2(sK1,X39,k1_xboole_0),sK0) | k1_xboole_0 = k4_xboole_0(sK1,X39)) )),
% 0.20/0.57    inference(resolution,[],[f327,f106])).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (6185)------------------------------
% 0.20/0.57  % (6185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (6185)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (6185)Memory used [KB]: 2174
% 0.20/0.57  % (6185)Time elapsed: 0.167 s
% 0.20/0.57  % (6185)------------------------------
% 0.20/0.57  % (6185)------------------------------
% 0.20/0.57  % (6161)Success in time 0.216 s
%------------------------------------------------------------------------------
