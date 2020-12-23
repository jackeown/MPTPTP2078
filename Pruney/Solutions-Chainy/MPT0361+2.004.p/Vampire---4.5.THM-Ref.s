%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:58 EST 2020

% Result     : Theorem 7.06s
% Output     : Refutation 7.06s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 193 expanded)
%              Number of leaves         :   20 (  59 expanded)
%              Depth                    :   17
%              Number of atoms          :  227 ( 527 expanded)
%              Number of equality atoms :   50 (  84 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11712,plain,(
    $false ),
    inference(subsumption_resolution,[],[f11711,f1347])).

fof(f1347,plain,(
    ! [X6,X8,X7] : r1_tarski(k4_xboole_0(X6,k2_xboole_0(X7,X8)),k4_xboole_0(X6,X7)) ),
    inference(superposition,[],[f49,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f11711,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f9546,f11706])).

fof(f11706,plain,(
    k3_subset_1(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f11702,f7391])).

fof(f7391,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(resolution,[],[f425,f75])).

fof(f75,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f425,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X2))
      | k4_xboole_0(X2,X3) = k3_subset_1(X2,X3) ) ),
    inference(subsumption_resolution,[],[f423,f46])).

fof(f46,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f423,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X2,X3) = k3_subset_1(X2,X3)
      | ~ r2_hidden(X3,k1_zfmisc_1(X2))
      | v1_xboole_0(k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f58,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f11702,plain,(
    r1_tarski(k2_xboole_0(sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f11692,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f11692,plain,(
    r1_tarski(k2_xboole_0(sK2,sK1),sK0) ),
    inference(superposition,[],[f11257,f102])).

fof(f102,plain,(
    sK0 = k2_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f56,f93])).

fof(f93,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f91,f76])).

fof(f76,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f91,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f89,f46])).

fof(f89,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f52,f44])).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f34,f33])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,X2)),k3_subset_1(sK0,sK1))
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,X2)),k3_subset_1(sK0,sK1))
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f11257,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(X0,sK1),k2_xboole_0(X0,sK0)) ),
    inference(resolution,[],[f11109,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f11109,plain,(
    ! [X82] : r1_tarski(k4_xboole_0(k2_xboole_0(X82,sK1),X82),sK0) ),
    inference(resolution,[],[f11041,f1110])).

fof(f1110,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | r1_tarski(X0,sK0) ) ),
    inference(superposition,[],[f68,f1101])).

fof(f1101,plain,(
    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f443,f1100])).

fof(f1100,plain,(
    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1094,f420])).

fof(f420,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f58,f43])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f1094,plain,(
    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f59,f43])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f443,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f442,f58])).

fof(f442,plain,(
    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f441,f43])).

fof(f441,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f57,f420])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f11041,plain,(
    ! [X26,X27] : r1_tarski(k4_xboole_0(k2_xboole_0(X26,X27),X26),X27) ),
    inference(forward_demodulation,[],[f10992,f109])).

fof(f109,plain,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(superposition,[],[f96,f51])).

fof(f96,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(resolution,[],[f56,f47])).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f10992,plain,(
    ! [X26,X27] : r1_tarski(k4_xboole_0(k2_xboole_0(X26,X27),X26),k2_xboole_0(X27,k1_xboole_0)) ),
    inference(superposition,[],[f1357,f111])).

fof(f111,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f78,f96])).

fof(f78,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f50,f51])).

fof(f50,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f1357,plain,(
    ! [X43,X41,X42] : r1_tarski(k4_xboole_0(X41,X42),k2_xboole_0(X43,k4_xboole_0(X41,k2_xboole_0(X42,X43)))) ),
    inference(superposition,[],[f340,f67])).

fof(f340,plain,(
    ! [X2,X3] : r1_tarski(X2,k2_xboole_0(X3,k4_xboole_0(X2,X3))) ),
    inference(resolution,[],[f70,f73])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f9546,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f424,f9538])).

fof(f9538,plain,(
    k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f5402,f44])).

fof(f5402,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k2_xboole_0(sK1,X0) = k4_subset_1(sK0,sK1,X0) ) ),
    inference(resolution,[],[f72,f43])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f424,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f45,f420])).

fof(f45,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:26:25 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (8177)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (8178)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (8180)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (8197)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.50  % (8184)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (8189)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (8192)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (8176)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (8181)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (8186)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (8196)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (8183)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (8195)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (8198)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (8174)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (8185)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (8175)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (8194)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % (8188)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (8182)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (8193)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.54  % (8190)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.55  % (8179)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.55  % (8199)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.57  % (8187)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.59  % (8191)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 2.69/0.73  % (8183)Refutation not found, incomplete strategy% (8183)------------------------------
% 2.69/0.73  % (8183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.69/0.75  % (8183)Termination reason: Refutation not found, incomplete strategy
% 2.69/0.75  
% 2.69/0.75  % (8183)Memory used [KB]: 6140
% 2.69/0.75  % (8183)Time elapsed: 0.321 s
% 2.69/0.75  % (8183)------------------------------
% 2.69/0.75  % (8183)------------------------------
% 4.05/0.92  % (8188)Time limit reached!
% 4.05/0.92  % (8188)------------------------------
% 4.05/0.92  % (8188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.05/0.92  % (8188)Termination reason: Time limit
% 4.05/0.92  
% 4.05/0.92  % (8188)Memory used [KB]: 7164
% 4.05/0.92  % (8188)Time elapsed: 0.508 s
% 4.05/0.92  % (8188)------------------------------
% 4.05/0.92  % (8188)------------------------------
% 4.05/0.93  % (8187)Time limit reached!
% 4.05/0.93  % (8187)------------------------------
% 4.05/0.93  % (8187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.05/0.93  % (8187)Termination reason: Time limit
% 4.05/0.93  % (8187)Termination phase: Saturation
% 4.05/0.93  
% 4.05/0.93  % (8187)Memory used [KB]: 8827
% 4.05/0.93  % (8187)Time elapsed: 0.500 s
% 4.05/0.93  % (8187)------------------------------
% 4.05/0.93  % (8187)------------------------------
% 4.42/0.94  % (8174)Time limit reached!
% 4.42/0.94  % (8174)------------------------------
% 4.42/0.94  % (8174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.42/0.94  % (8174)Termination reason: Time limit
% 4.42/0.94  % (8174)Termination phase: Saturation
% 4.42/0.94  
% 4.42/0.94  % (8174)Memory used [KB]: 14711
% 4.42/0.94  % (8174)Time elapsed: 0.531 s
% 4.42/0.94  % (8174)------------------------------
% 4.42/0.94  % (8174)------------------------------
% 5.09/1.01  % (8180)Time limit reached!
% 5.09/1.01  % (8180)------------------------------
% 5.09/1.01  % (8180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.09/1.01  % (8180)Termination reason: Time limit
% 5.09/1.01  % (8180)Termination phase: Saturation
% 5.09/1.01  
% 5.09/1.01  % (8180)Memory used [KB]: 13688
% 5.09/1.01  % (8180)Time elapsed: 0.600 s
% 5.09/1.01  % (8180)------------------------------
% 5.09/1.01  % (8180)------------------------------
% 7.06/1.27  % (8177)Refutation found. Thanks to Tanya!
% 7.06/1.27  % SZS status Theorem for theBenchmark
% 7.06/1.27  % SZS output start Proof for theBenchmark
% 7.06/1.27  fof(f11712,plain,(
% 7.06/1.27    $false),
% 7.06/1.27    inference(subsumption_resolution,[],[f11711,f1347])).
% 7.06/1.27  fof(f1347,plain,(
% 7.06/1.27    ( ! [X6,X8,X7] : (r1_tarski(k4_xboole_0(X6,k2_xboole_0(X7,X8)),k4_xboole_0(X6,X7))) )),
% 7.06/1.27    inference(superposition,[],[f49,f67])).
% 7.06/1.27  fof(f67,plain,(
% 7.06/1.27    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 7.06/1.27    inference(cnf_transformation,[],[f7])).
% 7.06/1.27  fof(f7,axiom,(
% 7.06/1.27    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 7.06/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 7.06/1.27  fof(f49,plain,(
% 7.06/1.27    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.06/1.27    inference(cnf_transformation,[],[f6])).
% 7.06/1.27  fof(f6,axiom,(
% 7.06/1.27    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.06/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 7.06/1.27  fof(f11711,plain,(
% 7.06/1.27    ~r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1))),
% 7.06/1.27    inference(backward_demodulation,[],[f9546,f11706])).
% 7.06/1.27  fof(f11706,plain,(
% 7.06/1.27    k3_subset_1(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 7.06/1.27    inference(resolution,[],[f11702,f7391])).
% 7.06/1.27  fof(f7391,plain,(
% 7.06/1.27    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 7.06/1.27    inference(resolution,[],[f425,f75])).
% 7.06/1.27  fof(f75,plain,(
% 7.06/1.27    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 7.06/1.27    inference(equality_resolution,[],[f64])).
% 7.06/1.27  fof(f64,plain,(
% 7.06/1.27    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 7.06/1.27    inference(cnf_transformation,[],[f42])).
% 7.06/1.27  fof(f42,plain,(
% 7.06/1.27    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.06/1.27    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).
% 7.06/1.27  fof(f41,plain,(
% 7.06/1.27    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 7.06/1.27    introduced(choice_axiom,[])).
% 7.06/1.27  fof(f40,plain,(
% 7.06/1.27    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.06/1.27    inference(rectify,[],[f39])).
% 7.06/1.27  fof(f39,plain,(
% 7.06/1.27    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.06/1.27    inference(nnf_transformation,[],[f12])).
% 7.06/1.27  fof(f12,axiom,(
% 7.06/1.27    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 7.06/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 7.06/1.27  fof(f425,plain,(
% 7.06/1.27    ( ! [X2,X3] : (~r2_hidden(X3,k1_zfmisc_1(X2)) | k4_xboole_0(X2,X3) = k3_subset_1(X2,X3)) )),
% 7.06/1.27    inference(subsumption_resolution,[],[f423,f46])).
% 7.06/1.27  fof(f46,plain,(
% 7.06/1.27    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 7.06/1.27    inference(cnf_transformation,[],[f16])).
% 7.06/1.27  fof(f16,axiom,(
% 7.06/1.27    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 7.06/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 7.06/1.27  fof(f423,plain,(
% 7.06/1.27    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_subset_1(X2,X3) | ~r2_hidden(X3,k1_zfmisc_1(X2)) | v1_xboole_0(k1_zfmisc_1(X2))) )),
% 7.06/1.27    inference(resolution,[],[f58,f53])).
% 7.06/1.27  fof(f53,plain,(
% 7.06/1.27    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 7.06/1.27    inference(cnf_transformation,[],[f36])).
% 7.06/1.27  fof(f36,plain,(
% 7.06/1.27    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 7.06/1.27    inference(nnf_transformation,[],[f22])).
% 7.06/1.27  fof(f22,plain,(
% 7.06/1.27    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 7.06/1.27    inference(ennf_transformation,[],[f13])).
% 7.06/1.27  fof(f13,axiom,(
% 7.06/1.27    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 7.06/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 7.06/1.27  fof(f58,plain,(
% 7.06/1.27    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 7.06/1.27    inference(cnf_transformation,[],[f25])).
% 7.06/1.27  fof(f25,plain,(
% 7.06/1.27    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.06/1.27    inference(ennf_transformation,[],[f14])).
% 7.06/1.27  fof(f14,axiom,(
% 7.06/1.27    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.06/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 7.06/1.27  fof(f11702,plain,(
% 7.06/1.27    r1_tarski(k2_xboole_0(sK1,sK2),sK0)),
% 7.06/1.27    inference(forward_demodulation,[],[f11692,f51])).
% 7.06/1.27  fof(f51,plain,(
% 7.06/1.27    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.06/1.27    inference(cnf_transformation,[],[f1])).
% 7.06/1.27  fof(f1,axiom,(
% 7.06/1.27    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.06/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 7.06/1.27  fof(f11692,plain,(
% 7.06/1.27    r1_tarski(k2_xboole_0(sK2,sK1),sK0)),
% 7.06/1.27    inference(superposition,[],[f11257,f102])).
% 7.06/1.27  fof(f102,plain,(
% 7.06/1.27    sK0 = k2_xboole_0(sK2,sK0)),
% 7.06/1.27    inference(resolution,[],[f56,f93])).
% 7.06/1.27  fof(f93,plain,(
% 7.06/1.27    r1_tarski(sK2,sK0)),
% 7.06/1.27    inference(resolution,[],[f91,f76])).
% 7.06/1.27  fof(f76,plain,(
% 7.06/1.27    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 7.06/1.27    inference(equality_resolution,[],[f63])).
% 7.06/1.27  fof(f63,plain,(
% 7.06/1.27    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 7.06/1.27    inference(cnf_transformation,[],[f42])).
% 7.06/1.27  fof(f91,plain,(
% 7.06/1.27    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 7.06/1.27    inference(subsumption_resolution,[],[f89,f46])).
% 7.06/1.27  fof(f89,plain,(
% 7.06/1.27    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 7.06/1.27    inference(resolution,[],[f52,f44])).
% 7.06/1.27  fof(f44,plain,(
% 7.06/1.27    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 7.06/1.27    inference(cnf_transformation,[],[f35])).
% 7.06/1.27  fof(f35,plain,(
% 7.06/1.27    (~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 7.06/1.27    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f34,f33])).
% 7.06/1.27  fof(f33,plain,(
% 7.06/1.27    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,X2)),k3_subset_1(sK0,sK1)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 7.06/1.27    introduced(choice_axiom,[])).
% 7.06/1.27  fof(f34,plain,(
% 7.06/1.27    ? [X2] : (~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,X2)),k3_subset_1(sK0,sK1)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 7.06/1.27    introduced(choice_axiom,[])).
% 7.06/1.27  fof(f21,plain,(
% 7.06/1.27    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.06/1.27    inference(ennf_transformation,[],[f20])).
% 7.06/1.27  fof(f20,negated_conjecture,(
% 7.06/1.27    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 7.06/1.27    inference(negated_conjecture,[],[f19])).
% 7.06/1.27  fof(f19,conjecture,(
% 7.06/1.27    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 7.06/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).
% 7.06/1.27  fof(f52,plain,(
% 7.06/1.27    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 7.06/1.27    inference(cnf_transformation,[],[f36])).
% 7.06/1.27  fof(f56,plain,(
% 7.06/1.27    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 7.06/1.27    inference(cnf_transformation,[],[f23])).
% 7.06/1.27  fof(f23,plain,(
% 7.06/1.27    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.06/1.27    inference(ennf_transformation,[],[f4])).
% 7.06/1.27  fof(f4,axiom,(
% 7.06/1.27    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.06/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 7.06/1.27  fof(f11257,plain,(
% 7.06/1.27    ( ! [X0] : (r1_tarski(k2_xboole_0(X0,sK1),k2_xboole_0(X0,sK0))) )),
% 7.06/1.27    inference(resolution,[],[f11109,f70])).
% 7.06/1.27  fof(f70,plain,(
% 7.06/1.27    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 7.06/1.27    inference(cnf_transformation,[],[f28])).
% 7.06/1.27  fof(f28,plain,(
% 7.06/1.27    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 7.06/1.27    inference(ennf_transformation,[],[f8])).
% 7.06/1.27  fof(f8,axiom,(
% 7.06/1.27    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 7.06/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 7.06/1.27  fof(f11109,plain,(
% 7.06/1.27    ( ! [X82] : (r1_tarski(k4_xboole_0(k2_xboole_0(X82,sK1),X82),sK0)) )),
% 7.06/1.27    inference(resolution,[],[f11041,f1110])).
% 7.06/1.27  fof(f1110,plain,(
% 7.06/1.27    ( ! [X0] : (~r1_tarski(X0,sK1) | r1_tarski(X0,sK0)) )),
% 7.06/1.27    inference(superposition,[],[f68,f1101])).
% 7.06/1.27  fof(f1101,plain,(
% 7.06/1.27    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 7.06/1.27    inference(backward_demodulation,[],[f443,f1100])).
% 7.06/1.27  fof(f1100,plain,(
% 7.06/1.27    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))),
% 7.06/1.27    inference(forward_demodulation,[],[f1094,f420])).
% 7.06/1.27  fof(f420,plain,(
% 7.06/1.27    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 7.06/1.27    inference(resolution,[],[f58,f43])).
% 7.06/1.27  fof(f43,plain,(
% 7.06/1.27    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 7.06/1.27    inference(cnf_transformation,[],[f35])).
% 7.06/1.27  fof(f1094,plain,(
% 7.06/1.27    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 7.06/1.27    inference(resolution,[],[f59,f43])).
% 7.06/1.27  fof(f59,plain,(
% 7.06/1.27    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 7.06/1.27    inference(cnf_transformation,[],[f26])).
% 7.06/1.27  fof(f26,plain,(
% 7.06/1.27    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.06/1.27    inference(ennf_transformation,[],[f17])).
% 7.06/1.27  fof(f17,axiom,(
% 7.06/1.27    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 7.06/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 7.06/1.27  fof(f443,plain,(
% 7.06/1.27    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))),
% 7.06/1.27    inference(resolution,[],[f442,f58])).
% 7.06/1.27  fof(f442,plain,(
% 7.06/1.27    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 7.06/1.27    inference(subsumption_resolution,[],[f441,f43])).
% 7.06/1.27  fof(f441,plain,(
% 7.06/1.27    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 7.06/1.27    inference(superposition,[],[f57,f420])).
% 7.06/1.27  fof(f57,plain,(
% 7.06/1.27    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.06/1.27    inference(cnf_transformation,[],[f24])).
% 7.06/1.27  fof(f24,plain,(
% 7.06/1.27    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.06/1.27    inference(ennf_transformation,[],[f15])).
% 7.06/1.27  fof(f15,axiom,(
% 7.06/1.27    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 7.06/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 7.06/1.27  fof(f68,plain,(
% 7.06/1.27    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 7.06/1.27    inference(cnf_transformation,[],[f27])).
% 7.06/1.27  fof(f27,plain,(
% 7.06/1.27    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 7.06/1.27    inference(ennf_transformation,[],[f3])).
% 7.06/1.27  fof(f3,axiom,(
% 7.06/1.27    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 7.06/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 7.06/1.27  fof(f11041,plain,(
% 7.06/1.27    ( ! [X26,X27] : (r1_tarski(k4_xboole_0(k2_xboole_0(X26,X27),X26),X27)) )),
% 7.06/1.27    inference(forward_demodulation,[],[f10992,f109])).
% 7.06/1.27  fof(f109,plain,(
% 7.06/1.27    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) )),
% 7.06/1.27    inference(superposition,[],[f96,f51])).
% 7.06/1.27  fof(f96,plain,(
% 7.06/1.27    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 7.06/1.27    inference(resolution,[],[f56,f47])).
% 7.06/1.27  fof(f47,plain,(
% 7.06/1.27    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.06/1.27    inference(cnf_transformation,[],[f5])).
% 7.06/1.27  fof(f5,axiom,(
% 7.06/1.27    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.06/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 7.06/1.27  fof(f10992,plain,(
% 7.06/1.27    ( ! [X26,X27] : (r1_tarski(k4_xboole_0(k2_xboole_0(X26,X27),X26),k2_xboole_0(X27,k1_xboole_0))) )),
% 7.06/1.27    inference(superposition,[],[f1357,f111])).
% 7.06/1.27  fof(f111,plain,(
% 7.06/1.27    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 7.06/1.27    inference(superposition,[],[f78,f96])).
% 7.06/1.27  fof(f78,plain,(
% 7.06/1.27    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 7.06/1.27    inference(superposition,[],[f50,f51])).
% 7.06/1.27  fof(f50,plain,(
% 7.06/1.27    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 7.06/1.27    inference(cnf_transformation,[],[f9])).
% 7.06/1.27  fof(f9,axiom,(
% 7.06/1.27    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 7.06/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 7.06/1.27  fof(f1357,plain,(
% 7.06/1.27    ( ! [X43,X41,X42] : (r1_tarski(k4_xboole_0(X41,X42),k2_xboole_0(X43,k4_xboole_0(X41,k2_xboole_0(X42,X43))))) )),
% 7.06/1.27    inference(superposition,[],[f340,f67])).
% 7.06/1.27  fof(f340,plain,(
% 7.06/1.27    ( ! [X2,X3] : (r1_tarski(X2,k2_xboole_0(X3,k4_xboole_0(X2,X3)))) )),
% 7.06/1.27    inference(resolution,[],[f70,f73])).
% 7.06/1.27  fof(f73,plain,(
% 7.06/1.27    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.06/1.27    inference(equality_resolution,[],[f61])).
% 7.06/1.27  fof(f61,plain,(
% 7.06/1.27    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.06/1.27    inference(cnf_transformation,[],[f38])).
% 7.06/1.27  fof(f38,plain,(
% 7.06/1.27    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.06/1.27    inference(flattening,[],[f37])).
% 7.06/1.27  fof(f37,plain,(
% 7.06/1.27    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.06/1.27    inference(nnf_transformation,[],[f2])).
% 7.06/1.27  fof(f2,axiom,(
% 7.06/1.27    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.06/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 7.06/1.27  fof(f9546,plain,(
% 7.06/1.27    ~r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1))),
% 7.06/1.27    inference(backward_demodulation,[],[f424,f9538])).
% 7.06/1.27  fof(f9538,plain,(
% 7.06/1.27    k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK1,sK2)),
% 7.06/1.27    inference(resolution,[],[f5402,f44])).
% 7.06/1.27  fof(f5402,plain,(
% 7.06/1.27    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k2_xboole_0(sK1,X0) = k4_subset_1(sK0,sK1,X0)) )),
% 7.06/1.27    inference(resolution,[],[f72,f43])).
% 7.06/1.27  fof(f72,plain,(
% 7.06/1.27    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 7.06/1.27    inference(cnf_transformation,[],[f32])).
% 7.06/1.27  fof(f32,plain,(
% 7.06/1.27    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.06/1.27    inference(flattening,[],[f31])).
% 7.06/1.27  fof(f31,plain,(
% 7.06/1.27    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.06/1.27    inference(ennf_transformation,[],[f18])).
% 7.06/1.27  fof(f18,axiom,(
% 7.06/1.27    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 7.06/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 7.06/1.27  fof(f424,plain,(
% 7.06/1.27    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1))),
% 7.06/1.27    inference(backward_demodulation,[],[f45,f420])).
% 7.06/1.27  fof(f45,plain,(
% 7.06/1.27    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))),
% 7.06/1.27    inference(cnf_transformation,[],[f35])).
% 7.06/1.27  % SZS output end Proof for theBenchmark
% 7.06/1.27  % (8177)------------------------------
% 7.06/1.27  % (8177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.06/1.27  % (8177)Termination reason: Refutation
% 7.06/1.27  
% 7.06/1.27  % (8177)Memory used [KB]: 12920
% 7.06/1.27  % (8177)Time elapsed: 0.842 s
% 7.06/1.27  % (8177)------------------------------
% 7.06/1.27  % (8177)------------------------------
% 7.06/1.28  % (8173)Success in time 0.914 s
%------------------------------------------------------------------------------
