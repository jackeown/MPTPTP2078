%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:18 EST 2020

% Result     : Theorem 2.16s
% Output     : Refutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 347 expanded)
%              Number of leaves         :   17 ( 103 expanded)
%              Depth                    :   17
%              Number of atoms          :  243 (1008 expanded)
%              Number of equality atoms :   42 ( 172 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2845,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f416,f2842,f340])).

fof(f340,plain,(
    ! [X2,X3] :
      ( r1_tarski(X2,k4_xboole_0(X2,X3))
      | ~ r1_tarski(X3,k1_xboole_0) ) ),
    inference(superposition,[],[f58,f120])).

fof(f120,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f118,f72])).

fof(f72,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f40,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f118,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[],[f72,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f2842,plain,(
    r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1256,f1208])).

fof(f1208,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f724,f683])).

fof(f683,plain,(
    ! [X6] :
      ( ~ r1_tarski(X6,k1_xboole_0)
      | k1_xboole_0 = X6 ) ),
    inference(forward_demodulation,[],[f682,f435])).

fof(f435,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f122,f120])).

fof(f122,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f82,f60])).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f42,f44,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f82,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f41,f40,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f682,plain,(
    ! [X6] :
      ( k1_xboole_0 = X6
      | ~ r1_tarski(X6,k4_xboole_0(X6,X6)) ) ),
    inference(forward_demodulation,[],[f251,f435])).

fof(f251,plain,(
    ! [X6] :
      ( k4_xboole_0(X6,X6) = X6
      | ~ r1_tarski(X6,k4_xboole_0(X6,X6)) ) ),
    inference(superposition,[],[f78,f73])).

fof(f73,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f61,f49])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f78,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X3,X2) = k2_xboole_0(X2,X3)
      | ~ r1_tarski(X2,k4_xboole_0(X3,X2)) ) ),
    inference(superposition,[],[f43,f49])).

fof(f724,plain,(
    r1_tarski(k4_xboole_0(sK1,sK0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f86,f712])).

fof(f712,plain,(
    ! [X6,X7] :
      ( r1_tarski(k4_xboole_0(X6,X7),k1_xboole_0)
      | ~ r1_tarski(X6,X7) ) ),
    inference(forward_demodulation,[],[f304,f120])).

fof(f304,plain,(
    ! [X6,X7] :
      ( r1_tarski(k4_xboole_0(X6,X7),k1_xboole_0)
      | ~ r1_tarski(k4_xboole_0(X6,k1_xboole_0),X7) ) ),
    inference(superposition,[],[f104,f82])).

fof(f104,plain,(
    ! [X8,X7,X9] :
      ( r1_tarski(k4_xboole_0(X7,X9),k4_xboole_0(X8,k4_xboole_0(X8,X7)))
      | ~ r1_tarski(k4_xboole_0(X7,X8),X9) ) ),
    inference(superposition,[],[f58,f60])).

fof(f86,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f69,f64])).

fof(f64,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).

fof(f33,plain,(
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

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f69,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f39,f35,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | ~ r1_tarski(sK1,sK2) )
    & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | r1_tarski(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f26,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | r1_tarski(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | ~ r1_tarski(sK1,X2) )
          & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | r1_tarski(sK1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
          | ~ r1_tarski(sK1,X2) )
        & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
          | r1_tarski(sK1,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
        | ~ r1_tarski(sK1,sK2) )
      & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
        | r1_tarski(sK1,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(f39,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f1256,plain,(
    r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),k4_xboole_0(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f242,f231])).

fof(f231,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))
      | r1_tarski(X2,k4_xboole_0(X0,X1)) ) ),
    inference(superposition,[],[f105,f60])).

fof(f105,plain,(
    ! [X12,X10,X11] :
      ( ~ r1_tarski(X12,k4_xboole_0(X11,k4_xboole_0(X11,X10)))
      | r1_tarski(X12,X10) ) ),
    inference(superposition,[],[f59,f60])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f242,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(sK0,sK2))),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(sK0,sK1)))) ),
    inference(unit_resulting_resolution,[],[f154,f58])).

fof(f154,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),k4_xboole_0(X0,k4_xboole_0(sK0,sK2))) ),
    inference(unit_resulting_resolution,[],[f152,f58])).

fof(f152,plain,(
    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f150,f143])).

fof(f143,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f142,f58])).

fof(f142,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f141,f36])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f141,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ r1_tarski(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f139,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f139,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(backward_demodulation,[],[f38,f91])).

fof(f91,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f35,f50])).

fof(f38,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f150,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(backward_demodulation,[],[f140,f92])).

fof(f92,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f36,f50])).

fof(f140,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(backward_demodulation,[],[f37,f91])).

fof(f37,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f416,plain,(
    ! [X0,X1] : ~ r1_tarski(sK1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK2))))) ),
    inference(unit_resulting_resolution,[],[f224,f105])).

fof(f224,plain,(
    ! [X0] : ~ r1_tarski(sK1,k4_xboole_0(X0,k4_xboole_0(X0,sK2))) ),
    inference(unit_resulting_resolution,[],[f143,f105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:19:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (14377)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.49  % (14399)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.49  % (14389)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.49  % (14377)Refutation not found, incomplete strategy% (14377)------------------------------
% 0.22/0.49  % (14377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (14377)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (14377)Memory used [KB]: 1663
% 0.22/0.49  % (14377)Time elapsed: 0.080 s
% 0.22/0.49  % (14377)------------------------------
% 0.22/0.49  % (14377)------------------------------
% 0.22/0.50  % (14385)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.50  % (14380)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (14382)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (14381)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (14396)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.52  % (14376)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (14392)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (14393)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.52  % (14388)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (14400)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.53  % (14383)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (14384)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.53  % (14397)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.54  % (14378)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (14391)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (14401)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (14379)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (14401)Refutation not found, incomplete strategy% (14401)------------------------------
% 0.22/0.54  % (14401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (14393)Refutation not found, incomplete strategy% (14393)------------------------------
% 0.22/0.54  % (14393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (14401)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (14401)Memory used [KB]: 10746
% 0.22/0.54  % (14401)Time elapsed: 0.131 s
% 0.22/0.54  % (14401)------------------------------
% 0.22/0.54  % (14401)------------------------------
% 0.22/0.54  % (14404)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (14390)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (14402)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (14405)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (14398)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (14393)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (14393)Memory used [KB]: 10618
% 0.22/0.55  % (14393)Time elapsed: 0.130 s
% 0.22/0.55  % (14393)------------------------------
% 0.22/0.55  % (14393)------------------------------
% 0.22/0.55  % (14405)Refutation not found, incomplete strategy% (14405)------------------------------
% 0.22/0.55  % (14405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (14407)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.42/0.55  % (14404)Refutation not found, incomplete strategy% (14404)------------------------------
% 1.42/0.55  % (14404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (14404)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (14404)Memory used [KB]: 6140
% 1.42/0.55  % (14404)Time elapsed: 0.142 s
% 1.42/0.55  % (14404)------------------------------
% 1.42/0.55  % (14404)------------------------------
% 1.42/0.55  % (14403)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.42/0.55  % (14394)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.42/0.55  % (14386)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.42/0.56  % (14386)Refutation not found, incomplete strategy% (14386)------------------------------
% 1.42/0.56  % (14386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (14391)Refutation not found, incomplete strategy% (14391)------------------------------
% 1.42/0.56  % (14391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (14391)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (14391)Memory used [KB]: 1791
% 1.42/0.56  % (14391)Time elapsed: 0.152 s
% 1.42/0.56  % (14391)------------------------------
% 1.42/0.56  % (14391)------------------------------
% 1.42/0.56  % (14394)Refutation not found, incomplete strategy% (14394)------------------------------
% 1.42/0.56  % (14394)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (14407)Refutation not found, incomplete strategy% (14407)------------------------------
% 1.42/0.56  % (14407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (14407)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (14407)Memory used [KB]: 1663
% 1.42/0.56  % (14407)Time elapsed: 0.003 s
% 1.42/0.56  % (14407)------------------------------
% 1.42/0.56  % (14407)------------------------------
% 1.42/0.56  % (14395)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.42/0.56  % (14394)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (14394)Memory used [KB]: 1791
% 1.42/0.56  % (14386)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  % (14394)Time elapsed: 0.153 s
% 1.42/0.56  % (14394)------------------------------
% 1.42/0.56  % (14394)------------------------------
% 1.42/0.57  
% 1.42/0.57  % (14386)Memory used [KB]: 10746
% 1.42/0.57  % (14386)Time elapsed: 0.143 s
% 1.42/0.57  % (14386)------------------------------
% 1.42/0.57  % (14386)------------------------------
% 1.42/0.57  % (14395)Refutation not found, incomplete strategy% (14395)------------------------------
% 1.42/0.57  % (14395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (14395)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.57  
% 1.42/0.57  % (14395)Memory used [KB]: 1663
% 1.42/0.57  % (14395)Time elapsed: 0.162 s
% 1.42/0.57  % (14395)------------------------------
% 1.42/0.57  % (14395)------------------------------
% 1.61/0.57  % (14405)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.57  
% 1.61/0.57  % (14405)Memory used [KB]: 10746
% 1.61/0.57  % (14405)Time elapsed: 0.143 s
% 1.61/0.57  % (14405)------------------------------
% 1.61/0.57  % (14405)------------------------------
% 1.61/0.60  % (14478)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.99/0.66  % (14503)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.16/0.66  % (14501)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.16/0.66  % (14380)Refutation found. Thanks to Tanya!
% 2.16/0.66  % SZS status Theorem for theBenchmark
% 2.16/0.66  % SZS output start Proof for theBenchmark
% 2.16/0.66  fof(f2845,plain,(
% 2.16/0.66    $false),
% 2.16/0.66    inference(unit_resulting_resolution,[],[f416,f2842,f340])).
% 2.16/0.66  fof(f340,plain,(
% 2.16/0.66    ( ! [X2,X3] : (r1_tarski(X2,k4_xboole_0(X2,X3)) | ~r1_tarski(X3,k1_xboole_0)) )),
% 2.16/0.66    inference(superposition,[],[f58,f120])).
% 2.16/0.66  fof(f120,plain,(
% 2.16/0.66    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) )),
% 2.16/0.66    inference(forward_demodulation,[],[f118,f72])).
% 2.16/0.66  fof(f72,plain,(
% 2.16/0.66    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.16/0.66    inference(unit_resulting_resolution,[],[f40,f49])).
% 2.16/0.66  fof(f49,plain,(
% 2.16/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.16/0.66    inference(cnf_transformation,[],[f19])).
% 2.16/0.66  fof(f19,plain,(
% 2.16/0.66    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.16/0.66    inference(ennf_transformation,[],[f4])).
% 2.16/0.66  fof(f4,axiom,(
% 2.16/0.66    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.16/0.66  fof(f40,plain,(
% 2.16/0.66    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.16/0.66    inference(cnf_transformation,[],[f5])).
% 2.16/0.66  fof(f5,axiom,(
% 2.16/0.66    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.16/0.66  fof(f118,plain,(
% 2.16/0.66    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X2)) )),
% 2.16/0.66    inference(superposition,[],[f72,f43])).
% 2.16/0.66  fof(f43,plain,(
% 2.16/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.16/0.66    inference(cnf_transformation,[],[f8])).
% 2.16/0.66  fof(f8,axiom,(
% 2.16/0.66    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.16/0.66  fof(f58,plain,(
% 2.16/0.66    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 2.16/0.66    inference(cnf_transformation,[],[f21])).
% 2.16/0.66  fof(f21,plain,(
% 2.16/0.66    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 2.16/0.66    inference(ennf_transformation,[],[f6])).
% 2.16/0.66  fof(f6,axiom,(
% 2.16/0.66    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).
% 2.16/0.66  fof(f2842,plain,(
% 2.16/0.66    r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),k1_xboole_0)),
% 2.16/0.66    inference(forward_demodulation,[],[f1256,f1208])).
% 2.16/0.66  fof(f1208,plain,(
% 2.16/0.66    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 2.16/0.66    inference(unit_resulting_resolution,[],[f724,f683])).
% 2.16/0.66  fof(f683,plain,(
% 2.16/0.66    ( ! [X6] : (~r1_tarski(X6,k1_xboole_0) | k1_xboole_0 = X6) )),
% 2.16/0.66    inference(forward_demodulation,[],[f682,f435])).
% 2.16/0.66  fof(f435,plain,(
% 2.16/0.66    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 2.16/0.66    inference(forward_demodulation,[],[f122,f120])).
% 2.16/0.66  fof(f122,plain,(
% 2.16/0.66    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) )),
% 2.16/0.66    inference(superposition,[],[f82,f60])).
% 2.16/0.66  fof(f60,plain,(
% 2.16/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.16/0.66    inference(definition_unfolding,[],[f42,f44,f44])).
% 2.16/0.66  fof(f44,plain,(
% 2.16/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.16/0.66    inference(cnf_transformation,[],[f9])).
% 2.16/0.66  fof(f9,axiom,(
% 2.16/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.16/0.66  fof(f42,plain,(
% 2.16/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.16/0.66    inference(cnf_transformation,[],[f1])).
% 2.16/0.66  fof(f1,axiom,(
% 2.16/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.16/0.66  fof(f82,plain,(
% 2.16/0.66    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.16/0.66    inference(unit_resulting_resolution,[],[f41,f40,f53])).
% 2.16/0.66  fof(f53,plain,(
% 2.16/0.66    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.16/0.66    inference(cnf_transformation,[],[f30])).
% 2.16/0.66  fof(f30,plain,(
% 2.16/0.66    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.16/0.66    inference(flattening,[],[f29])).
% 2.16/0.66  fof(f29,plain,(
% 2.16/0.66    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.16/0.66    inference(nnf_transformation,[],[f2])).
% 2.16/0.66  fof(f2,axiom,(
% 2.16/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.16/0.66  fof(f41,plain,(
% 2.16/0.66    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.16/0.66    inference(cnf_transformation,[],[f7])).
% 2.16/0.66  fof(f7,axiom,(
% 2.16/0.66    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.16/0.66  fof(f682,plain,(
% 2.16/0.66    ( ! [X6] : (k1_xboole_0 = X6 | ~r1_tarski(X6,k4_xboole_0(X6,X6))) )),
% 2.16/0.66    inference(forward_demodulation,[],[f251,f435])).
% 2.16/0.66  fof(f251,plain,(
% 2.16/0.66    ( ! [X6] : (k4_xboole_0(X6,X6) = X6 | ~r1_tarski(X6,k4_xboole_0(X6,X6))) )),
% 2.16/0.66    inference(superposition,[],[f78,f73])).
% 2.16/0.66  fof(f73,plain,(
% 2.16/0.66    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.16/0.66    inference(unit_resulting_resolution,[],[f61,f49])).
% 2.16/0.66  fof(f61,plain,(
% 2.16/0.66    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.16/0.66    inference(equality_resolution,[],[f52])).
% 2.16/0.66  fof(f52,plain,(
% 2.16/0.66    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.16/0.66    inference(cnf_transformation,[],[f30])).
% 2.16/0.66  fof(f78,plain,(
% 2.16/0.66    ( ! [X2,X3] : (k4_xboole_0(X3,X2) = k2_xboole_0(X2,X3) | ~r1_tarski(X2,k4_xboole_0(X3,X2))) )),
% 2.16/0.66    inference(superposition,[],[f43,f49])).
% 2.16/0.66  fof(f724,plain,(
% 2.16/0.66    r1_tarski(k4_xboole_0(sK1,sK0),k1_xboole_0)),
% 2.16/0.66    inference(unit_resulting_resolution,[],[f86,f712])).
% 2.16/0.66  fof(f712,plain,(
% 2.16/0.66    ( ! [X6,X7] : (r1_tarski(k4_xboole_0(X6,X7),k1_xboole_0) | ~r1_tarski(X6,X7)) )),
% 2.16/0.66    inference(forward_demodulation,[],[f304,f120])).
% 2.16/0.66  fof(f304,plain,(
% 2.16/0.66    ( ! [X6,X7] : (r1_tarski(k4_xboole_0(X6,X7),k1_xboole_0) | ~r1_tarski(k4_xboole_0(X6,k1_xboole_0),X7)) )),
% 2.16/0.66    inference(superposition,[],[f104,f82])).
% 2.16/0.66  fof(f104,plain,(
% 2.16/0.66    ( ! [X8,X7,X9] : (r1_tarski(k4_xboole_0(X7,X9),k4_xboole_0(X8,k4_xboole_0(X8,X7))) | ~r1_tarski(k4_xboole_0(X7,X8),X9)) )),
% 2.16/0.66    inference(superposition,[],[f58,f60])).
% 2.16/0.66  fof(f86,plain,(
% 2.16/0.66    r1_tarski(sK1,sK0)),
% 2.16/0.66    inference(unit_resulting_resolution,[],[f69,f64])).
% 2.16/0.66  fof(f64,plain,(
% 2.16/0.66    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 2.16/0.66    inference(equality_resolution,[],[f54])).
% 2.16/0.66  fof(f54,plain,(
% 2.16/0.66    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.16/0.66    inference(cnf_transformation,[],[f34])).
% 2.16/0.66  fof(f34,plain,(
% 2.16/0.66    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.16/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).
% 2.16/0.66  fof(f33,plain,(
% 2.16/0.66    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 2.16/0.66    introduced(choice_axiom,[])).
% 2.16/0.66  fof(f32,plain,(
% 2.16/0.66    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.16/0.66    inference(rectify,[],[f31])).
% 2.16/0.66  fof(f31,plain,(
% 2.16/0.66    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.16/0.66    inference(nnf_transformation,[],[f10])).
% 2.16/0.66  fof(f10,axiom,(
% 2.16/0.66    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.16/0.66  fof(f69,plain,(
% 2.16/0.66    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 2.16/0.66    inference(unit_resulting_resolution,[],[f39,f35,f45])).
% 2.16/0.66  fof(f45,plain,(
% 2.16/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.16/0.66    inference(cnf_transformation,[],[f28])).
% 2.16/0.66  fof(f28,plain,(
% 2.16/0.66    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.16/0.66    inference(nnf_transformation,[],[f18])).
% 2.16/0.66  fof(f18,plain,(
% 2.16/0.66    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.16/0.66    inference(ennf_transformation,[],[f11])).
% 2.16/0.66  fof(f11,axiom,(
% 2.16/0.66    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 2.16/0.66  fof(f35,plain,(
% 2.16/0.66    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.16/0.66    inference(cnf_transformation,[],[f27])).
% 2.16/0.66  fof(f27,plain,(
% 2.16/0.66    ((~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)) & (r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.16/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f26,f25])).
% 2.16/0.66  fof(f25,plain,(
% 2.16/0.66    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,X2)) & (r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 2.16/0.66    introduced(choice_axiom,[])).
% 2.16/0.66  fof(f26,plain,(
% 2.16/0.66    ? [X2] : ((~r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,X2)) & (r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => ((~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)) & (r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 2.16/0.66    introduced(choice_axiom,[])).
% 2.16/0.66  fof(f24,plain,(
% 2.16/0.66    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.16/0.66    inference(flattening,[],[f23])).
% 2.16/0.66  fof(f23,plain,(
% 2.16/0.66    ? [X0,X1] : (? [X2] : (((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.16/0.66    inference(nnf_transformation,[],[f17])).
% 2.16/0.66  fof(f17,plain,(
% 2.16/0.66    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.16/0.66    inference(ennf_transformation,[],[f15])).
% 2.16/0.66  fof(f15,negated_conjecture,(
% 2.16/0.66    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 2.16/0.66    inference(negated_conjecture,[],[f14])).
% 2.16/0.66  fof(f14,conjecture,(
% 2.16/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).
% 2.16/0.66  fof(f39,plain,(
% 2.16/0.66    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.16/0.66    inference(cnf_transformation,[],[f13])).
% 2.16/0.66  fof(f13,axiom,(
% 2.16/0.66    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 2.16/0.66  fof(f1256,plain,(
% 2.16/0.66    r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),k4_xboole_0(sK1,sK0))),
% 2.16/0.66    inference(unit_resulting_resolution,[],[f242,f231])).
% 2.16/0.66  fof(f231,plain,(
% 2.16/0.66    ( ! [X2,X0,X1] : (~r1_tarski(X2,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) | r1_tarski(X2,k4_xboole_0(X0,X1))) )),
% 2.16/0.66    inference(superposition,[],[f105,f60])).
% 2.16/0.66  fof(f105,plain,(
% 2.16/0.66    ( ! [X12,X10,X11] : (~r1_tarski(X12,k4_xboole_0(X11,k4_xboole_0(X11,X10))) | r1_tarski(X12,X10)) )),
% 2.16/0.66    inference(superposition,[],[f59,f60])).
% 2.16/0.66  fof(f59,plain,(
% 2.16/0.66    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 2.16/0.66    inference(cnf_transformation,[],[f22])).
% 2.16/0.66  fof(f22,plain,(
% 2.16/0.66    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.16/0.66    inference(ennf_transformation,[],[f16])).
% 2.16/0.66  fof(f16,plain,(
% 2.16/0.66    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 2.16/0.66    inference(pure_predicate_removal,[],[f3])).
% 2.16/0.66  fof(f3,axiom,(
% 2.16/0.66    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 2.16/0.66  fof(f242,plain,(
% 2.16/0.66    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(sK0,sK2))),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(sK0,sK1))))) )),
% 2.16/0.66    inference(unit_resulting_resolution,[],[f154,f58])).
% 2.16/0.66  fof(f154,plain,(
% 2.16/0.66    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),k4_xboole_0(X0,k4_xboole_0(sK0,sK2)))) )),
% 2.16/0.66    inference(unit_resulting_resolution,[],[f152,f58])).
% 2.16/0.66  fof(f152,plain,(
% 2.16/0.66    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))),
% 2.16/0.66    inference(subsumption_resolution,[],[f150,f143])).
% 2.16/0.66  fof(f143,plain,(
% 2.16/0.66    ~r1_tarski(sK1,sK2)),
% 2.16/0.66    inference(subsumption_resolution,[],[f142,f58])).
% 2.16/0.66  fof(f142,plain,(
% 2.16/0.66    ~r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~r1_tarski(sK1,sK2)),
% 2.16/0.66    inference(subsumption_resolution,[],[f141,f36])).
% 2.16/0.66  fof(f36,plain,(
% 2.16/0.66    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.16/0.66    inference(cnf_transformation,[],[f27])).
% 2.16/0.66  fof(f141,plain,(
% 2.16/0.66    ~r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~r1_tarski(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.16/0.66    inference(superposition,[],[f139,f50])).
% 2.16/0.66  fof(f50,plain,(
% 2.16/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.16/0.66    inference(cnf_transformation,[],[f20])).
% 2.16/0.66  fof(f20,plain,(
% 2.16/0.66    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.16/0.66    inference(ennf_transformation,[],[f12])).
% 2.16/0.66  fof(f12,axiom,(
% 2.16/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.16/0.66  fof(f139,plain,(
% 2.16/0.66    ~r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~r1_tarski(sK1,sK2)),
% 2.16/0.66    inference(backward_demodulation,[],[f38,f91])).
% 2.16/0.66  fof(f91,plain,(
% 2.16/0.66    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 2.16/0.66    inference(unit_resulting_resolution,[],[f35,f50])).
% 2.16/0.66  fof(f38,plain,(
% 2.16/0.66    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)),
% 2.16/0.66    inference(cnf_transformation,[],[f27])).
% 2.16/0.66  fof(f150,plain,(
% 2.16/0.66    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 2.16/0.66    inference(backward_demodulation,[],[f140,f92])).
% 2.16/0.66  fof(f92,plain,(
% 2.16/0.66    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 2.16/0.66    inference(unit_resulting_resolution,[],[f36,f50])).
% 2.16/0.66  fof(f140,plain,(
% 2.16/0.66    r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 2.16/0.66    inference(backward_demodulation,[],[f37,f91])).
% 2.16/0.66  fof(f37,plain,(
% 2.16/0.66    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 2.16/0.66    inference(cnf_transformation,[],[f27])).
% 2.16/0.66  fof(f416,plain,(
% 2.16/0.66    ( ! [X0,X1] : (~r1_tarski(sK1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK2)))))) )),
% 2.16/0.66    inference(unit_resulting_resolution,[],[f224,f105])).
% 2.16/0.66  fof(f224,plain,(
% 2.16/0.66    ( ! [X0] : (~r1_tarski(sK1,k4_xboole_0(X0,k4_xboole_0(X0,sK2)))) )),
% 2.16/0.66    inference(unit_resulting_resolution,[],[f143,f105])).
% 2.16/0.66  % SZS output end Proof for theBenchmark
% 2.16/0.66  % (14380)------------------------------
% 2.16/0.66  % (14380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.66  % (14380)Termination reason: Refutation
% 2.16/0.66  
% 2.16/0.66  % (14380)Memory used [KB]: 3070
% 2.16/0.66  % (14380)Time elapsed: 0.235 s
% 2.16/0.66  % (14380)------------------------------
% 2.16/0.66  % (14380)------------------------------
% 2.16/0.66  % (14372)Success in time 0.292 s
%------------------------------------------------------------------------------
