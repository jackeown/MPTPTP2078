%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:24 EST 2020

% Result     : Theorem 11.53s
% Output     : Refutation 12.07s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 324 expanded)
%              Number of leaves         :   21 (  93 expanded)
%              Depth                    :   16
%              Number of atoms          :  262 ( 936 expanded)
%              Number of equality atoms :   65 ( 186 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11882,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f833,f141,f11852,f170])).

fof(f170,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,k4_xboole_0(X3,X2)) ) ),
    inference(resolution,[],[f74,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f11852,plain,(
    ! [X56] : r1_tarski(sK2,k4_xboole_0(k2_xboole_0(sK2,X56),sK1)) ),
    inference(superposition,[],[f1521,f1146])).

fof(f1146,plain,(
    sK2 = k4_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f1145,f1045])).

fof(f1045,plain,(
    sK2 = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f932,f1044])).

fof(f1044,plain,(
    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f1018,f52])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f1018,plain,
    ( sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ r1_tarski(k4_xboole_0(sK0,sK2),sK0) ),
    inference(superposition,[],[f359,f176])).

fof(f176,plain,(
    sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f175,f45])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ~ r1_tarski(sK2,k3_subset_1(sK0,sK1))
    & r1_tarski(sK1,k3_subset_1(sK0,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f35,f34])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
            & r1_tarski(X1,k3_subset_1(X0,X2))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(sK0,sK1))
          & r1_tarski(sK1,k3_subset_1(sK0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( ~ r1_tarski(X2,k3_subset_1(sK0,sK1))
        & r1_tarski(sK1,k3_subset_1(sK0,X2))
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ~ r1_tarski(sK2,k3_subset_1(sK0,sK1))
      & r1_tarski(sK1,k3_subset_1(sK0,sK2))
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
          & r1_tarski(X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
          & r1_tarski(X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,k3_subset_1(X0,X2))
             => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

fof(f175,plain,
    ( sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f63,f138])).

fof(f138,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f62,f45])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f359,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(resolution,[],[f164,f80])).

fof(f80,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f41,f42])).

fof(f42,plain,(
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

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f164,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X1))
      | k4_xboole_0(X1,X2) = k3_subset_1(X1,X2) ) ),
    inference(subsumption_resolution,[],[f140,f48])).

fof(f48,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f140,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(X1,X2) = k3_subset_1(X1,X2)
      | ~ r2_hidden(X2,k1_zfmisc_1(X1))
      | v1_xboole_0(k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f62,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f932,plain,(
    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f77,f872])).

fof(f872,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f833,f286])).

fof(f286,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,X7)
      | k1_xboole_0 = k4_xboole_0(X6,X7) ) ),
    inference(backward_demodulation,[],[f224,f275])).

fof(f275,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(resolution,[],[f94,f49])).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f94,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | k2_xboole_0(X3,X2) = X3 ) ),
    inference(superposition,[],[f61,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f224,plain,(
    ! [X6,X7] :
      ( k1_xboole_0 = k4_xboole_0(X6,X7)
      | ~ r1_tarski(X6,k2_xboole_0(X7,k1_xboole_0)) ) ),
    inference(resolution,[],[f105,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f105,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f66,f49])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f77,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f53,f55,f55])).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1145,plain,(
    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f1144,f373])).

fof(f373,plain,(
    ! [X4] : k4_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X4,k1_xboole_0) ),
    inference(forward_demodulation,[],[f369,f220])).

fof(f220,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f105,f52])).

fof(f369,plain,(
    ! [X4] : k4_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X4,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f177,f220])).

fof(f177,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f76,f77])).

fof(f76,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f56,f55])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f1144,plain,(
    k4_xboole_0(sK2,sK1) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1134,f700])).

fof(f700,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(resolution,[],[f286,f78])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1134,plain,(
    k4_xboole_0(sK2,sK1) = k5_xboole_0(sK2,k4_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f177,f1112])).

fof(f1112,plain,(
    sK1 = k4_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f1092,f107])).

fof(f107,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k4_xboole_0(X2,X3))
      | k4_xboole_0(X2,X3) = X2 ) ),
    inference(resolution,[],[f66,f52])).

fof(f1092,plain,(
    r1_tarski(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f399,f162])).

fof(f162,plain,(
    r1_tarski(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f46,f138])).

fof(f46,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f399,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X3,k4_xboole_0(X5,X4))
      | r1_tarski(X3,k4_xboole_0(X3,X4)) ) ),
    inference(resolution,[],[f170,f78])).

fof(f1521,plain,(
    ! [X8,X7,X9] : r1_tarski(k4_xboole_0(X7,X8),k4_xboole_0(k2_xboole_0(k4_xboole_0(X7,X8),X9),X8)) ),
    inference(resolution,[],[f406,f78])).

fof(f406,plain,(
    ! [X35,X33,X36,X34] :
      ( ~ r1_tarski(X33,k4_xboole_0(X36,X35))
      | r1_tarski(X33,k4_xboole_0(k2_xboole_0(X33,X34),X35)) ) ),
    inference(resolution,[],[f170,f51])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f141,plain,(
    ~ r1_tarski(sK2,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f47,f137])).

fof(f137,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f62,f44])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f47,plain,(
    ~ r1_tarski(sK2,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f833,plain,(
    r1_tarski(sK2,sK0) ),
    inference(superposition,[],[f82,f771])).

fof(f771,plain,(
    sK0 = k2_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f280,f45])).

fof(f280,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | k2_xboole_0(X10,X11) = X10 ) ),
    inference(resolution,[],[f94,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(subsumption_resolution,[],[f87,f48])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | v1_xboole_0(k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f57,f81])).

fof(f81,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f82,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f51,f54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:17:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (27506)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.49  % (27514)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.49  % (27525)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.50  % (27517)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.50  % (27530)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.50  % (27504)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (27511)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.51  % (27526)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.52  % (27527)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.52  % (27524)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.52  % (27509)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (27521)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.53  % (27507)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (27508)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (27519)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.53  % (27518)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (27520)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.53  % (27513)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (27512)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.53  % (27505)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (27531)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.53  % (27505)Refutation not found, incomplete strategy% (27505)------------------------------
% 0.22/0.53  % (27505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (27516)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  % (27515)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (27510)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (27533)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (27529)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.53  % (27505)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (27505)Memory used [KB]: 1663
% 0.22/0.53  % (27505)Time elapsed: 0.110 s
% 0.22/0.53  % (27505)------------------------------
% 0.22/0.53  % (27505)------------------------------
% 0.22/0.54  % (27522)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.54  % (27532)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.30/0.54  % (27528)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.30/0.55  % (27523)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 2.26/0.67  % (27507)Refutation not found, incomplete strategy% (27507)------------------------------
% 2.26/0.67  % (27507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.26/0.69  % (27578)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.26/0.69  % (27507)Termination reason: Refutation not found, incomplete strategy
% 2.26/0.69  
% 2.26/0.69  % (27507)Memory used [KB]: 6268
% 2.26/0.69  % (27507)Time elapsed: 0.252 s
% 2.26/0.69  % (27507)------------------------------
% 2.26/0.69  % (27507)------------------------------
% 3.01/0.82  % (27528)Time limit reached!
% 3.01/0.82  % (27528)------------------------------
% 3.01/0.82  % (27528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.47/0.83  % (27528)Termination reason: Time limit
% 3.47/0.83  % (27528)Termination phase: Saturation
% 3.47/0.83  
% 3.47/0.83  % (27528)Memory used [KB]: 12281
% 3.47/0.83  % (27528)Time elapsed: 0.411 s
% 3.47/0.83  % (27528)------------------------------
% 3.47/0.83  % (27528)------------------------------
% 3.47/0.83  % (27506)Time limit reached!
% 3.47/0.83  % (27506)------------------------------
% 3.47/0.83  % (27506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.47/0.83  % (27506)Termination reason: Time limit
% 3.47/0.83  
% 3.47/0.83  % (27506)Memory used [KB]: 6780
% 3.47/0.83  % (27506)Time elapsed: 0.413 s
% 3.47/0.83  % (27506)------------------------------
% 3.47/0.83  % (27506)------------------------------
% 3.47/0.86  % (27666)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.73/0.93  % (27510)Time limit reached!
% 3.73/0.93  % (27510)------------------------------
% 3.73/0.93  % (27510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.19/0.93  % (27510)Termination reason: Time limit
% 4.19/0.93  % (27510)Termination phase: Saturation
% 4.19/0.93  
% 4.19/0.93  % (27510)Memory used [KB]: 15095
% 4.19/0.93  % (27510)Time elapsed: 0.500 s
% 4.19/0.93  % (27510)------------------------------
% 4.19/0.93  % (27510)------------------------------
% 4.19/0.94  % (27518)Time limit reached!
% 4.19/0.94  % (27518)------------------------------
% 4.19/0.94  % (27518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.19/0.94  % (27518)Termination reason: Time limit
% 4.19/0.94  % (27518)Termination phase: Saturation
% 4.19/0.94  
% 4.19/0.94  % (27518)Memory used [KB]: 4989
% 4.19/0.94  % (27518)Time elapsed: 0.520 s
% 4.19/0.94  % (27518)------------------------------
% 4.19/0.94  % (27518)------------------------------
% 4.19/0.96  % (27702)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 4.19/0.96  % (27702)Refutation not found, incomplete strategy% (27702)------------------------------
% 4.19/0.96  % (27702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.19/0.96  % (27702)Termination reason: Refutation not found, incomplete strategy
% 4.19/0.96  
% 4.19/0.96  % (27702)Memory used [KB]: 6140
% 4.19/0.96  % (27702)Time elapsed: 0.098 s
% 4.19/0.96  % (27702)------------------------------
% 4.19/0.96  % (27702)------------------------------
% 4.50/0.97  % (27704)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.50/0.97  % (27533)Time limit reached!
% 4.50/0.97  % (27533)------------------------------
% 4.50/0.97  % (27533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.50/0.97  % (27533)Termination reason: Time limit
% 4.50/0.97  
% 4.50/0.97  % (27533)Memory used [KB]: 1918
% 4.50/0.97  % (27533)Time elapsed: 0.546 s
% 4.50/0.97  % (27533)------------------------------
% 4.50/0.97  % (27533)------------------------------
% 4.50/1.02  % (27511)Time limit reached!
% 4.50/1.02  % (27511)------------------------------
% 4.50/1.02  % (27511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.50/1.02  % (27511)Termination reason: Time limit
% 4.50/1.02  
% 4.50/1.02  % (27511)Memory used [KB]: 6780
% 4.50/1.02  % (27511)Time elapsed: 0.602 s
% 4.50/1.02  % (27511)------------------------------
% 4.50/1.02  % (27511)------------------------------
% 4.50/1.03  % (27728)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 4.92/1.04  % (27727)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 5.51/1.08  % (27739)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 6.02/1.16  % (27769)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 6.28/1.18  % (27746)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 7.80/1.42  % (27531)Time limit reached!
% 7.80/1.42  % (27531)------------------------------
% 7.80/1.42  % (27531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.80/1.42  % (27531)Termination reason: Time limit
% 7.80/1.42  
% 7.80/1.42  % (27531)Memory used [KB]: 8699
% 7.80/1.42  % (27531)Time elapsed: 1.006 s
% 7.80/1.42  % (27531)------------------------------
% 7.80/1.42  % (27531)------------------------------
% 7.80/1.43  % (27516)Time limit reached!
% 7.80/1.43  % (27516)------------------------------
% 7.80/1.43  % (27516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.80/1.43  % (27516)Termination reason: Time limit
% 7.80/1.43  
% 7.80/1.43  % (27516)Memory used [KB]: 11897
% 7.80/1.43  % (27516)Time elapsed: 1.018 s
% 7.80/1.43  % (27516)------------------------------
% 7.80/1.43  % (27516)------------------------------
% 9.11/1.54  % (27771)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 9.34/1.57  % (27772)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 9.34/1.62  % (27739)Time limit reached!
% 9.34/1.62  % (27739)------------------------------
% 9.34/1.62  % (27739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.99/1.64  % (27739)Termination reason: Time limit
% 9.99/1.64  
% 9.99/1.64  % (27739)Memory used [KB]: 15223
% 9.99/1.64  % (27739)Time elapsed: 0.610 s
% 9.99/1.64  % (27739)------------------------------
% 9.99/1.64  % (27739)------------------------------
% 9.99/1.65  % (27504)Time limit reached!
% 9.99/1.65  % (27504)------------------------------
% 9.99/1.65  % (27504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.99/1.65  % (27504)Termination reason: Time limit
% 9.99/1.65  
% 9.99/1.65  % (27504)Memory used [KB]: 10490
% 9.99/1.65  % (27504)Time elapsed: 1.203 s
% 9.99/1.65  % (27504)------------------------------
% 9.99/1.65  % (27504)------------------------------
% 10.33/1.74  % (27520)Time limit reached!
% 10.33/1.74  % (27520)------------------------------
% 10.33/1.74  % (27520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.33/1.74  % (27520)Termination reason: Time limit
% 10.33/1.74  % (27520)Termination phase: Saturation
% 10.33/1.74  
% 10.33/1.74  % (27520)Memory used [KB]: 12792
% 10.33/1.74  % (27520)Time elapsed: 1.300 s
% 10.33/1.74  % (27520)------------------------------
% 10.33/1.74  % (27520)------------------------------
% 10.33/1.74  % (27509)Time limit reached!
% 10.33/1.74  % (27509)------------------------------
% 10.33/1.74  % (27509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.84/1.75  % (27509)Termination reason: Time limit
% 10.84/1.75  
% 10.84/1.75  % (27509)Memory used [KB]: 10106
% 10.84/1.75  % (27509)Time elapsed: 1.323 s
% 10.84/1.75  % (27509)------------------------------
% 10.84/1.75  % (27509)------------------------------
% 10.84/1.76  % (27773)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 11.01/1.77  % (27774)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 11.53/1.87  % (27775)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 11.53/1.89  % (27776)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 11.53/1.92  % (27526)Refutation found. Thanks to Tanya!
% 11.53/1.92  % SZS status Theorem for theBenchmark
% 12.07/1.95  % SZS output start Proof for theBenchmark
% 12.07/1.95  fof(f11882,plain,(
% 12.07/1.95    $false),
% 12.07/1.95    inference(unit_resulting_resolution,[],[f833,f141,f11852,f170])).
% 12.07/1.95  fof(f170,plain,(
% 12.07/1.95    ( ! [X2,X0,X3,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_tarski(X0,k4_xboole_0(X3,X2))) )),
% 12.07/1.95    inference(resolution,[],[f74,f73])).
% 12.07/1.95  fof(f73,plain,(
% 12.07/1.95    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 12.07/1.95    inference(cnf_transformation,[],[f29])).
% 12.07/1.95  fof(f29,plain,(
% 12.07/1.95    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 12.07/1.95    inference(ennf_transformation,[],[f5])).
% 12.07/1.95  fof(f5,axiom,(
% 12.07/1.95    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 12.07/1.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 12.07/1.95  fof(f74,plain,(
% 12.07/1.95    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 12.07/1.95    inference(cnf_transformation,[],[f31])).
% 12.07/1.95  fof(f31,plain,(
% 12.07/1.95    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 12.07/1.95    inference(flattening,[],[f30])).
% 12.07/1.95  fof(f30,plain,(
% 12.07/1.95    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 12.07/1.95    inference(ennf_transformation,[],[f13])).
% 12.07/1.95  fof(f13,axiom,(
% 12.07/1.95    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 12.07/1.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).
% 12.07/1.95  fof(f11852,plain,(
% 12.07/1.95    ( ! [X56] : (r1_tarski(sK2,k4_xboole_0(k2_xboole_0(sK2,X56),sK1))) )),
% 12.07/1.95    inference(superposition,[],[f1521,f1146])).
% 12.07/1.95  fof(f1146,plain,(
% 12.07/1.95    sK2 = k4_xboole_0(sK2,sK1)),
% 12.07/1.95    inference(forward_demodulation,[],[f1145,f1045])).
% 12.07/1.95  fof(f1045,plain,(
% 12.07/1.95    sK2 = k4_xboole_0(sK2,k1_xboole_0)),
% 12.07/1.95    inference(backward_demodulation,[],[f932,f1044])).
% 12.07/1.95  fof(f1044,plain,(
% 12.07/1.95    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 12.07/1.95    inference(subsumption_resolution,[],[f1018,f52])).
% 12.07/1.95  fof(f52,plain,(
% 12.07/1.95    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 12.07/1.95    inference(cnf_transformation,[],[f9])).
% 12.07/1.95  fof(f9,axiom,(
% 12.07/1.95    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 12.07/1.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 12.07/1.95  fof(f1018,plain,(
% 12.07/1.95    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~r1_tarski(k4_xboole_0(sK0,sK2),sK0)),
% 12.07/1.95    inference(superposition,[],[f359,f176])).
% 12.07/1.95  fof(f176,plain,(
% 12.07/1.95    sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))),
% 12.07/1.95    inference(subsumption_resolution,[],[f175,f45])).
% 12.07/1.95  fof(f45,plain,(
% 12.07/1.95    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 12.07/1.95    inference(cnf_transformation,[],[f36])).
% 12.07/1.95  fof(f36,plain,(
% 12.07/1.95    (~r1_tarski(sK2,k3_subset_1(sK0,sK1)) & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 12.07/1.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f35,f34])).
% 12.07/1.95  fof(f34,plain,(
% 12.07/1.95    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(X2,k3_subset_1(sK0,sK1)) & r1_tarski(sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 12.07/1.95    introduced(choice_axiom,[])).
% 12.07/1.95  fof(f35,plain,(
% 12.07/1.95    ? [X2] : (~r1_tarski(X2,k3_subset_1(sK0,sK1)) & r1_tarski(sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (~r1_tarski(sK2,k3_subset_1(sK0,sK1)) & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 12.07/1.95    introduced(choice_axiom,[])).
% 12.07/1.95  fof(f23,plain,(
% 12.07/1.95    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 12.07/1.95    inference(flattening,[],[f22])).
% 12.07/1.95  fof(f22,plain,(
% 12.07/1.95    ? [X0,X1] : (? [X2] : ((~r1_tarski(X2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 12.07/1.95    inference(ennf_transformation,[],[f21])).
% 12.07/1.95  fof(f21,negated_conjecture,(
% 12.07/1.95    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 12.07/1.95    inference(negated_conjecture,[],[f20])).
% 12.07/1.95  fof(f20,conjecture,(
% 12.07/1.95    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 12.07/1.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).
% 12.07/1.95  fof(f175,plain,(
% 12.07/1.95    sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 12.07/1.95    inference(superposition,[],[f63,f138])).
% 12.07/1.95  fof(f138,plain,(
% 12.07/1.95    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 12.07/1.95    inference(resolution,[],[f62,f45])).
% 12.07/1.95  fof(f62,plain,(
% 12.07/1.95    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 12.07/1.95    inference(cnf_transformation,[],[f26])).
% 12.07/1.95  fof(f26,plain,(
% 12.07/1.95    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 12.07/1.95    inference(ennf_transformation,[],[f16])).
% 12.07/1.95  fof(f16,axiom,(
% 12.07/1.95    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 12.07/1.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 12.07/1.95  fof(f63,plain,(
% 12.07/1.95    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 12.07/1.95    inference(cnf_transformation,[],[f27])).
% 12.07/1.95  fof(f27,plain,(
% 12.07/1.95    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 12.07/1.95    inference(ennf_transformation,[],[f18])).
% 12.07/1.95  fof(f18,axiom,(
% 12.07/1.95    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 12.07/1.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 12.07/1.95  fof(f359,plain,(
% 12.07/1.95    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~r1_tarski(X1,X0)) )),
% 12.07/1.95    inference(resolution,[],[f164,f80])).
% 12.07/1.95  fof(f80,plain,(
% 12.07/1.95    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 12.07/1.95    inference(equality_resolution,[],[f68])).
% 12.07/1.95  fof(f68,plain,(
% 12.07/1.95    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 12.07/1.95    inference(cnf_transformation,[],[f43])).
% 12.07/1.95  fof(f43,plain,(
% 12.07/1.95    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 12.07/1.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f41,f42])).
% 12.07/1.95  fof(f42,plain,(
% 12.07/1.95    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 12.07/1.95    introduced(choice_axiom,[])).
% 12.07/1.95  fof(f41,plain,(
% 12.07/1.95    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 12.07/1.95    inference(rectify,[],[f40])).
% 12.07/1.95  fof(f40,plain,(
% 12.07/1.95    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 12.07/1.95    inference(nnf_transformation,[],[f14])).
% 12.07/1.95  fof(f14,axiom,(
% 12.07/1.95    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 12.07/1.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 12.07/1.95  fof(f164,plain,(
% 12.07/1.95    ( ! [X2,X1] : (~r2_hidden(X2,k1_zfmisc_1(X1)) | k4_xboole_0(X1,X2) = k3_subset_1(X1,X2)) )),
% 12.07/1.95    inference(subsumption_resolution,[],[f140,f48])).
% 12.07/1.95  fof(f48,plain,(
% 12.07/1.95    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 12.07/1.95    inference(cnf_transformation,[],[f17])).
% 12.07/1.95  fof(f17,axiom,(
% 12.07/1.95    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 12.07/1.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 12.07/1.95  fof(f140,plain,(
% 12.07/1.95    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k3_subset_1(X1,X2) | ~r2_hidden(X2,k1_zfmisc_1(X1)) | v1_xboole_0(k1_zfmisc_1(X1))) )),
% 12.07/1.95    inference(resolution,[],[f62,f58])).
% 12.07/1.95  fof(f58,plain,(
% 12.07/1.95    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 12.07/1.95    inference(cnf_transformation,[],[f37])).
% 12.07/1.95  fof(f37,plain,(
% 12.07/1.95    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 12.07/1.95    inference(nnf_transformation,[],[f24])).
% 12.07/1.95  fof(f24,plain,(
% 12.07/1.95    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 12.07/1.95    inference(ennf_transformation,[],[f15])).
% 12.07/1.95  fof(f15,axiom,(
% 12.07/1.95    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 12.07/1.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 12.07/1.95  fof(f932,plain,(
% 12.07/1.95    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 12.07/1.95    inference(superposition,[],[f77,f872])).
% 12.07/1.95  fof(f872,plain,(
% 12.07/1.95    k1_xboole_0 = k4_xboole_0(sK2,sK0)),
% 12.07/1.95    inference(resolution,[],[f833,f286])).
% 12.07/1.95  fof(f286,plain,(
% 12.07/1.95    ( ! [X6,X7] : (~r1_tarski(X6,X7) | k1_xboole_0 = k4_xboole_0(X6,X7)) )),
% 12.07/1.95    inference(backward_demodulation,[],[f224,f275])).
% 12.07/1.95  fof(f275,plain,(
% 12.07/1.95    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 12.07/1.95    inference(resolution,[],[f94,f49])).
% 12.07/1.95  fof(f49,plain,(
% 12.07/1.95    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 12.07/1.95    inference(cnf_transformation,[],[f8])).
% 12.07/1.95  fof(f8,axiom,(
% 12.07/1.95    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 12.07/1.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 12.07/1.95  fof(f94,plain,(
% 12.07/1.95    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k2_xboole_0(X3,X2) = X3) )),
% 12.07/1.95    inference(superposition,[],[f61,f54])).
% 12.07/1.95  fof(f54,plain,(
% 12.07/1.95    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 12.07/1.95    inference(cnf_transformation,[],[f1])).
% 12.07/1.95  fof(f1,axiom,(
% 12.07/1.95    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 12.07/1.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 12.07/1.95  fof(f61,plain,(
% 12.07/1.95    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 12.07/1.95    inference(cnf_transformation,[],[f25])).
% 12.07/1.95  fof(f25,plain,(
% 12.07/1.95    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 12.07/1.95    inference(ennf_transformation,[],[f6])).
% 12.07/1.95  fof(f6,axiom,(
% 12.07/1.95    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 12.07/1.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 12.07/1.95  fof(f224,plain,(
% 12.07/1.95    ( ! [X6,X7] : (k1_xboole_0 = k4_xboole_0(X6,X7) | ~r1_tarski(X6,k2_xboole_0(X7,k1_xboole_0))) )),
% 12.07/1.95    inference(resolution,[],[f105,f71])).
% 12.07/1.95  fof(f71,plain,(
% 12.07/1.95    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 12.07/1.95    inference(cnf_transformation,[],[f28])).
% 12.07/1.95  fof(f28,plain,(
% 12.07/1.95    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 12.07/1.95    inference(ennf_transformation,[],[f10])).
% 12.07/1.95  fof(f10,axiom,(
% 12.07/1.95    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 12.07/1.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 12.07/1.95  fof(f105,plain,(
% 12.07/1.95    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 12.07/1.95    inference(resolution,[],[f66,f49])).
% 12.07/1.95  fof(f66,plain,(
% 12.07/1.95    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 12.07/1.95    inference(cnf_transformation,[],[f39])).
% 12.07/1.95  fof(f39,plain,(
% 12.07/1.95    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 12.07/1.95    inference(flattening,[],[f38])).
% 12.07/1.95  fof(f38,plain,(
% 12.07/1.95    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 12.07/1.95    inference(nnf_transformation,[],[f3])).
% 12.07/1.95  fof(f3,axiom,(
% 12.07/1.95    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 12.07/1.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 12.07/1.95  fof(f77,plain,(
% 12.07/1.95    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 12.07/1.95    inference(definition_unfolding,[],[f53,f55,f55])).
% 12.07/1.95  fof(f55,plain,(
% 12.07/1.95    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 12.07/1.95    inference(cnf_transformation,[],[f11])).
% 12.07/1.95  fof(f11,axiom,(
% 12.07/1.95    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 12.07/1.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 12.07/1.95  fof(f53,plain,(
% 12.07/1.95    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 12.07/1.95    inference(cnf_transformation,[],[f2])).
% 12.07/1.95  fof(f2,axiom,(
% 12.07/1.95    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 12.07/1.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 12.07/1.95  fof(f1145,plain,(
% 12.07/1.95    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK1)),
% 12.07/1.95    inference(forward_demodulation,[],[f1144,f373])).
% 12.07/1.95  fof(f373,plain,(
% 12.07/1.95    ( ! [X4] : (k4_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X4,k1_xboole_0)) )),
% 12.07/1.95    inference(forward_demodulation,[],[f369,f220])).
% 12.07/1.95  fof(f220,plain,(
% 12.07/1.95    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 12.07/1.95    inference(resolution,[],[f105,f52])).
% 12.07/1.95  fof(f369,plain,(
% 12.07/1.95    ( ! [X4] : (k4_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X4,k4_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 12.07/1.95    inference(superposition,[],[f177,f220])).
% 12.07/1.95  fof(f177,plain,(
% 12.07/1.95    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 12.07/1.95    inference(superposition,[],[f76,f77])).
% 12.07/1.95  fof(f76,plain,(
% 12.07/1.95    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 12.07/1.95    inference(definition_unfolding,[],[f56,f55])).
% 12.07/1.95  fof(f56,plain,(
% 12.07/1.95    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 12.07/1.95    inference(cnf_transformation,[],[f4])).
% 12.07/1.95  fof(f4,axiom,(
% 12.07/1.95    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 12.07/1.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 12.07/1.95  fof(f1144,plain,(
% 12.07/1.95    k4_xboole_0(sK2,sK1) = k5_xboole_0(sK2,k1_xboole_0)),
% 12.07/1.95    inference(forward_demodulation,[],[f1134,f700])).
% 12.07/1.95  fof(f700,plain,(
% 12.07/1.95    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 12.07/1.95    inference(resolution,[],[f286,f78])).
% 12.07/1.95  fof(f78,plain,(
% 12.07/1.95    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 12.07/1.95    inference(equality_resolution,[],[f65])).
% 12.07/1.95  fof(f65,plain,(
% 12.07/1.95    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 12.07/1.95    inference(cnf_transformation,[],[f39])).
% 12.07/1.95  fof(f1134,plain,(
% 12.07/1.95    k4_xboole_0(sK2,sK1) = k5_xboole_0(sK2,k4_xboole_0(sK1,sK1))),
% 12.07/1.95    inference(superposition,[],[f177,f1112])).
% 12.07/1.95  fof(f1112,plain,(
% 12.07/1.95    sK1 = k4_xboole_0(sK1,sK2)),
% 12.07/1.95    inference(resolution,[],[f1092,f107])).
% 12.07/1.95  fof(f107,plain,(
% 12.07/1.95    ( ! [X2,X3] : (~r1_tarski(X2,k4_xboole_0(X2,X3)) | k4_xboole_0(X2,X3) = X2) )),
% 12.07/1.95    inference(resolution,[],[f66,f52])).
% 12.07/1.95  fof(f1092,plain,(
% 12.07/1.95    r1_tarski(sK1,k4_xboole_0(sK1,sK2))),
% 12.07/1.95    inference(resolution,[],[f399,f162])).
% 12.07/1.95  fof(f162,plain,(
% 12.07/1.95    r1_tarski(sK1,k4_xboole_0(sK0,sK2))),
% 12.07/1.95    inference(backward_demodulation,[],[f46,f138])).
% 12.07/1.95  fof(f46,plain,(
% 12.07/1.95    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 12.07/1.95    inference(cnf_transformation,[],[f36])).
% 12.07/1.95  fof(f399,plain,(
% 12.07/1.95    ( ! [X4,X5,X3] : (~r1_tarski(X3,k4_xboole_0(X5,X4)) | r1_tarski(X3,k4_xboole_0(X3,X4))) )),
% 12.07/1.95    inference(resolution,[],[f170,f78])).
% 12.07/1.95  fof(f1521,plain,(
% 12.07/1.95    ( ! [X8,X7,X9] : (r1_tarski(k4_xboole_0(X7,X8),k4_xboole_0(k2_xboole_0(k4_xboole_0(X7,X8),X9),X8))) )),
% 12.07/1.95    inference(resolution,[],[f406,f78])).
% 12.07/1.95  fof(f406,plain,(
% 12.07/1.95    ( ! [X35,X33,X36,X34] : (~r1_tarski(X33,k4_xboole_0(X36,X35)) | r1_tarski(X33,k4_xboole_0(k2_xboole_0(X33,X34),X35))) )),
% 12.07/1.95    inference(resolution,[],[f170,f51])).
% 12.07/1.95  fof(f51,plain,(
% 12.07/1.95    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 12.07/1.95    inference(cnf_transformation,[],[f12])).
% 12.07/1.95  fof(f12,axiom,(
% 12.07/1.95    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 12.07/1.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 12.07/1.95  fof(f141,plain,(
% 12.07/1.95    ~r1_tarski(sK2,k4_xboole_0(sK0,sK1))),
% 12.07/1.95    inference(backward_demodulation,[],[f47,f137])).
% 12.07/1.95  fof(f137,plain,(
% 12.07/1.95    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 12.07/1.95    inference(resolution,[],[f62,f44])).
% 12.07/1.95  fof(f44,plain,(
% 12.07/1.95    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 12.07/1.95    inference(cnf_transformation,[],[f36])).
% 12.07/1.95  fof(f47,plain,(
% 12.07/1.95    ~r1_tarski(sK2,k3_subset_1(sK0,sK1))),
% 12.07/1.95    inference(cnf_transformation,[],[f36])).
% 12.07/1.95  fof(f833,plain,(
% 12.07/1.95    r1_tarski(sK2,sK0)),
% 12.07/1.95    inference(superposition,[],[f82,f771])).
% 12.07/1.95  fof(f771,plain,(
% 12.07/1.95    sK0 = k2_xboole_0(sK0,sK2)),
% 12.07/1.95    inference(resolution,[],[f280,f45])).
% 12.07/1.95  fof(f280,plain,(
% 12.07/1.95    ( ! [X10,X11] : (~m1_subset_1(X11,k1_zfmisc_1(X10)) | k2_xboole_0(X10,X11) = X10) )),
% 12.07/1.95    inference(resolution,[],[f94,f88])).
% 12.07/1.95  fof(f88,plain,(
% 12.07/1.95    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 12.07/1.95    inference(subsumption_resolution,[],[f87,f48])).
% 12.07/1.95  fof(f87,plain,(
% 12.07/1.95    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | v1_xboole_0(k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 12.07/1.95    inference(resolution,[],[f57,f81])).
% 12.07/1.95  fof(f81,plain,(
% 12.07/1.95    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 12.07/1.95    inference(equality_resolution,[],[f67])).
% 12.07/1.95  fof(f67,plain,(
% 12.07/1.95    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 12.07/1.95    inference(cnf_transformation,[],[f43])).
% 12.07/1.95  fof(f57,plain,(
% 12.07/1.95    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 12.07/1.95    inference(cnf_transformation,[],[f37])).
% 12.07/1.95  fof(f82,plain,(
% 12.07/1.95    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 12.07/1.95    inference(superposition,[],[f51,f54])).
% 12.07/1.95  % SZS output end Proof for theBenchmark
% 12.07/1.95  % (27526)------------------------------
% 12.07/1.95  % (27526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.07/1.95  % (27526)Termination reason: Refutation
% 12.07/1.95  
% 12.07/1.95  % (27526)Memory used [KB]: 14200
% 12.07/1.95  % (27526)Time elapsed: 1.497 s
% 12.07/1.95  % (27526)------------------------------
% 12.07/1.95  % (27526)------------------------------
% 12.07/1.95  % (27503)Success in time 1.569 s
%------------------------------------------------------------------------------
