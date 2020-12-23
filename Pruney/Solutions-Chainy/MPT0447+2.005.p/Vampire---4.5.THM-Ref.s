%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:08 EST 2020

% Result     : Theorem 2.22s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 338 expanded)
%              Number of leaves         :   29 ( 109 expanded)
%              Depth                    :   20
%              Number of atoms          :  274 ( 866 expanded)
%              Number of equality atoms :   45 ( 154 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f920,plain,(
    $false ),
    inference(subsumption_resolution,[],[f919,f74])).

fof(f74,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f919,plain,(
    ~ r1_tarski(k1_xboole_0,k2_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f914,f682])).

fof(f682,plain,(
    k1_xboole_0 = k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f680,f129])).

fof(f129,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f116,f109])).

fof(f109,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f75,f84])).

fof(f84,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f75,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f116,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f99,f84])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f680,plain,(
    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f679,f171])).

fof(f171,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f168,f80])).

fof(f80,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f168,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f128,f155])).

fof(f155,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f150,f151])).

fof(f151,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0)) ),
    inference(resolution,[],[f150,f80])).

fof(f150,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k1_setfam_1(k1_enumset1(X1,X1,k1_xboole_0))) ),
    inference(resolution,[],[f114,f73])).

fof(f73,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f89,f107])).

fof(f107,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f85,f86])).

fof(f86,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f85,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f128,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f60,f63,f62,f61])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f679,plain,(
    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f678,f70])).

fof(f70,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f49,f48])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
          & r1_tarski(sK0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
        & r1_tarski(sK0,X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(f678,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0))
    | ~ r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f276,f116])).

fof(f276,plain,(
    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(resolution,[],[f217,f68])).

fof(f68,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f217,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(X1,sK1))) ) ),
    inference(resolution,[],[f79,f69])).

fof(f69,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).

fof(f914,plain,(
    ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k2_relat_1(sK1)) ),
    inference(resolution,[],[f910,f227])).

fof(f227,plain,(
    ! [X2] :
      ( r1_tarski(X2,k3_relat_1(sK1))
      | ~ r1_tarski(k6_subset_1(X2,k1_relat_1(sK1)),k2_relat_1(sK1)) ) ),
    inference(superposition,[],[f120,f198])).

fof(f198,plain,(
    k3_relat_1(sK1) = k3_tarski(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(resolution,[],[f110,f69])).

fof(f110,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f77,f108])).

fof(f108,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f87,f86])).

fof(f87,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f77,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f102,f108,f84])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f910,plain,(
    ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f909,f74])).

fof(f909,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f903,f572])).

fof(f572,plain,(
    k1_xboole_0 = k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(resolution,[],[f562,f129])).

fof(f562,plain,(
    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f561,f186])).

fof(f186,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f180,f80])).

fof(f180,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f179,f72])).

fof(f72,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f179,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f172,f76])).

fof(f76,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f172,plain,(
    ! [X3] :
      ( ~ v1_relat_1(k1_xboole_0)
      | ~ r2_hidden(X3,k2_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f168,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f55])).

fof(f55,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
     => r2_hidden(sK4(X1),k1_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

fof(f561,plain,(
    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f560,f70])).

fof(f560,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k1_xboole_0))
    | ~ r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f256,f116])).

fof(f256,plain,(
    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(resolution,[],[f213,f68])).

fof(f213,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(X1,sK1))) ) ),
    inference(resolution,[],[f78,f69])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relat_1)).

fof(f903,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k1_relat_1(sK1)) ),
    inference(resolution,[],[f880,f355])).

fof(f355,plain,(
    ! [X1] :
      ( r1_tarski(X1,k3_relat_1(sK1))
      | ~ r1_tarski(k6_subset_1(X1,k2_relat_1(sK1)),k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f192,f198])).

fof(f192,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k3_tarski(k1_enumset1(X1,X1,X0)))
      | ~ r1_tarski(k6_subset_1(X2,X0),X1) ) ),
    inference(superposition,[],[f120,f113])).

fof(f113,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f83,f86,f86])).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f880,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f209,f71])).

fof(f71,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f50])).

fof(f209,plain,(
    ! [X0] :
      ( r1_tarski(k3_relat_1(sK0),X0)
      | ~ r1_tarski(k2_relat_1(sK0),X0)
      | ~ r1_tarski(k1_relat_1(sK0),X0) ) ),
    inference(superposition,[],[f121,f197])).

fof(f197,plain,(
    k3_relat_1(sK0) = k3_tarski(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(resolution,[],[f110,f68])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f103,f108])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:16:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (8382)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (8404)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.49  % (8396)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.50  % (8390)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.50  % (8377)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (8405)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.51  % (8405)Refutation not found, incomplete strategy% (8405)------------------------------
% 0.21/0.51  % (8405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (8384)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (8405)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (8405)Memory used [KB]: 10746
% 0.21/0.52  % (8405)Time elapsed: 0.109 s
% 0.21/0.52  % (8405)------------------------------
% 0.21/0.52  % (8405)------------------------------
% 0.21/0.53  % (8381)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (8383)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (8380)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (8378)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (8397)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (8379)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (8399)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (8403)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (8406)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (8395)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (8398)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (8388)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (8406)Refutation not found, incomplete strategy% (8406)------------------------------
% 0.21/0.54  % (8406)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8401)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (8394)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (8402)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (8393)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (8391)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.55  % (8387)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (8393)Refutation not found, incomplete strategy% (8393)------------------------------
% 0.21/0.55  % (8393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (8386)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (8389)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.56  % (8387)Refutation not found, incomplete strategy% (8387)------------------------------
% 0.21/0.56  % (8387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (8406)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (8406)Memory used [KB]: 1663
% 0.21/0.56  % (8406)Time elapsed: 0.141 s
% 0.21/0.56  % (8406)------------------------------
% 0.21/0.56  % (8406)------------------------------
% 0.21/0.56  % (8387)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  % (8393)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (8393)Memory used [KB]: 10618
% 0.21/0.56  % (8393)Time elapsed: 0.140 s
% 0.21/0.56  % (8393)------------------------------
% 0.21/0.56  % (8393)------------------------------
% 0.21/0.56  
% 0.21/0.56  % (8387)Memory used [KB]: 10746
% 0.21/0.56  % (8387)Time elapsed: 0.153 s
% 0.21/0.56  % (8387)------------------------------
% 0.21/0.56  % (8387)------------------------------
% 1.48/0.58  % (8392)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.48/0.59  % (8385)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.80/0.60  % (8400)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 2.22/0.65  % (8399)Refutation found. Thanks to Tanya!
% 2.22/0.65  % SZS status Theorem for theBenchmark
% 2.22/0.65  % SZS output start Proof for theBenchmark
% 2.22/0.65  fof(f920,plain,(
% 2.22/0.65    $false),
% 2.22/0.65    inference(subsumption_resolution,[],[f919,f74])).
% 2.22/0.65  fof(f74,plain,(
% 2.22/0.65    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f9])).
% 2.22/0.65  fof(f9,axiom,(
% 2.22/0.65    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.22/0.65  fof(f919,plain,(
% 2.22/0.65    ~r1_tarski(k1_xboole_0,k2_relat_1(sK1))),
% 2.22/0.65    inference(forward_demodulation,[],[f914,f682])).
% 2.22/0.65  fof(f682,plain,(
% 2.22/0.65    k1_xboole_0 = k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1))),
% 2.22/0.65    inference(resolution,[],[f680,f129])).
% 2.22/0.65  fof(f129,plain,(
% 2.22/0.65    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.22/0.65    inference(superposition,[],[f116,f109])).
% 2.22/0.65  fof(f109,plain,(
% 2.22/0.65    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 2.22/0.65    inference(definition_unfolding,[],[f75,f84])).
% 2.22/0.65  fof(f84,plain,(
% 2.22/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f19])).
% 2.22/0.65  fof(f19,axiom,(
% 2.22/0.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.22/0.65  fof(f75,plain,(
% 2.22/0.65    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.22/0.65    inference(cnf_transformation,[],[f10])).
% 2.22/0.65  fof(f10,axiom,(
% 2.22/0.65    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.22/0.65  fof(f116,plain,(
% 2.22/0.65    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 2.22/0.65    inference(definition_unfolding,[],[f99,f84])).
% 2.22/0.65  fof(f99,plain,(
% 2.22/0.65    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f65])).
% 2.22/0.65  fof(f65,plain,(
% 2.22/0.65    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 2.22/0.65    inference(nnf_transformation,[],[f6])).
% 2.22/0.65  fof(f6,axiom,(
% 2.22/0.65    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.22/0.65  fof(f680,plain,(
% 2.22/0.65    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_xboole_0)),
% 2.22/0.65    inference(forward_demodulation,[],[f679,f171])).
% 2.22/0.65  fof(f171,plain,(
% 2.22/0.65    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.22/0.65    inference(resolution,[],[f168,f80])).
% 2.22/0.65  fof(f80,plain,(
% 2.22/0.65    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 2.22/0.65    inference(cnf_transformation,[],[f52])).
% 2.22/0.65  fof(f52,plain,(
% 2.22/0.65    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 2.22/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f51])).
% 2.22/0.65  fof(f51,plain,(
% 2.22/0.65    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 2.22/0.65    introduced(choice_axiom,[])).
% 2.22/0.65  fof(f37,plain,(
% 2.22/0.65    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.22/0.65    inference(ennf_transformation,[],[f4])).
% 2.22/0.65  fof(f4,axiom,(
% 2.22/0.65    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.22/0.65  fof(f168,plain,(
% 2.22/0.65    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0))) )),
% 2.22/0.65    inference(resolution,[],[f128,f155])).
% 2.22/0.65  fof(f155,plain,(
% 2.22/0.65    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.22/0.65    inference(backward_demodulation,[],[f150,f151])).
% 2.22/0.65  fof(f151,plain,(
% 2.22/0.65    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0))) )),
% 2.22/0.65    inference(resolution,[],[f150,f80])).
% 2.22/0.65  fof(f150,plain,(
% 2.22/0.65    ( ! [X0,X1] : (~r2_hidden(X0,k1_setfam_1(k1_enumset1(X1,X1,k1_xboole_0)))) )),
% 2.22/0.65    inference(resolution,[],[f114,f73])).
% 2.22/0.65  fof(f73,plain,(
% 2.22/0.65    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f13])).
% 2.22/0.65  fof(f13,axiom,(
% 2.22/0.65    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 2.22/0.65  fof(f114,plain,(
% 2.22/0.65    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 2.22/0.65    inference(definition_unfolding,[],[f89,f107])).
% 2.22/0.65  fof(f107,plain,(
% 2.22/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 2.22/0.65    inference(definition_unfolding,[],[f85,f86])).
% 2.22/0.65  fof(f86,plain,(
% 2.22/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f17])).
% 2.22/0.65  fof(f17,axiom,(
% 2.22/0.65    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.22/0.65  fof(f85,plain,(
% 2.22/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.22/0.65    inference(cnf_transformation,[],[f20])).
% 2.22/0.65  fof(f20,axiom,(
% 2.22/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.22/0.65  fof(f89,plain,(
% 2.22/0.65    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.22/0.65    inference(cnf_transformation,[],[f54])).
% 2.22/0.65  fof(f54,plain,(
% 2.22/0.65    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.22/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f53])).
% 2.22/0.65  fof(f53,plain,(
% 2.22/0.65    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 2.22/0.65    introduced(choice_axiom,[])).
% 2.22/0.65  fof(f38,plain,(
% 2.22/0.65    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.22/0.65    inference(ennf_transformation,[],[f30])).
% 2.22/0.65  fof(f30,plain,(
% 2.22/0.65    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.22/0.65    inference(rectify,[],[f3])).
% 2.22/0.65  fof(f3,axiom,(
% 2.22/0.65    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.22/0.65  fof(f128,plain,(
% 2.22/0.65    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 2.22/0.65    inference(equality_resolution,[],[f94])).
% 2.22/0.65  fof(f94,plain,(
% 2.22/0.65    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 2.22/0.65    inference(cnf_transformation,[],[f64])).
% 2.22/0.65  fof(f64,plain,(
% 2.22/0.65    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.22/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f60,f63,f62,f61])).
% 2.22/0.65  fof(f61,plain,(
% 2.22/0.65    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 2.22/0.65    introduced(choice_axiom,[])).
% 2.22/0.65  fof(f62,plain,(
% 2.22/0.65    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0))),
% 2.22/0.65    introduced(choice_axiom,[])).
% 2.22/0.65  fof(f63,plain,(
% 2.22/0.65    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0))),
% 2.22/0.65    introduced(choice_axiom,[])).
% 2.22/0.65  fof(f60,plain,(
% 2.22/0.65    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.22/0.65    inference(rectify,[],[f59])).
% 2.22/0.65  fof(f59,plain,(
% 2.22/0.65    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.22/0.65    inference(nnf_transformation,[],[f22])).
% 2.22/0.65  fof(f22,axiom,(
% 2.22/0.65    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 2.22/0.65  fof(f679,plain,(
% 2.22/0.65    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0))),
% 2.22/0.65    inference(subsumption_resolution,[],[f678,f70])).
% 2.22/0.65  fof(f70,plain,(
% 2.22/0.65    r1_tarski(sK0,sK1)),
% 2.22/0.65    inference(cnf_transformation,[],[f50])).
% 2.22/0.65  fof(f50,plain,(
% 2.22/0.65    (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 2.22/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f49,f48])).
% 2.22/0.65  fof(f48,plain,(
% 2.22/0.65    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 2.22/0.65    introduced(choice_axiom,[])).
% 2.22/0.65  fof(f49,plain,(
% 2.22/0.65    ? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1))),
% 2.22/0.65    introduced(choice_axiom,[])).
% 2.22/0.65  fof(f32,plain,(
% 2.22/0.65    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.22/0.65    inference(flattening,[],[f31])).
% 2.22/0.65  fof(f31,plain,(
% 2.22/0.65    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.22/0.65    inference(ennf_transformation,[],[f28])).
% 2.22/0.65  fof(f28,negated_conjecture,(
% 2.22/0.65    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 2.22/0.65    inference(negated_conjecture,[],[f27])).
% 2.22/0.65  fof(f27,conjecture,(
% 2.22/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).
% 2.22/0.65  fof(f678,plain,(
% 2.22/0.65    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0)) | ~r1_tarski(sK0,sK1)),
% 2.22/0.65    inference(superposition,[],[f276,f116])).
% 2.22/0.65  fof(f276,plain,(
% 2.22/0.65    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))),
% 2.22/0.65    inference(resolution,[],[f217,f68])).
% 2.22/0.65  fof(f68,plain,(
% 2.22/0.65    v1_relat_1(sK0)),
% 2.22/0.65    inference(cnf_transformation,[],[f50])).
% 2.22/0.65  fof(f217,plain,(
% 2.22/0.65    ( ! [X1] : (~v1_relat_1(X1) | r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(X1,sK1)))) )),
% 2.22/0.65    inference(resolution,[],[f79,f69])).
% 2.22/0.65  fof(f69,plain,(
% 2.22/0.65    v1_relat_1(sK1)),
% 2.22/0.65    inference(cnf_transformation,[],[f50])).
% 2.22/0.65  fof(f79,plain,(
% 2.22/0.65    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f36])).
% 2.22/0.65  fof(f36,plain,(
% 2.22/0.65    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.22/0.65    inference(ennf_transformation,[],[f24])).
% 2.22/0.65  fof(f24,axiom,(
% 2.22/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).
% 2.22/0.65  fof(f914,plain,(
% 2.22/0.65    ~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k2_relat_1(sK1))),
% 2.22/0.65    inference(resolution,[],[f910,f227])).
% 2.22/0.65  fof(f227,plain,(
% 2.22/0.65    ( ! [X2] : (r1_tarski(X2,k3_relat_1(sK1)) | ~r1_tarski(k6_subset_1(X2,k1_relat_1(sK1)),k2_relat_1(sK1))) )),
% 2.22/0.65    inference(superposition,[],[f120,f198])).
% 2.22/0.65  fof(f198,plain,(
% 2.22/0.65    k3_relat_1(sK1) = k3_tarski(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k2_relat_1(sK1)))),
% 2.22/0.65    inference(resolution,[],[f110,f69])).
% 2.22/0.65  fof(f110,plain,(
% 2.22/0.65    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))) )),
% 2.22/0.65    inference(definition_unfolding,[],[f77,f108])).
% 2.22/0.65  fof(f108,plain,(
% 2.22/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 2.22/0.65    inference(definition_unfolding,[],[f87,f86])).
% 2.22/0.65  fof(f87,plain,(
% 2.22/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.22/0.65    inference(cnf_transformation,[],[f18])).
% 2.22/0.65  fof(f18,axiom,(
% 2.22/0.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.22/0.65  fof(f77,plain,(
% 2.22/0.65    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f34])).
% 2.22/0.65  fof(f34,plain,(
% 2.22/0.65    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.22/0.65    inference(ennf_transformation,[],[f23])).
% 2.22/0.65  fof(f23,axiom,(
% 2.22/0.65    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 2.22/0.65  fof(f120,plain,(
% 2.22/0.65    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) | ~r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 2.22/0.66    inference(definition_unfolding,[],[f102,f108,f84])).
% 2.22/0.66  fof(f102,plain,(
% 2.22/0.66    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.22/0.66    inference(cnf_transformation,[],[f43])).
% 2.22/0.66  fof(f43,plain,(
% 2.22/0.66    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.22/0.66    inference(ennf_transformation,[],[f12])).
% 2.22/0.66  fof(f12,axiom,(
% 2.22/0.66    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.22/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 2.22/0.66  fof(f910,plain,(
% 2.22/0.66    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 2.22/0.66    inference(subsumption_resolution,[],[f909,f74])).
% 2.22/0.66  fof(f909,plain,(
% 2.22/0.66    ~r1_tarski(k1_xboole_0,k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 2.22/0.66    inference(forward_demodulation,[],[f903,f572])).
% 2.22/0.66  fof(f572,plain,(
% 2.22/0.66    k1_xboole_0 = k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1))),
% 2.22/0.66    inference(resolution,[],[f562,f129])).
% 2.22/0.66  fof(f562,plain,(
% 2.22/0.66    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k1_xboole_0)),
% 2.22/0.66    inference(forward_demodulation,[],[f561,f186])).
% 2.22/0.66  fof(f186,plain,(
% 2.22/0.66    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.22/0.66    inference(resolution,[],[f180,f80])).
% 2.22/0.66  fof(f180,plain,(
% 2.22/0.66    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0))) )),
% 2.22/0.66    inference(subsumption_resolution,[],[f179,f72])).
% 2.22/0.66  fof(f72,plain,(
% 2.22/0.66    v1_xboole_0(k1_xboole_0)),
% 2.22/0.66    inference(cnf_transformation,[],[f1])).
% 2.22/0.66  fof(f1,axiom,(
% 2.22/0.66    v1_xboole_0(k1_xboole_0)),
% 2.22/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.22/0.66  fof(f179,plain,(
% 2.22/0.66    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)) )),
% 2.22/0.66    inference(resolution,[],[f172,f76])).
% 2.22/0.66  fof(f76,plain,(
% 2.22/0.66    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 2.22/0.66    inference(cnf_transformation,[],[f33])).
% 2.22/0.66  fof(f33,plain,(
% 2.22/0.66    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 2.22/0.66    inference(ennf_transformation,[],[f21])).
% 2.22/0.66  fof(f21,axiom,(
% 2.22/0.66    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 2.22/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 2.22/0.66  fof(f172,plain,(
% 2.22/0.66    ( ! [X3] : (~v1_relat_1(k1_xboole_0) | ~r2_hidden(X3,k2_relat_1(k1_xboole_0))) )),
% 2.22/0.66    inference(resolution,[],[f168,f90])).
% 2.22/0.66  fof(f90,plain,(
% 2.22/0.66    ( ! [X0,X1] : (r2_hidden(sK4(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.22/0.66    inference(cnf_transformation,[],[f56])).
% 2.22/0.66  fof(f56,plain,(
% 2.22/0.66    ! [X0,X1] : (r2_hidden(sK4(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.22/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f55])).
% 2.22/0.66  fof(f55,plain,(
% 2.22/0.66    ! [X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(sK4(X1),k1_relat_1(X1)))),
% 2.22/0.66    introduced(choice_axiom,[])).
% 2.22/0.66  fof(f40,plain,(
% 2.22/0.66    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.22/0.66    inference(flattening,[],[f39])).
% 2.22/0.66  fof(f39,plain,(
% 2.22/0.66    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.22/0.66    inference(ennf_transformation,[],[f25])).
% 2.22/0.66  fof(f25,axiom,(
% 2.22/0.66    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 2.22/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).
% 2.22/0.66  fof(f561,plain,(
% 2.22/0.66    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k1_xboole_0))),
% 2.22/0.66    inference(subsumption_resolution,[],[f560,f70])).
% 2.22/0.66  fof(f560,plain,(
% 2.22/0.66    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k1_xboole_0)) | ~r1_tarski(sK0,sK1)),
% 2.22/0.66    inference(superposition,[],[f256,f116])).
% 2.22/0.66  fof(f256,plain,(
% 2.22/0.66    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))),
% 2.22/0.66    inference(resolution,[],[f213,f68])).
% 2.22/0.66  fof(f213,plain,(
% 2.22/0.66    ( ! [X1] : (~v1_relat_1(X1) | r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(X1,sK1)))) )),
% 2.22/0.66    inference(resolution,[],[f78,f69])).
% 2.22/0.66  fof(f78,plain,(
% 2.22/0.66    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X0)) )),
% 2.22/0.66    inference(cnf_transformation,[],[f35])).
% 2.22/0.66  fof(f35,plain,(
% 2.22/0.66    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.22/0.66    inference(ennf_transformation,[],[f26])).
% 2.22/0.66  fof(f26,axiom,(
% 2.22/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 2.22/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relat_1)).
% 2.22/0.66  fof(f903,plain,(
% 2.22/0.66    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | ~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k1_relat_1(sK1))),
% 2.22/0.66    inference(resolution,[],[f880,f355])).
% 2.22/0.66  fof(f355,plain,(
% 2.22/0.66    ( ! [X1] : (r1_tarski(X1,k3_relat_1(sK1)) | ~r1_tarski(k6_subset_1(X1,k2_relat_1(sK1)),k1_relat_1(sK1))) )),
% 2.22/0.66    inference(superposition,[],[f192,f198])).
% 2.22/0.66  fof(f192,plain,(
% 2.22/0.66    ( ! [X2,X0,X1] : (r1_tarski(X2,k3_tarski(k1_enumset1(X1,X1,X0))) | ~r1_tarski(k6_subset_1(X2,X0),X1)) )),
% 2.22/0.66    inference(superposition,[],[f120,f113])).
% 2.22/0.66  fof(f113,plain,(
% 2.22/0.66    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 2.22/0.66    inference(definition_unfolding,[],[f83,f86,f86])).
% 2.22/0.66  fof(f83,plain,(
% 2.22/0.66    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.22/0.66    inference(cnf_transformation,[],[f16])).
% 2.22/0.66  fof(f16,axiom,(
% 2.22/0.66    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.22/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.22/0.66  fof(f880,plain,(
% 2.22/0.66    ~r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 2.22/0.66    inference(resolution,[],[f209,f71])).
% 2.22/0.66  fof(f71,plain,(
% 2.22/0.66    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 2.22/0.66    inference(cnf_transformation,[],[f50])).
% 2.22/0.66  fof(f209,plain,(
% 2.22/0.66    ( ! [X0] : (r1_tarski(k3_relat_1(sK0),X0) | ~r1_tarski(k2_relat_1(sK0),X0) | ~r1_tarski(k1_relat_1(sK0),X0)) )),
% 2.22/0.66    inference(superposition,[],[f121,f197])).
% 2.22/0.66  fof(f197,plain,(
% 2.22/0.66    k3_relat_1(sK0) = k3_tarski(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k2_relat_1(sK0)))),
% 2.22/0.66    inference(resolution,[],[f110,f68])).
% 2.22/0.66  fof(f121,plain,(
% 2.22/0.66    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.22/0.66    inference(definition_unfolding,[],[f103,f108])).
% 2.22/0.66  fof(f103,plain,(
% 2.22/0.66    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.22/0.66    inference(cnf_transformation,[],[f45])).
% 2.22/0.66  fof(f45,plain,(
% 2.22/0.66    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.22/0.66    inference(flattening,[],[f44])).
% 2.22/0.66  fof(f44,plain,(
% 2.22/0.66    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.22/0.66    inference(ennf_transformation,[],[f15])).
% 2.22/0.66  fof(f15,axiom,(
% 2.22/0.66    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 2.22/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 2.22/0.66  % SZS output end Proof for theBenchmark
% 2.22/0.66  % (8399)------------------------------
% 2.22/0.66  % (8399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.66  % (8399)Termination reason: Refutation
% 2.22/0.66  
% 2.22/0.66  % (8399)Memory used [KB]: 7291
% 2.22/0.66  % (8399)Time elapsed: 0.214 s
% 2.22/0.66  % (8399)------------------------------
% 2.22/0.66  % (8399)------------------------------
% 2.22/0.66  % (8376)Success in time 0.289 s
%------------------------------------------------------------------------------
