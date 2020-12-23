%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:26 EST 2020

% Result     : Theorem 1.73s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 219 expanded)
%              Number of leaves         :   15 (  55 expanded)
%              Depth                    :   24
%              Number of atoms          :  264 ( 863 expanded)
%              Number of equality atoms :   45 ( 143 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3039,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3036,f35])).

fof(f35,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k7_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k7_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k7_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 != k7_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 = k7_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f3036,plain,(
    ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f3035,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f3035,plain,(
    ~ v1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f3034,f189])).

fof(f189,plain,(
    r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(resolution,[],[f185,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f185,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(k1_relat_1(sK1),X0),sK0)
      | r1_xboole_0(k1_relat_1(sK1),X0) ) ),
    inference(resolution,[],[f184,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f184,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f183,f61])).

fof(f61,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f52,f40])).

fof(f40,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f183,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(forward_demodulation,[],[f182,f38])).

fof(f38,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f182,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f181,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f181,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ r2_hidden(X0,sK0)
      | r1_xboole_0(k1_relat_1(sK1),sK0) ) ),
    inference(subsumption_resolution,[],[f178,f35])).

fof(f178,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ r2_hidden(X0,sK0)
      | ~ v1_relat_1(sK1)
      | r1_xboole_0(k1_relat_1(sK1),sK0) ) ),
    inference(superposition,[],[f55,f36])).

fof(f36,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(f3034,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(trivial_inequality_removal,[],[f3014])).

fof(f3014,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f37,f2865])).

fof(f2865,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(trivial_inequality_removal,[],[f2822])).

fof(f2822,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f41,f2798])).

fof(f2798,plain,(
    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f2787,f253])).

fof(f253,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f249,f86])).

fof(f86,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,X2)
      | ~ r1_xboole_0(X2,X2) ) ),
    inference(resolution,[],[f84,f62])).

fof(f62,plain,(
    ! [X2,X1] :
      ( ~ r1_xboole_0(X2,k1_tarski(X1))
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f52,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f69,f43])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X1,X2),X0)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X2) ) ),
    inference(resolution,[],[f45,f43])).

fof(f249,plain,(
    ! [X4] :
      ( r2_hidden(sK3(k1_xboole_0,X4),X4)
      | k1_xboole_0 = X4 ) ),
    inference(forward_demodulation,[],[f233,f38])).

fof(f233,plain,(
    ! [X4] :
      ( k1_relat_1(k1_xboole_0) = X4
      | r2_hidden(sK3(k1_xboole_0,X4),X4) ) ),
    inference(resolution,[],[f50,f61])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
      | k1_relat_1(X0) = X1
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f28,f31,f30,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f2787,plain,(
    ! [X0] : r1_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),X0) ),
    inference(subsumption_resolution,[],[f2786,f35])).

fof(f2786,plain,(
    ! [X0] :
      ( r1_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(duplicate_literal_removal,[],[f2777])).

fof(f2777,plain,(
    ! [X0] :
      ( r1_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),X0)
      | ~ v1_relat_1(sK1)
      | r1_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),X0) ) ),
    inference(resolution,[],[f2773,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(k1_relat_1(k7_relat_1(X0,X1)),X2),X1)
      | ~ v1_relat_1(X0)
      | r1_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X2) ) ),
    inference(resolution,[],[f53,f43])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2773,plain,(
    ! [X47,X48] :
      ( ~ r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,X47)),X48),sK0)
      | r1_xboole_0(k1_relat_1(k7_relat_1(sK1,X47)),X48) ) ),
    inference(subsumption_resolution,[],[f2754,f35])).

fof(f2754,plain,(
    ! [X47,X48] :
      ( ~ v1_relat_1(sK1)
      | r1_xboole_0(k1_relat_1(k7_relat_1(sK1,X47)),X48)
      | ~ r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,X47)),X48),sK0) ) ),
    inference(resolution,[],[f119,f184])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(k1_relat_1(k7_relat_1(X0,X1)),X2),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | r1_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X2) ) ),
    inference(resolution,[],[f54,f43])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f37,plain,
    ( k1_xboole_0 != k7_relat_1(sK1,sK0)
    | ~ r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:37:47 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.20/0.47  % (21187)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (21194)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (21193)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (21201)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.48  % (21190)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (21192)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (21199)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.49  % (21202)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (21205)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.50  % (21200)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (21188)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (21189)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.51  % (21195)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.51  % (21204)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.51  % (21206)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.51  % (21198)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.51  % (21203)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.51  % (21188)Refutation not found, incomplete strategy% (21188)------------------------------
% 0.20/0.51  % (21188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (21188)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (21188)Memory used [KB]: 10618
% 0.20/0.51  % (21188)Time elapsed: 0.090 s
% 0.20/0.51  % (21188)------------------------------
% 0.20/0.51  % (21188)------------------------------
% 0.20/0.51  % (21197)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.51  % (21196)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.52  % (21207)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.52  % (21208)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.53  % (21208)Refutation not found, incomplete strategy% (21208)------------------------------
% 0.20/0.53  % (21208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (21208)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (21208)Memory used [KB]: 10618
% 0.20/0.53  % (21208)Time elapsed: 0.114 s
% 0.20/0.53  % (21208)------------------------------
% 0.20/0.53  % (21208)------------------------------
% 1.73/0.61  % (21206)Refutation found. Thanks to Tanya!
% 1.73/0.61  % SZS status Theorem for theBenchmark
% 1.73/0.61  % SZS output start Proof for theBenchmark
% 1.73/0.61  fof(f3039,plain,(
% 1.73/0.61    $false),
% 1.73/0.61    inference(subsumption_resolution,[],[f3036,f35])).
% 1.73/0.61  fof(f35,plain,(
% 1.73/0.61    v1_relat_1(sK1)),
% 1.73/0.61    inference(cnf_transformation,[],[f24])).
% 1.73/0.61  fof(f24,plain,(
% 1.73/0.61    (~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 1.73/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).
% 1.73/0.61  fof(f23,plain,(
% 1.73/0.61    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 1.73/0.61    introduced(choice_axiom,[])).
% 1.73/0.61  fof(f22,plain,(
% 1.73/0.61    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1))),
% 1.73/0.61    inference(flattening,[],[f21])).
% 1.73/0.61  fof(f21,plain,(
% 1.73/0.61    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 1.73/0.61    inference(nnf_transformation,[],[f13])).
% 1.73/0.61  fof(f13,plain,(
% 1.73/0.61    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.73/0.61    inference(ennf_transformation,[],[f11])).
% 1.73/0.61  fof(f11,negated_conjecture,(
% 1.73/0.61    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.73/0.61    inference(negated_conjecture,[],[f10])).
% 1.73/0.61  fof(f10,conjecture,(
% 1.73/0.61    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.73/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 1.73/0.61  fof(f3036,plain,(
% 1.73/0.61    ~v1_relat_1(sK1)),
% 1.73/0.61    inference(resolution,[],[f3035,f46])).
% 1.73/0.61  fof(f46,plain,(
% 1.73/0.61    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f17])).
% 1.73/0.61  fof(f17,plain,(
% 1.73/0.61    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.73/0.61    inference(ennf_transformation,[],[f6])).
% 1.73/0.61  fof(f6,axiom,(
% 1.73/0.61    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.73/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.73/0.61  fof(f3035,plain,(
% 1.73/0.61    ~v1_relat_1(k7_relat_1(sK1,sK0))),
% 1.73/0.61    inference(subsumption_resolution,[],[f3034,f189])).
% 1.73/0.61  fof(f189,plain,(
% 1.73/0.61    r1_xboole_0(k1_relat_1(sK1),sK0)),
% 1.73/0.61    inference(duplicate_literal_removal,[],[f188])).
% 1.73/0.61  fof(f188,plain,(
% 1.73/0.61    r1_xboole_0(k1_relat_1(sK1),sK0) | r1_xboole_0(k1_relat_1(sK1),sK0)),
% 1.73/0.61    inference(resolution,[],[f185,f44])).
% 1.73/0.61  fof(f44,plain,(
% 1.73/0.61    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f26])).
% 1.73/0.61  fof(f26,plain,(
% 1.73/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.73/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f25])).
% 1.73/0.61  fof(f25,plain,(
% 1.73/0.61    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.73/0.61    introduced(choice_axiom,[])).
% 1.73/0.61  fof(f16,plain,(
% 1.73/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.73/0.61    inference(ennf_transformation,[],[f12])).
% 1.73/0.61  fof(f12,plain,(
% 1.73/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.73/0.61    inference(rectify,[],[f2])).
% 1.73/0.61  fof(f2,axiom,(
% 1.73/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.73/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.73/0.61  fof(f185,plain,(
% 1.73/0.61    ( ! [X0] : (~r2_hidden(sK2(k1_relat_1(sK1),X0),sK0) | r1_xboole_0(k1_relat_1(sK1),X0)) )),
% 1.73/0.61    inference(resolution,[],[f184,f43])).
% 1.73/0.61  fof(f43,plain,(
% 1.73/0.61    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f26])).
% 1.73/0.61  fof(f184,plain,(
% 1.73/0.61    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(X0,sK0)) )),
% 1.73/0.61    inference(subsumption_resolution,[],[f183,f61])).
% 1.73/0.61  fof(f61,plain,(
% 1.73/0.61    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.73/0.61    inference(resolution,[],[f52,f40])).
% 1.73/0.61  fof(f40,plain,(
% 1.73/0.61    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f3])).
% 1.73/0.61  fof(f3,axiom,(
% 1.73/0.61    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.73/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.73/0.61  fof(f52,plain,(
% 1.73/0.61    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f19])).
% 1.73/0.61  fof(f19,plain,(
% 1.73/0.61    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 1.73/0.61    inference(ennf_transformation,[],[f4])).
% 1.73/0.61  fof(f4,axiom,(
% 1.73/0.61    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 1.73/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 1.73/0.61  fof(f183,plain,(
% 1.73/0.61    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(X0,sK0)) )),
% 1.73/0.61    inference(forward_demodulation,[],[f182,f38])).
% 1.73/0.61  fof(f38,plain,(
% 1.73/0.61    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.73/0.61    inference(cnf_transformation,[],[f7])).
% 1.73/0.61  fof(f7,axiom,(
% 1.73/0.61    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.73/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.73/0.61  fof(f182,plain,(
% 1.73/0.61    ( ! [X0] : (r2_hidden(X0,k1_relat_1(k1_xboole_0)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(X0,sK0)) )),
% 1.73/0.61    inference(subsumption_resolution,[],[f181,f45])).
% 1.73/0.61  fof(f45,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f26])).
% 1.73/0.61  fof(f181,plain,(
% 1.73/0.61    ( ! [X0] : (r2_hidden(X0,k1_relat_1(k1_xboole_0)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(X0,sK0) | r1_xboole_0(k1_relat_1(sK1),sK0)) )),
% 1.73/0.61    inference(subsumption_resolution,[],[f178,f35])).
% 1.73/0.61  fof(f178,plain,(
% 1.73/0.61    ( ! [X0] : (r2_hidden(X0,k1_relat_1(k1_xboole_0)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(X0,sK0) | ~v1_relat_1(sK1) | r1_xboole_0(k1_relat_1(sK1),sK0)) )),
% 1.73/0.61    inference(superposition,[],[f55,f36])).
% 1.73/0.61  fof(f36,plain,(
% 1.73/0.61    k1_xboole_0 = k7_relat_1(sK1,sK0) | r1_xboole_0(k1_relat_1(sK1),sK0)),
% 1.73/0.61    inference(cnf_transformation,[],[f24])).
% 1.73/0.61  fof(f55,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f34])).
% 1.73/0.61  fof(f34,plain,(
% 1.73/0.61    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 1.73/0.61    inference(flattening,[],[f33])).
% 1.73/0.61  fof(f33,plain,(
% 1.73/0.61    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 1.73/0.61    inference(nnf_transformation,[],[f20])).
% 1.73/0.61  fof(f20,plain,(
% 1.73/0.61    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 1.73/0.61    inference(ennf_transformation,[],[f9])).
% 1.73/0.61  fof(f9,axiom,(
% 1.73/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 1.73/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).
% 1.73/0.61  fof(f3034,plain,(
% 1.73/0.61    ~r1_xboole_0(k1_relat_1(sK1),sK0) | ~v1_relat_1(k7_relat_1(sK1,sK0))),
% 1.73/0.61    inference(trivial_inequality_removal,[],[f3014])).
% 1.73/0.61  fof(f3014,plain,(
% 1.73/0.61    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k1_relat_1(sK1),sK0) | ~v1_relat_1(k7_relat_1(sK1,sK0))),
% 1.73/0.61    inference(superposition,[],[f37,f2865])).
% 1.73/0.61  fof(f2865,plain,(
% 1.73/0.61    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~v1_relat_1(k7_relat_1(sK1,sK0))),
% 1.73/0.61    inference(trivial_inequality_removal,[],[f2822])).
% 1.73/0.61  fof(f2822,plain,(
% 1.73/0.61    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k7_relat_1(sK1,sK0) | ~v1_relat_1(k7_relat_1(sK1,sK0))),
% 1.73/0.61    inference(superposition,[],[f41,f2798])).
% 1.73/0.61  fof(f2798,plain,(
% 1.73/0.61    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.73/0.61    inference(resolution,[],[f2787,f253])).
% 1.73/0.61  fof(f253,plain,(
% 1.73/0.61    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.73/0.61    inference(resolution,[],[f249,f86])).
% 1.73/0.61  fof(f86,plain,(
% 1.73/0.61    ( ! [X2,X3] : (~r2_hidden(X3,X2) | ~r1_xboole_0(X2,X2)) )),
% 1.73/0.61    inference(resolution,[],[f84,f62])).
% 1.73/0.61  fof(f62,plain,(
% 1.73/0.61    ( ! [X2,X1] : (~r1_xboole_0(X2,k1_tarski(X1)) | ~r2_hidden(X1,X2)) )),
% 1.73/0.61    inference(resolution,[],[f52,f47])).
% 1.73/0.61  fof(f47,plain,(
% 1.73/0.61    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f18])).
% 1.73/0.61  fof(f18,plain,(
% 1.73/0.61    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.73/0.61    inference(ennf_transformation,[],[f1])).
% 1.73/0.61  fof(f1,axiom,(
% 1.73/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.73/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.73/0.61  fof(f84,plain,(
% 1.73/0.61    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X0)) )),
% 1.73/0.61    inference(duplicate_literal_removal,[],[f81])).
% 1.73/0.61  fof(f81,plain,(
% 1.73/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1) | r1_xboole_0(X0,X1)) )),
% 1.73/0.61    inference(resolution,[],[f69,f43])).
% 1.73/0.61  fof(f69,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X1,X2),X0) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X2)) )),
% 1.73/0.61    inference(resolution,[],[f45,f43])).
% 1.73/0.61  fof(f249,plain,(
% 1.73/0.61    ( ! [X4] : (r2_hidden(sK3(k1_xboole_0,X4),X4) | k1_xboole_0 = X4) )),
% 1.73/0.61    inference(forward_demodulation,[],[f233,f38])).
% 1.73/0.61  fof(f233,plain,(
% 1.73/0.61    ( ! [X4] : (k1_relat_1(k1_xboole_0) = X4 | r2_hidden(sK3(k1_xboole_0,X4),X4)) )),
% 1.73/0.61    inference(resolution,[],[f50,f61])).
% 1.73/0.61  fof(f50,plain,(
% 1.73/0.61    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | k1_relat_1(X0) = X1 | r2_hidden(sK3(X0,X1),X1)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f32])).
% 1.73/0.61  fof(f32,plain,(
% 1.73/0.61    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.73/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f28,f31,f30,f29])).
% 1.73/0.61  fof(f29,plain,(
% 1.73/0.61    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.73/0.61    introduced(choice_axiom,[])).
% 1.73/0.61  fof(f30,plain,(
% 1.73/0.61    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0))),
% 1.73/0.61    introduced(choice_axiom,[])).
% 1.73/0.61  fof(f31,plain,(
% 1.73/0.61    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0))),
% 1.73/0.61    introduced(choice_axiom,[])).
% 1.73/0.61  fof(f28,plain,(
% 1.73/0.61    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.73/0.61    inference(rectify,[],[f27])).
% 1.73/0.61  fof(f27,plain,(
% 1.73/0.61    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 1.73/0.61    inference(nnf_transformation,[],[f5])).
% 1.73/0.61  fof(f5,axiom,(
% 1.73/0.61    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.73/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 1.73/0.61  fof(f2787,plain,(
% 1.73/0.61    ( ! [X0] : (r1_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),X0)) )),
% 1.73/0.61    inference(subsumption_resolution,[],[f2786,f35])).
% 1.73/0.61  fof(f2786,plain,(
% 1.73/0.61    ( ! [X0] : (r1_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),X0) | ~v1_relat_1(sK1)) )),
% 1.73/0.61    inference(duplicate_literal_removal,[],[f2777])).
% 1.73/0.61  fof(f2777,plain,(
% 1.73/0.61    ( ! [X0] : (r1_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),X0) | ~v1_relat_1(sK1) | r1_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),X0)) )),
% 1.73/0.61    inference(resolution,[],[f2773,f71])).
% 1.73/0.61  fof(f71,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (r2_hidden(sK2(k1_relat_1(k7_relat_1(X0,X1)),X2),X1) | ~v1_relat_1(X0) | r1_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X2)) )),
% 1.73/0.61    inference(resolution,[],[f53,f43])).
% 1.73/0.61  fof(f53,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f34])).
% 1.73/0.61  fof(f2773,plain,(
% 1.73/0.61    ( ! [X47,X48] : (~r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,X47)),X48),sK0) | r1_xboole_0(k1_relat_1(k7_relat_1(sK1,X47)),X48)) )),
% 1.73/0.61    inference(subsumption_resolution,[],[f2754,f35])).
% 1.73/0.61  fof(f2754,plain,(
% 1.73/0.61    ( ! [X47,X48] : (~v1_relat_1(sK1) | r1_xboole_0(k1_relat_1(k7_relat_1(sK1,X47)),X48) | ~r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,X47)),X48),sK0)) )),
% 1.73/0.61    inference(resolution,[],[f119,f184])).
% 1.73/0.61  fof(f119,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (r2_hidden(sK2(k1_relat_1(k7_relat_1(X0,X1)),X2),k1_relat_1(X0)) | ~v1_relat_1(X0) | r1_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X2)) )),
% 1.73/0.61    inference(resolution,[],[f54,f43])).
% 1.73/0.61  fof(f54,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f34])).
% 1.73/0.61  fof(f41,plain,(
% 1.73/0.61    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f15])).
% 1.73/0.61  fof(f15,plain,(
% 1.73/0.61    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.73/0.61    inference(flattening,[],[f14])).
% 1.73/0.61  fof(f14,plain,(
% 1.73/0.61    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.73/0.61    inference(ennf_transformation,[],[f8])).
% 1.73/0.61  fof(f8,axiom,(
% 1.73/0.61    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.73/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.73/0.61  fof(f37,plain,(
% 1.73/0.61    k1_xboole_0 != k7_relat_1(sK1,sK0) | ~r1_xboole_0(k1_relat_1(sK1),sK0)),
% 1.73/0.61    inference(cnf_transformation,[],[f24])).
% 1.73/0.61  % SZS output end Proof for theBenchmark
% 1.73/0.61  % (21206)------------------------------
% 1.73/0.61  % (21206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.61  % (21206)Termination reason: Refutation
% 1.73/0.61  
% 1.73/0.61  % (21206)Memory used [KB]: 2686
% 1.73/0.61  % (21206)Time elapsed: 0.200 s
% 1.73/0.61  % (21206)------------------------------
% 1.73/0.61  % (21206)------------------------------
% 1.73/0.61  % (21184)Success in time 0.249 s
%------------------------------------------------------------------------------
