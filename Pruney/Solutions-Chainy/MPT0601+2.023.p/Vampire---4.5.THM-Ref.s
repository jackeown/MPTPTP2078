%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 121 expanded)
%              Number of leaves         :   17 (  27 expanded)
%              Depth                    :   17
%              Number of atoms          :  241 ( 374 expanded)
%              Number of equality atoms :   62 ( 114 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f149,plain,(
    $false ),
    inference(subsumption_resolution,[],[f148,f132])).

fof(f132,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f131,f37])).

fof(f37,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
      | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
    & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
      | r2_hidden(sK0,k1_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
        | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
      & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
        | r2_hidden(sK0,k1_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f131,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(trivial_inequality_removal,[],[f130])).

fof(f130,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(superposition,[],[f38,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k11_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | r2_hidden(X1,k1_relat_1(X0)) ) ),
    inference(resolution,[],[f96,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f96,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(k1_tarski(X3),k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | k1_xboole_0 = k11_relat_1(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = k11_relat_1(X2,X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r1_xboole_0(k1_tarski(X3),k1_relat_1(X2)) ) ),
    inference(resolution,[],[f71,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0)
      | ~ r1_xboole_0(X1,k1_relat_1(X0)) ) ),
    inference(trivial_inequality_removal,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0)
      | ~ r1_xboole_0(X1,k1_relat_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f49,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_relat_1(X0),k1_tarski(X1))
      | k1_xboole_0 = k11_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k11_relat_1(X0,X1)
      | ~ r1_xboole_0(k1_relat_1(X0),k1_tarski(X1))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f48,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f38,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f148,plain,(
    ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f147,f37])).

fof(f147,plain,
    ( ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(trivial_inequality_removal,[],[f146])).

fof(f146,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(duplicate_literal_removal,[],[f143])).

fof(f143,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(superposition,[],[f120,f39])).

fof(f39,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f120,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | k1_xboole_0 != k11_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f111,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X0),k1_tarski(X1))
      | k1_xboole_0 != k11_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(X0,X1)
      | r1_xboole_0(k1_relat_1(X0),k1_tarski(X1))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f47,f42])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_relat_1(X0),k1_tarski(X1))
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f110,f40])).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ r1_xboole_0(k1_relat_1(X0),k1_tarski(X1)) ) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ r1_xboole_0(k1_relat_1(X0),k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f103,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f103,plain,(
    ! [X4,X3] :
      ( ~ v1_xboole_0(k7_relat_1(X3,k1_tarski(X4)))
      | ~ v1_relat_1(X3)
      | ~ r2_hidden(X4,k1_relat_1(X3)) ) ),
    inference(subsumption_resolution,[],[f100,f98])).

fof(f98,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(superposition,[],[f92,f41])).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f92,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(superposition,[],[f91,f45])).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f91,plain,(
    ! [X2,X0,X1] : ~ v1_xboole_0(k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f90,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f90,plain,(
    ! [X2,X0,X3,X1] : ~ v1_xboole_0(k2_enumset1(X0,X1,X2,X3)) ),
    inference(superposition,[],[f89,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f89,plain,(
    ! [X4,X2,X0,X3,X1] : ~ v1_xboole_0(k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(superposition,[],[f58,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : ~ v1_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : ~ v1_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_subset_1)).

fof(f100,plain,(
    ! [X4,X3] :
      ( ~ v1_xboole_0(k7_relat_1(X3,k1_tarski(X4)))
      | v1_xboole_0(k1_tarski(X4))
      | ~ v1_relat_1(X3)
      | ~ r2_hidden(X4,k1_relat_1(X3)) ) ),
    inference(resolution,[],[f84,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f55,f41])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f84,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X4,k1_relat_1(X3))
      | ~ v1_xboole_0(k7_relat_1(X3,X4))
      | v1_xboole_0(X4)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f44,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f44,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:30:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (22482)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (22481)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (22480)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (22477)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (22483)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (22480)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f148,f132])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f131,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    v1_relat_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    (k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.21/0.48    inference(negated_conjecture,[],[f18])).
% 0.21/0.48  fof(f18,conjecture,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f130])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f129])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.48    inference(superposition,[],[f38,f121])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k11_relat_1(X0,X1) | ~v1_relat_1(X0) | r2_hidden(X1,k1_relat_1(X0))) )),
% 0.21/0.48    inference(resolution,[],[f96,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~r1_xboole_0(k1_tarski(X3),k1_relat_1(X2)) | ~v1_relat_1(X2) | k1_xboole_0 = k11_relat_1(X2,X3)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f94])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    ( ! [X2,X3] : (k1_xboole_0 = k11_relat_1(X2,X3) | ~v1_relat_1(X2) | ~v1_relat_1(X2) | ~r1_xboole_0(k1_tarski(X3),k1_relat_1(X2))) )),
% 0.21/0.48    inference(resolution,[],[f71,f74])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X0),X1) | ~v1_relat_1(X0) | ~r1_xboole_0(X1,k1_relat_1(X0))) )),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f73])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(X0),X1) | ~v1_relat_1(X0) | ~r1_xboole_0(X1,k1_relat_1(X0))) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(X0),X1) | ~v1_relat_1(X0) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(superposition,[],[f49,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 != k7_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X0),k1_tarski(X1)) | k1_xboole_0 = k11_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k11_relat_1(X0,X1) | ~r1_xboole_0(k1_relat_1(X0),k1_tarski(X1)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(superposition,[],[f48,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f147,f37])).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    ~v1_relat_1(sK1) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f146])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK1) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f143])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK1) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.48    inference(superposition,[],[f120,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1))) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f116])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | k1_xboole_0 != k11_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(resolution,[],[f111,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X0),k1_tarski(X1)) | k1_xboole_0 != k11_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X0,X1) | r1_xboole_0(k1_relat_1(X0),k1_tarski(X1)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(superposition,[],[f47,f42])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X0),k1_tarski(X1)) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f110,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~r1_xboole_0(k1_relat_1(X0),k1_tarski(X1))) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f107])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~r1_xboole_0(k1_relat_1(X0),k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(superposition,[],[f103,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    ( ! [X4,X3] : (~v1_xboole_0(k7_relat_1(X3,k1_tarski(X4))) | ~v1_relat_1(X3) | ~r2_hidden(X4,k1_relat_1(X3))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f100,f98])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.21/0.48    inference(superposition,[],[f92,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_xboole_0(k2_tarski(X0,X1))) )),
% 0.21/0.48    inference(superposition,[],[f91,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_xboole_0(k1_enumset1(X0,X1,X2))) )),
% 0.21/0.48    inference(superposition,[],[f90,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~v1_xboole_0(k2_enumset1(X0,X1,X2,X3))) )),
% 0.21/0.48    inference(superposition,[],[f89,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (~v1_xboole_0(k3_enumset1(X0,X1,X2,X3,X4))) )),
% 0.21/0.48    inference(superposition,[],[f58,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : ~v1_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_subset_1)).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    ( ! [X4,X3] : (~v1_xboole_0(k7_relat_1(X3,k1_tarski(X4))) | v1_xboole_0(k1_tarski(X4)) | ~v1_relat_1(X3) | ~r2_hidden(X4,k1_relat_1(X3))) )),
% 0.21/0.48    inference(resolution,[],[f84,f80])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f79])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(superposition,[],[f55,f41])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.48    inference(flattening,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.48    inference(nnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ( ! [X4,X3] : (~r1_tarski(X4,k1_relat_1(X3)) | ~v1_xboole_0(k7_relat_1(X3,X4)) | v1_xboole_0(X4) | ~v1_relat_1(X3)) )),
% 0.21/0.48    inference(superposition,[],[f44,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (22480)------------------------------
% 0.21/0.48  % (22480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (22480)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (22480)Memory used [KB]: 1663
% 0.21/0.48  % (22480)Time elapsed: 0.053 s
% 0.21/0.48  % (22480)------------------------------
% 0.21/0.48  % (22480)------------------------------
% 0.21/0.48  % (22489)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (22493)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (22474)Success in time 0.112 s
%------------------------------------------------------------------------------
