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
% DateTime   : Thu Dec  3 12:51:50 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 719 expanded)
%              Number of leaves         :   16 ( 203 expanded)
%              Depth                    :   24
%              Number of atoms          :  225 (1799 expanded)
%              Number of equality atoms :  116 (1046 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f286,plain,(
    $false ),
    inference(subsumption_resolution,[],[f285,f248])).

fof(f248,plain,(
    k1_xboole_0 = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(backward_demodulation,[],[f70,f247])).

fof(f247,plain,(
    k1_xboole_0 = k1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f246,f39])).

fof(f39,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))
    & k1_tarski(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
        & k1_tarski(X0) = k1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))
      & k1_tarski(sK0) = k1_relat_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f246,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(trivial_inequality_removal,[],[f245])).

fof(f245,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f47,f213])).

fof(f213,plain,(
    k1_xboole_0 = k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f210,f69])).

fof(f69,plain,(
    k2_relat_1(sK1) != k4_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(definition_unfolding,[],[f42,f68])).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f54,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f61,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f62,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f62,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f61,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f54,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f210,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | k2_relat_1(sK1) = k4_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(trivial_inequality_removal,[],[f209])).

fof(f209,plain,
    ( k1_funct_1(sK1,sK0) != k1_funct_1(sK1,sK0)
    | k1_xboole_0 = k2_relat_1(sK1)
    | k2_relat_1(sK1) = k4_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(duplicate_literal_removal,[],[f208])).

fof(f208,plain,
    ( k1_funct_1(sK1,sK0) != k1_funct_1(sK1,sK0)
    | k1_xboole_0 = k2_relat_1(sK1)
    | k2_relat_1(sK1) = k4_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))
    | k1_xboole_0 = k2_relat_1(sK1) ),
    inference(superposition,[],[f71,f202])).

fof(f202,plain,
    ( k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0))
    | k1_xboole_0 = k2_relat_1(sK1) ),
    inference(trivial_inequality_removal,[],[f201])).

fof(f201,plain,
    ( k2_relat_1(sK1) != k2_relat_1(sK1)
    | k1_xboole_0 = k2_relat_1(sK1)
    | k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) ),
    inference(superposition,[],[f69,f120])).

fof(f120,plain,(
    ! [X2] :
      ( k2_relat_1(sK1) = k4_enumset1(X2,X2,X2,X2,X2,X2)
      | k1_xboole_0 = k2_relat_1(sK1)
      | k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),X2) ) ),
    inference(resolution,[],[f72,f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | k1_funct_1(sK1,sK0) = X0 ) ),
    inference(superposition,[],[f84,f91])).

fof(f91,plain,(
    k2_relat_1(sK1) = k11_relat_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f90,f78])).

fof(f78,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(resolution,[],[f48,f39])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f90,plain,(
    k9_relat_1(sK1,k1_relat_1(sK1)) = k11_relat_1(sK1,sK0) ),
    inference(superposition,[],[f89,f70])).

fof(f89,plain,(
    ! [X0] : k11_relat_1(sK1,X0) = k9_relat_1(sK1,k4_enumset1(X0,X0,X0,X0,X0,X0)) ),
    inference(resolution,[],[f73,f39])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k4_enumset1(X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f53,f68])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k11_relat_1(sK1,X0))
      | k1_funct_1(sK1,X0) = X1 ) ),
    inference(subsumption_resolution,[],[f81,f39])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_funct_1(sK1,X0) = X1
      | ~ r2_hidden(X1,k11_relat_1(sK1,X0))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f80,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | k1_funct_1(sK1,X0) = X1 ) ),
    inference(subsumption_resolution,[],[f79,f39])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | k1_funct_1(sK1,X0) = X1
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f44,f40])).

fof(f40,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f51,f68])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f52,f68])).

fof(f52,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f70,plain,(
    k1_relat_1(sK1) = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f41,f68])).

fof(f41,plain,(
    k1_tarski(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f285,plain,(
    k1_xboole_0 != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(backward_demodulation,[],[f215,f270])).

fof(f270,plain,(
    ! [X0] : sK0 = k1_funct_1(sK1,X0) ),
    inference(subsumption_resolution,[],[f251,f60])).

fof(f60,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f251,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k11_relat_1(sK1,X0))
      | sK0 = k1_funct_1(sK1,X0) ) ),
    inference(backward_demodulation,[],[f114,f247])).

fof(f114,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK1),k11_relat_1(sK1,X0))
      | sK0 = k1_funct_1(sK1,X0) ) ),
    inference(superposition,[],[f86,f70])).

fof(f86,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(k4_enumset1(X3,X3,X3,X3,X3,X4),k11_relat_1(sK1,X2))
      | k1_funct_1(sK1,X2) = X3 ) ),
    inference(resolution,[],[f84,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f55,f67])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f215,plain,(
    k1_xboole_0 != k4_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(backward_demodulation,[],[f69,f213])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : run_vampire %s %d
% 0.08/0.27  % Computer   : n020.cluster.edu
% 0.08/0.27  % Model      : x86_64 x86_64
% 0.08/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.27  % Memory     : 8042.1875MB
% 0.08/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.27  % CPULimit   : 60
% 0.08/0.27  % WCLimit    : 600
% 0.08/0.27  % DateTime   : Tue Dec  1 14:22:07 EST 2020
% 0.08/0.27  % CPUTime    : 
% 0.13/0.35  % (7946)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.13/0.36  % (7946)Refutation found. Thanks to Tanya!
% 0.13/0.36  % SZS status Theorem for theBenchmark
% 0.13/0.36  % (7972)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.13/0.38  % SZS output start Proof for theBenchmark
% 0.13/0.38  fof(f286,plain,(
% 0.13/0.38    $false),
% 0.13/0.38    inference(subsumption_resolution,[],[f285,f248])).
% 0.13/0.38  fof(f248,plain,(
% 0.13/0.38    k1_xboole_0 = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.13/0.38    inference(backward_demodulation,[],[f70,f247])).
% 0.13/0.38  fof(f247,plain,(
% 0.13/0.38    k1_xboole_0 = k1_relat_1(sK1)),
% 0.13/0.38    inference(subsumption_resolution,[],[f246,f39])).
% 0.13/0.38  fof(f39,plain,(
% 0.13/0.38    v1_relat_1(sK1)),
% 0.13/0.38    inference(cnf_transformation,[],[f29])).
% 0.13/0.38  fof(f29,plain,(
% 0.13/0.38    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.13/0.38    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f28])).
% 0.13/0.38  fof(f28,plain,(
% 0.13/0.38    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.13/0.38    introduced(choice_axiom,[])).
% 0.13/0.38  fof(f19,plain,(
% 0.13/0.38    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.13/0.38    inference(flattening,[],[f18])).
% 0.13/0.38  fof(f18,plain,(
% 0.13/0.38    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.13/0.38    inference(ennf_transformation,[],[f17])).
% 0.13/0.38  fof(f17,negated_conjecture,(
% 0.13/0.38    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.13/0.38    inference(negated_conjecture,[],[f16])).
% 0.13/0.38  fof(f16,conjecture,(
% 0.13/0.38    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.13/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 0.13/0.38  fof(f246,plain,(
% 0.13/0.38    k1_xboole_0 = k1_relat_1(sK1) | ~v1_relat_1(sK1)),
% 0.13/0.38    inference(trivial_inequality_removal,[],[f245])).
% 0.13/0.38  fof(f245,plain,(
% 0.13/0.38    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k1_relat_1(sK1) | ~v1_relat_1(sK1)),
% 0.13/0.38    inference(superposition,[],[f47,f213])).
% 0.13/0.38  fof(f213,plain,(
% 0.13/0.38    k1_xboole_0 = k2_relat_1(sK1)),
% 0.13/0.38    inference(subsumption_resolution,[],[f210,f69])).
% 0.13/0.38  fof(f69,plain,(
% 0.13/0.38    k2_relat_1(sK1) != k4_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 0.13/0.38    inference(definition_unfolding,[],[f42,f68])).
% 0.13/0.38  fof(f68,plain,(
% 0.13/0.38    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 0.13/0.38    inference(definition_unfolding,[],[f54,f67])).
% 0.13/0.38  fof(f67,plain,(
% 0.13/0.38    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.13/0.38    inference(definition_unfolding,[],[f61,f66])).
% 0.13/0.38  fof(f66,plain,(
% 0.13/0.38    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.13/0.38    inference(definition_unfolding,[],[f62,f65])).
% 0.13/0.38  fof(f65,plain,(
% 0.13/0.38    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.13/0.38    inference(definition_unfolding,[],[f63,f64])).
% 0.13/0.38  fof(f64,plain,(
% 0.13/0.38    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.13/0.38    inference(cnf_transformation,[],[f6])).
% 0.13/0.38  fof(f6,axiom,(
% 0.13/0.38    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.13/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.13/0.38  fof(f63,plain,(
% 0.13/0.38    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.13/0.38    inference(cnf_transformation,[],[f5])).
% 0.13/0.38  fof(f5,axiom,(
% 0.13/0.38    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.13/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.13/0.38  fof(f62,plain,(
% 0.13/0.38    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.13/0.38    inference(cnf_transformation,[],[f4])).
% 0.13/0.38  fof(f4,axiom,(
% 0.13/0.38    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.13/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.13/0.38  fof(f61,plain,(
% 0.13/0.38    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.13/0.38    inference(cnf_transformation,[],[f3])).
% 0.13/0.38  fof(f3,axiom,(
% 0.13/0.38    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.13/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.13/0.38  fof(f54,plain,(
% 0.13/0.38    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.13/0.38    inference(cnf_transformation,[],[f2])).
% 0.13/0.38  fof(f2,axiom,(
% 0.13/0.38    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.13/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.13/0.38  fof(f42,plain,(
% 0.13/0.38    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))),
% 0.13/0.38    inference(cnf_transformation,[],[f29])).
% 0.13/0.38  fof(f210,plain,(
% 0.13/0.38    k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k4_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 0.13/0.38    inference(trivial_inequality_removal,[],[f209])).
% 0.13/0.38  fof(f209,plain,(
% 0.13/0.38    k1_funct_1(sK1,sK0) != k1_funct_1(sK1,sK0) | k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k4_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 0.13/0.38    inference(duplicate_literal_removal,[],[f208])).
% 0.13/0.38  fof(f208,plain,(
% 0.13/0.38    k1_funct_1(sK1,sK0) != k1_funct_1(sK1,sK0) | k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k4_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) | k1_xboole_0 = k2_relat_1(sK1)),
% 0.13/0.38    inference(superposition,[],[f71,f202])).
% 0.13/0.38  fof(f202,plain,(
% 0.13/0.38    k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) | k1_xboole_0 = k2_relat_1(sK1)),
% 0.13/0.38    inference(trivial_inequality_removal,[],[f201])).
% 0.13/0.38  fof(f201,plain,(
% 0.13/0.38    k2_relat_1(sK1) != k2_relat_1(sK1) | k1_xboole_0 = k2_relat_1(sK1) | k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0))),
% 0.13/0.38    inference(superposition,[],[f69,f120])).
% 0.13/0.38  fof(f120,plain,(
% 0.13/0.38    ( ! [X2] : (k2_relat_1(sK1) = k4_enumset1(X2,X2,X2,X2,X2,X2) | k1_xboole_0 = k2_relat_1(sK1) | k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),X2)) )),
% 0.13/0.38    inference(resolution,[],[f72,f92])).
% 0.13/0.38  fof(f92,plain,(
% 0.13/0.38    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | k1_funct_1(sK1,sK0) = X0) )),
% 0.13/0.38    inference(superposition,[],[f84,f91])).
% 0.13/0.38  fof(f91,plain,(
% 0.13/0.38    k2_relat_1(sK1) = k11_relat_1(sK1,sK0)),
% 0.13/0.38    inference(forward_demodulation,[],[f90,f78])).
% 0.13/0.38  fof(f78,plain,(
% 0.13/0.38    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1))),
% 0.13/0.38    inference(resolution,[],[f48,f39])).
% 0.13/0.38  fof(f48,plain,(
% 0.13/0.38    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.13/0.38    inference(cnf_transformation,[],[f23])).
% 0.13/0.38  fof(f23,plain,(
% 0.13/0.38    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.13/0.38    inference(ennf_transformation,[],[f11])).
% 0.13/0.38  fof(f11,axiom,(
% 0.13/0.38    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.13/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.13/0.38  fof(f90,plain,(
% 0.13/0.38    k9_relat_1(sK1,k1_relat_1(sK1)) = k11_relat_1(sK1,sK0)),
% 0.13/0.38    inference(superposition,[],[f89,f70])).
% 0.13/0.38  fof(f89,plain,(
% 0.13/0.38    ( ! [X0] : (k11_relat_1(sK1,X0) = k9_relat_1(sK1,k4_enumset1(X0,X0,X0,X0,X0,X0))) )),
% 0.13/0.38    inference(resolution,[],[f73,f39])).
% 0.13/0.38  fof(f73,plain,(
% 0.13/0.38    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k4_enumset1(X1,X1,X1,X1,X1,X1))) )),
% 0.13/0.38    inference(definition_unfolding,[],[f53,f68])).
% 0.13/0.38  fof(f53,plain,(
% 0.13/0.38    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 0.13/0.38    inference(cnf_transformation,[],[f26])).
% 0.13/0.38  fof(f26,plain,(
% 0.13/0.38    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.13/0.38    inference(ennf_transformation,[],[f10])).
% 0.13/0.38  fof(f10,axiom,(
% 0.13/0.38    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.13/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 0.13/0.38  fof(f84,plain,(
% 0.13/0.38    ( ! [X0,X1] : (~r2_hidden(X1,k11_relat_1(sK1,X0)) | k1_funct_1(sK1,X0) = X1) )),
% 0.13/0.38    inference(subsumption_resolution,[],[f81,f39])).
% 0.13/0.38  fof(f81,plain,(
% 0.13/0.38    ( ! [X0,X1] : (k1_funct_1(sK1,X0) = X1 | ~r2_hidden(X1,k11_relat_1(sK1,X0)) | ~v1_relat_1(sK1)) )),
% 0.13/0.38    inference(resolution,[],[f80,f59])).
% 0.13/0.38  fof(f59,plain,(
% 0.13/0.38    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 0.13/0.38    inference(cnf_transformation,[],[f38])).
% 0.13/0.38  fof(f38,plain,(
% 0.13/0.38    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 0.13/0.38    inference(nnf_transformation,[],[f27])).
% 0.13/0.38  fof(f27,plain,(
% 0.13/0.38    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.13/0.38    inference(ennf_transformation,[],[f12])).
% 0.13/0.38  fof(f12,axiom,(
% 0.13/0.38    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.13/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).
% 0.13/0.38  fof(f80,plain,(
% 0.13/0.38    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | k1_funct_1(sK1,X0) = X1) )),
% 0.13/0.38    inference(subsumption_resolution,[],[f79,f39])).
% 0.13/0.38  fof(f79,plain,(
% 0.13/0.38    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | k1_funct_1(sK1,X0) = X1 | ~v1_relat_1(sK1)) )),
% 0.13/0.38    inference(resolution,[],[f44,f40])).
% 0.13/0.38  fof(f40,plain,(
% 0.13/0.38    v1_funct_1(sK1)),
% 0.13/0.38    inference(cnf_transformation,[],[f29])).
% 0.13/0.38  fof(f44,plain,(
% 0.13/0.38    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.13/0.38    inference(cnf_transformation,[],[f31])).
% 0.13/0.38  fof(f31,plain,(
% 0.13/0.38    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.13/0.38    inference(flattening,[],[f30])).
% 0.13/0.38  fof(f30,plain,(
% 0.13/0.38    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.13/0.38    inference(nnf_transformation,[],[f21])).
% 0.13/0.38  fof(f21,plain,(
% 0.13/0.38    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.13/0.38    inference(flattening,[],[f20])).
% 0.13/0.38  fof(f20,plain,(
% 0.13/0.38    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.13/0.38    inference(ennf_transformation,[],[f15])).
% 0.13/0.38  fof(f15,axiom,(
% 0.13/0.38    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.13/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.13/0.38  fof(f72,plain,(
% 0.13/0.38    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0) )),
% 0.13/0.38    inference(definition_unfolding,[],[f51,f68])).
% 0.13/0.38  fof(f51,plain,(
% 0.13/0.38    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.13/0.38    inference(cnf_transformation,[],[f35])).
% 0.13/0.38  fof(f35,plain,(
% 0.13/0.38    ! [X0,X1] : ((sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.13/0.38    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f34])).
% 0.13/0.38  fof(f34,plain,(
% 0.13/0.38    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)))),
% 0.13/0.38    introduced(choice_axiom,[])).
% 0.13/0.38  fof(f25,plain,(
% 0.13/0.38    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.13/0.38    inference(ennf_transformation,[],[f9])).
% 0.13/0.38  fof(f9,axiom,(
% 0.13/0.38    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.13/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 0.13/0.38  fof(f71,plain,(
% 0.13/0.38    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0) )),
% 0.13/0.38    inference(definition_unfolding,[],[f52,f68])).
% 0.13/0.38  fof(f52,plain,(
% 0.13/0.38    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.13/0.38    inference(cnf_transformation,[],[f35])).
% 0.13/0.38  fof(f47,plain,(
% 0.13/0.38    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.13/0.38    inference(cnf_transformation,[],[f32])).
% 0.13/0.38  fof(f32,plain,(
% 0.13/0.38    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.13/0.38    inference(nnf_transformation,[],[f22])).
% 0.13/0.38  fof(f22,plain,(
% 0.13/0.38    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.13/0.38    inference(ennf_transformation,[],[f14])).
% 0.13/0.38  fof(f14,axiom,(
% 0.13/0.38    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.13/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.13/0.38  fof(f70,plain,(
% 0.13/0.38    k1_relat_1(sK1) = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.13/0.38    inference(definition_unfolding,[],[f41,f68])).
% 0.13/0.38  fof(f41,plain,(
% 0.13/0.38    k1_tarski(sK0) = k1_relat_1(sK1)),
% 0.13/0.38    inference(cnf_transformation,[],[f29])).
% 0.13/0.38  fof(f285,plain,(
% 0.13/0.38    k1_xboole_0 != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.13/0.38    inference(backward_demodulation,[],[f215,f270])).
% 0.13/0.38  fof(f270,plain,(
% 0.13/0.38    ( ! [X0] : (sK0 = k1_funct_1(sK1,X0)) )),
% 0.13/0.38    inference(subsumption_resolution,[],[f251,f60])).
% 0.13/0.38  fof(f60,plain,(
% 0.13/0.38    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.13/0.38    inference(cnf_transformation,[],[f1])).
% 0.13/0.38  fof(f1,axiom,(
% 0.13/0.38    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.13/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.13/0.38  fof(f251,plain,(
% 0.13/0.38    ( ! [X0] : (~r1_tarski(k1_xboole_0,k11_relat_1(sK1,X0)) | sK0 = k1_funct_1(sK1,X0)) )),
% 0.13/0.38    inference(backward_demodulation,[],[f114,f247])).
% 0.13/0.38  fof(f114,plain,(
% 0.13/0.38    ( ! [X0] : (~r1_tarski(k1_relat_1(sK1),k11_relat_1(sK1,X0)) | sK0 = k1_funct_1(sK1,X0)) )),
% 0.13/0.38    inference(superposition,[],[f86,f70])).
% 0.13/0.38  fof(f86,plain,(
% 0.13/0.38    ( ! [X4,X2,X3] : (~r1_tarski(k4_enumset1(X3,X3,X3,X3,X3,X4),k11_relat_1(sK1,X2)) | k1_funct_1(sK1,X2) = X3) )),
% 0.13/0.38    inference(resolution,[],[f84,f76])).
% 0.13/0.38  fof(f76,plain,(
% 0.13/0.38    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)) )),
% 0.13/0.38    inference(definition_unfolding,[],[f55,f67])).
% 0.13/0.38  fof(f55,plain,(
% 0.13/0.38    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.13/0.38    inference(cnf_transformation,[],[f37])).
% 0.13/0.38  fof(f37,plain,(
% 0.13/0.38    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.13/0.38    inference(flattening,[],[f36])).
% 0.13/0.38  fof(f36,plain,(
% 0.13/0.38    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.13/0.38    inference(nnf_transformation,[],[f8])).
% 0.13/0.38  fof(f8,axiom,(
% 0.13/0.38    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.13/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.13/0.38  fof(f215,plain,(
% 0.13/0.38    k1_xboole_0 != k4_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 0.13/0.38    inference(backward_demodulation,[],[f69,f213])).
% 0.13/0.38  % SZS output end Proof for theBenchmark
% 0.13/0.38  % (7946)------------------------------
% 0.13/0.38  % (7946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.38  % (7946)Termination reason: Refutation
% 0.13/0.38  
% 0.13/0.38  % (7946)Memory used [KB]: 6524
% 0.13/0.38  % (7946)Time elapsed: 0.051 s
% 0.13/0.38  % (7946)------------------------------
% 0.13/0.38  % (7946)------------------------------
% 0.13/0.38  % (7937)Success in time 0.1 s
%------------------------------------------------------------------------------
