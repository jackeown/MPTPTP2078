%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 349 expanded)
%              Number of leaves         :   14 (  96 expanded)
%              Depth                    :   21
%              Number of atoms          :  217 ( 919 expanded)
%              Number of equality atoms :   97 ( 496 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f220,plain,(
    $false ),
    inference(subsumption_resolution,[],[f219,f59])).

fof(f59,plain,(
    k2_relat_1(sK1) != k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(definition_unfolding,[],[f37,f58])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f37,plain,(
    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))
    & k1_tarski(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f23])).

fof(f23,plain,
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

fof(f15,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f219,plain,(
    k2_relat_1(sK1) = k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f218,f109])).

fof(f109,plain,(
    k1_xboole_0 != k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f108,f34])).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f108,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f106,f78])).

fof(f78,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f75,f66])).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f75,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK1),X0)
      | r2_hidden(sK0,X0) ) ),
    inference(superposition,[],[f63,f60])).

fof(f60,plain,(
    k1_relat_1(sK1) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f36,f58])).

fof(f36,plain,(
    k1_tarski(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f58])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f106,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f42,f104])).

% (6902)Refutation not found, incomplete strategy% (6902)------------------------------
% (6902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f104,plain,(
    k2_relat_1(sK1) = k11_relat_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f103,f69])).

fof(f69,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(resolution,[],[f39,f34])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f103,plain,(
    k9_relat_1(sK1,k1_relat_1(sK1)) = k11_relat_1(sK1,sK0) ),
    inference(superposition,[],[f102,f60])).

fof(f102,plain,(
    ! [X0] : k11_relat_1(sK1,X0) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) ),
    inference(resolution,[],[f61,f34])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f40,f58])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f218,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | k2_relat_1(sK1) = k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(trivial_inequality_removal,[],[f217])).

fof(f217,plain,
    ( k1_funct_1(sK1,sK0) != k1_funct_1(sK1,sK0)
    | k1_xboole_0 = k2_relat_1(sK1)
    | k2_relat_1(sK1) = k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(superposition,[],[f64,f167])).

fof(f167,plain,(
    k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) ),
    inference(trivial_inequality_removal,[],[f166])).

fof(f166,plain,
    ( k2_relat_1(sK1) != k2_relat_1(sK1)
    | k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) ),
    inference(superposition,[],[f59,f137])).

fof(f137,plain,(
    ! [X3] :
      ( k2_relat_1(sK1) = k2_enumset1(X3,X3,X3,X3)
      | k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),X3) ) ),
    inference(subsumption_resolution,[],[f136,f109])).

fof(f136,plain,(
    ! [X3] :
      ( k1_xboole_0 = k2_relat_1(sK1)
      | k2_relat_1(sK1) = k2_enumset1(X3,X3,X3,X3)
      | k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),X3) ) ),
    inference(resolution,[],[f65,f128])).

fof(f128,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | k1_funct_1(sK1,sK0) = X0 ) ),
    inference(subsumption_resolution,[],[f127,f34])).

fof(f127,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | k1_funct_1(sK1,sK0) = X0
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f124,f35])).

fof(f35,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f124,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | k1_funct_1(sK1,sK0) = X0
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f107,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f107,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK0,X0),sK1)
      | ~ r2_hidden(X0,k2_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f105,f34])).

fof(f105,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | r2_hidden(k4_tarski(sK0,X0),sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f53,f104])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f49,f58])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f50,f58])).

fof(f50,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:10:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (6894)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (6894)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (6902)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (6910)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f220,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(subsumption_resolution,[],[f219,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    k2_relat_1(sK1) != k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 0.21/0.54    inference(definition_unfolding,[],[f37,f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f38,f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f41,f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 1.33/0.55  fof(f24,plain,(
% 1.33/0.55    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.33/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f23])).
% 1.33/0.55  fof(f23,plain,(
% 1.33/0.55    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.33/0.55    introduced(choice_axiom,[])).
% 1.33/0.55  fof(f15,plain,(
% 1.33/0.55    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.33/0.55    inference(flattening,[],[f14])).
% 1.33/0.55  fof(f14,plain,(
% 1.33/0.55    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.33/0.55    inference(ennf_transformation,[],[f13])).
% 1.33/0.55  fof(f13,negated_conjecture,(
% 1.33/0.55    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.33/0.55    inference(negated_conjecture,[],[f12])).
% 1.33/0.55  fof(f12,conjecture,(
% 1.33/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 1.33/0.55  fof(f219,plain,(
% 1.33/0.55    k2_relat_1(sK1) = k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 1.33/0.55    inference(subsumption_resolution,[],[f218,f109])).
% 1.33/0.55  fof(f109,plain,(
% 1.33/0.55    k1_xboole_0 != k2_relat_1(sK1)),
% 1.33/0.55    inference(subsumption_resolution,[],[f108,f34])).
% 1.33/0.55  fof(f34,plain,(
% 1.33/0.55    v1_relat_1(sK1)),
% 1.33/0.55    inference(cnf_transformation,[],[f24])).
% 1.33/0.55  fof(f108,plain,(
% 1.33/0.55    k1_xboole_0 != k2_relat_1(sK1) | ~v1_relat_1(sK1)),
% 1.33/0.55    inference(subsumption_resolution,[],[f106,f78])).
% 1.33/0.55  fof(f78,plain,(
% 1.33/0.55    r2_hidden(sK0,k1_relat_1(sK1))),
% 1.33/0.55    inference(resolution,[],[f75,f66])).
% 1.33/0.55  fof(f66,plain,(
% 1.33/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.33/0.55    inference(equality_resolution,[],[f45])).
% 1.33/0.55  fof(f45,plain,(
% 1.33/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.33/0.55    inference(cnf_transformation,[],[f27])).
% 1.33/0.55  fof(f27,plain,(
% 1.33/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.33/0.55    inference(flattening,[],[f26])).
% 1.33/0.55  fof(f26,plain,(
% 1.33/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.33/0.55    inference(nnf_transformation,[],[f1])).
% 1.33/0.55  fof(f1,axiom,(
% 1.33/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.33/0.55  fof(f75,plain,(
% 1.33/0.55    ( ! [X0] : (~r1_tarski(k1_relat_1(sK1),X0) | r2_hidden(sK0,X0)) )),
% 1.33/0.55    inference(superposition,[],[f63,f60])).
% 1.33/0.55  fof(f60,plain,(
% 1.33/0.55    k1_relat_1(sK1) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.33/0.55    inference(definition_unfolding,[],[f36,f58])).
% 1.33/0.55  fof(f36,plain,(
% 1.33/0.55    k1_tarski(sK0) = k1_relat_1(sK1)),
% 1.33/0.55    inference(cnf_transformation,[],[f24])).
% 1.33/0.55  fof(f63,plain,(
% 1.33/0.55    ( ! [X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.33/0.55    inference(definition_unfolding,[],[f47,f58])).
% 1.33/0.55  fof(f47,plain,(
% 1.33/0.55    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f28])).
% 1.33/0.55  fof(f28,plain,(
% 1.33/0.55    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.33/0.55    inference(nnf_transformation,[],[f5])).
% 1.33/0.55  fof(f5,axiom,(
% 1.33/0.55    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.33/0.55  fof(f106,plain,(
% 1.33/0.55    k1_xboole_0 != k2_relat_1(sK1) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 1.33/0.55    inference(superposition,[],[f42,f104])).
% 1.33/0.55  % (6902)Refutation not found, incomplete strategy% (6902)------------------------------
% 1.33/0.55  % (6902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  fof(f104,plain,(
% 1.33/0.55    k2_relat_1(sK1) = k11_relat_1(sK1,sK0)),
% 1.33/0.55    inference(forward_demodulation,[],[f103,f69])).
% 1.33/0.55  fof(f69,plain,(
% 1.33/0.55    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1))),
% 1.33/0.55    inference(resolution,[],[f39,f34])).
% 1.33/0.55  fof(f39,plain,(
% 1.33/0.55    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f16])).
% 1.33/0.55  fof(f16,plain,(
% 1.33/0.55    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.33/0.55    inference(ennf_transformation,[],[f8])).
% 1.33/0.55  fof(f8,axiom,(
% 1.33/0.55    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 1.33/0.55  fof(f103,plain,(
% 1.33/0.55    k9_relat_1(sK1,k1_relat_1(sK1)) = k11_relat_1(sK1,sK0)),
% 1.33/0.55    inference(superposition,[],[f102,f60])).
% 1.33/0.55  fof(f102,plain,(
% 1.33/0.55    ( ! [X0] : (k11_relat_1(sK1,X0) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X0))) )),
% 1.33/0.55    inference(resolution,[],[f61,f34])).
% 1.33/0.55  fof(f61,plain,(
% 1.33/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 1.33/0.55    inference(definition_unfolding,[],[f40,f58])).
% 1.33/0.55  fof(f40,plain,(
% 1.33/0.55    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f17])).
% 1.33/0.55  fof(f17,plain,(
% 1.33/0.55    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 1.33/0.55    inference(ennf_transformation,[],[f7])).
% 1.33/0.55  fof(f7,axiom,(
% 1.33/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 1.33/0.55  fof(f42,plain,(
% 1.33/0.55    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f25])).
% 1.33/0.55  fof(f25,plain,(
% 1.33/0.55    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 1.33/0.55    inference(nnf_transformation,[],[f18])).
% 1.33/0.55  fof(f18,plain,(
% 1.33/0.55    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.33/0.55    inference(ennf_transformation,[],[f10])).
% 1.33/0.55  fof(f10,axiom,(
% 1.33/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 1.33/0.55  fof(f218,plain,(
% 1.33/0.55    k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 1.33/0.55    inference(trivial_inequality_removal,[],[f217])).
% 1.33/0.55  fof(f217,plain,(
% 1.33/0.55    k1_funct_1(sK1,sK0) != k1_funct_1(sK1,sK0) | k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 1.33/0.55    inference(superposition,[],[f64,f167])).
% 1.33/0.55  fof(f167,plain,(
% 1.33/0.55    k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0))),
% 1.33/0.55    inference(trivial_inequality_removal,[],[f166])).
% 1.33/0.55  fof(f166,plain,(
% 1.33/0.55    k2_relat_1(sK1) != k2_relat_1(sK1) | k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0))),
% 1.33/0.55    inference(superposition,[],[f59,f137])).
% 1.33/0.55  fof(f137,plain,(
% 1.33/0.55    ( ! [X3] : (k2_relat_1(sK1) = k2_enumset1(X3,X3,X3,X3) | k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),X3)) )),
% 1.33/0.55    inference(subsumption_resolution,[],[f136,f109])).
% 1.33/0.55  fof(f136,plain,(
% 1.33/0.55    ( ! [X3] : (k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k2_enumset1(X3,X3,X3,X3) | k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),X3)) )),
% 1.33/0.55    inference(resolution,[],[f65,f128])).
% 1.33/0.55  fof(f128,plain,(
% 1.33/0.55    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | k1_funct_1(sK1,sK0) = X0) )),
% 1.33/0.55    inference(subsumption_resolution,[],[f127,f34])).
% 1.33/0.55  fof(f127,plain,(
% 1.33/0.55    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | k1_funct_1(sK1,sK0) = X0 | ~v1_relat_1(sK1)) )),
% 1.33/0.55    inference(subsumption_resolution,[],[f124,f35])).
% 1.33/0.55  fof(f35,plain,(
% 1.33/0.55    v1_funct_1(sK1)),
% 1.33/0.55    inference(cnf_transformation,[],[f24])).
% 1.33/0.55  fof(f124,plain,(
% 1.33/0.55    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | k1_funct_1(sK1,sK0) = X0 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.33/0.55    inference(resolution,[],[f107,f55])).
% 1.33/0.55  fof(f55,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f33])).
% 1.33/0.55  fof(f33,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.33/0.55    inference(flattening,[],[f32])).
% 1.33/0.55  fof(f32,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.33/0.55    inference(nnf_transformation,[],[f22])).
% 1.33/0.55  fof(f22,plain,(
% 1.33/0.55    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.33/0.55    inference(flattening,[],[f21])).
% 1.33/0.55  fof(f21,plain,(
% 1.33/0.55    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.33/0.55    inference(ennf_transformation,[],[f11])).
% 1.33/0.55  fof(f11,axiom,(
% 1.33/0.55    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 1.33/0.55  fof(f107,plain,(
% 1.33/0.55    ( ! [X0] : (r2_hidden(k4_tarski(sK0,X0),sK1) | ~r2_hidden(X0,k2_relat_1(sK1))) )),
% 1.33/0.55    inference(subsumption_resolution,[],[f105,f34])).
% 1.33/0.55  fof(f105,plain,(
% 1.33/0.55    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | r2_hidden(k4_tarski(sK0,X0),sK1) | ~v1_relat_1(sK1)) )),
% 1.33/0.55    inference(superposition,[],[f53,f104])).
% 1.33/0.55  fof(f53,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f31])).
% 1.33/0.55  fof(f31,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 1.33/0.55    inference(nnf_transformation,[],[f20])).
% 1.33/0.55  fof(f20,plain,(
% 1.33/0.55    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 1.33/0.55    inference(ennf_transformation,[],[f9])).
% 1.33/0.55  fof(f9,axiom,(
% 1.33/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).
% 1.33/0.55  fof(f65,plain,(
% 1.33/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 1.33/0.55    inference(definition_unfolding,[],[f49,f58])).
% 1.33/0.55  fof(f49,plain,(
% 1.33/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.33/0.55    inference(cnf_transformation,[],[f30])).
% 1.33/0.55  fof(f30,plain,(
% 1.33/0.55    ! [X0,X1] : ((sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 1.33/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f29])).
% 1.33/0.55  fof(f29,plain,(
% 1.33/0.55    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)))),
% 1.33/0.55    introduced(choice_axiom,[])).
% 1.33/0.55  fof(f19,plain,(
% 1.33/0.55    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 1.33/0.55    inference(ennf_transformation,[],[f6])).
% 1.33/0.55  fof(f6,axiom,(
% 1.33/0.55    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 1.33/0.55  fof(f64,plain,(
% 1.33/0.55    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 1.33/0.55    inference(definition_unfolding,[],[f50,f58])).
% 1.33/0.55  fof(f50,plain,(
% 1.33/0.55    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.33/0.55    inference(cnf_transformation,[],[f30])).
% 1.33/0.55  % SZS output end Proof for theBenchmark
% 1.33/0.55  % (6894)------------------------------
% 1.33/0.55  % (6894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (6894)Termination reason: Refutation
% 1.33/0.55  
% 1.33/0.55  % (6894)Memory used [KB]: 10746
% 1.33/0.55  % (6894)Time elapsed: 0.113 s
% 1.33/0.55  % (6894)------------------------------
% 1.33/0.55  % (6894)------------------------------
% 1.33/0.56  % (6887)Success in time 0.19 s
%------------------------------------------------------------------------------
