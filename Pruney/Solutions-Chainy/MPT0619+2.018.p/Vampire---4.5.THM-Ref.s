%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:48 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 704 expanded)
%              Number of leaves         :   12 ( 191 expanded)
%              Depth                    :   19
%              Number of atoms          :  305 (2224 expanded)
%              Number of equality atoms :  107 (1085 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (17874)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f234,plain,(
    $false ),
    inference(subsumption_resolution,[],[f233,f185])).

fof(f185,plain,(
    r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f181,f98])).

fof(f98,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f92,f97])).

fof(f97,plain,(
    k2_relat_1(sK1) = k11_relat_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f94,f37])).

fof(f37,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))
    & k1_tarski(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f22])).

% (17865)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% (17860)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
fof(f22,plain,
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

fof(f14,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f94,plain,
    ( k2_relat_1(sK1) = k11_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f92,f42])).

fof(f42,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f92,plain,(
    k9_relat_1(sK1,k1_relat_1(sK1)) = k11_relat_1(sK1,sK0) ),
    inference(superposition,[],[f87,f64])).

fof(f64,plain,(
    k1_relat_1(sK1) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f39,f62])).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    k1_tarski(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f87,plain,(
    ! [X0] : k11_relat_1(sK1,X0) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) ),
    inference(resolution,[],[f65,f37])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f43,f62])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f181,plain,(
    r2_hidden(k1_funct_1(sK1,sK0),k9_relat_1(sK1,k1_relat_1(sK1))) ),
    inference(resolution,[],[f172,f76])).

fof(f76,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(superposition,[],[f73,f64])).

fof(f73,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f48,f62])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f172,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK0,X2)
      | r2_hidden(k1_funct_1(sK1,sK0),k9_relat_1(sK1,X2)) ) ),
    inference(resolution,[],[f140,f76])).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | r2_hidden(k1_funct_1(sK1,X0),k9_relat_1(sK1,X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f134,f117])).

fof(f117,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f116,f37])).

fof(f116,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f75,f38])).

fof(f38,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f75,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X2),sK1)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X2,k9_relat_1(sK1,X1)) ) ),
    inference(subsumption_resolution,[],[f133,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f83,f37])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f58,f38])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(k4_tarski(X0,X2),sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | r2_hidden(X2,k9_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f57,f37])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
            & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
        & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f233,plain,(
    ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f232,f63])).

fof(f63,plain,(
    k2_relat_1(sK1) != k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(definition_unfolding,[],[f40,f62])).

fof(f40,plain,(
    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f232,plain,
    ( k2_relat_1(sK1) = k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))
    | ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) ),
    inference(trivial_inequality_removal,[],[f231])).

fof(f231,plain,
    ( k1_funct_1(sK1,sK0) != k1_funct_1(sK1,sK0)
    | k2_relat_1(sK1) = k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))
    | ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) ),
    inference(superposition,[],[f66,f201])).

fof(f201,plain,(
    k1_funct_1(sK1,sK0) = sK2(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) ),
    inference(resolution,[],[f196,f131])).

fof(f131,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_relat_1(sK1))
      | k1_funct_1(sK1,sK0) = X2 ) ),
    inference(superposition,[],[f124,f98])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(sK1,X1))
      | k1_funct_1(sK1,sK0) = X0 ) ),
    inference(resolution,[],[f123,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | k1_funct_1(sK1,X0) = X1 ) ),
    inference(subsumption_resolution,[],[f100,f37])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | k1_funct_1(sK1,X0) = X1
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f59,f38])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f123,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK0,X0),sK1)
      | ~ r2_hidden(X0,k9_relat_1(sK1,X1)) ) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK0,X0),sK1)
      | ~ r2_hidden(X0,k9_relat_1(sK1,X1))
      | ~ r2_hidden(X0,k9_relat_1(sK1,X1)) ) ),
    inference(superposition,[],[f107,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( sK0 = sK4(X0,X1,sK1)
      | ~ r2_hidden(X0,k9_relat_1(sK1,X1)) ) ),
    inference(subsumption_resolution,[],[f90,f37])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(sK1,X1))
      | ~ v1_relat_1(sK1)
      | sK0 = sK4(X0,X1,sK1) ) ),
    inference(resolution,[],[f54,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | sK0 = X0 ) ),
    inference(superposition,[],[f74,f64])).

fof(f74,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f47,f62])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1,sK1),X0),sK1)
      | ~ r2_hidden(X0,k9_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f55,f37])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f196,plain,(
    r2_hidden(sK2(k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f195,f63])).

fof(f195,plain,
    ( k2_relat_1(sK1) = k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))
    | r2_hidden(sK2(k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) ),
    inference(resolution,[],[f185,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_enumset1(X0,X0,X0,X0) = X1
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(trivial_inequality_removal,[],[f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( X0 != X0
      | k2_enumset1(X0,X0,X0,X0) = X1
      | ~ r2_hidden(X0,X1)
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( X0 != X0
      | k2_enumset1(X0,X0,X0,X0) = X1
      | ~ r2_hidden(X0,X1)
      | k2_enumset1(X0,X0,X0,X0) = X1
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(superposition,[],[f66,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) = X0
      | k2_enumset1(X0,X0,X0,X0) = X1
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f49,f62])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK2(X0,X1) = X0
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X0
      | k2_enumset1(X0,X0,X0,X0) = X1
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f50,f62])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK2(X0,X1) != X0
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 18:55:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.52  % (17880)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.52  % (17871)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.21/0.53  % (17859)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.21/0.53  % (17882)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.21/0.53  % (17861)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.21/0.53  % (17863)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.21/0.54  % (17884)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.21/0.54  % (17878)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.21/0.54  % (17867)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.32/0.54  % (17869)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.32/0.54  % (17857)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.32/0.55  % (17856)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.32/0.55  % (17886)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.32/0.55  % (17858)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.32/0.55  % (17880)Refutation found. Thanks to Tanya!
% 1.32/0.55  % SZS status Theorem for theBenchmark
% 1.32/0.55  % SZS output start Proof for theBenchmark
% 1.32/0.55  % (17874)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.32/0.55  fof(f234,plain,(
% 1.32/0.55    $false),
% 1.32/0.55    inference(subsumption_resolution,[],[f233,f185])).
% 1.32/0.55  fof(f185,plain,(
% 1.32/0.55    r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))),
% 1.32/0.55    inference(forward_demodulation,[],[f181,f98])).
% 1.32/0.55  fof(f98,plain,(
% 1.32/0.55    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1))),
% 1.32/0.55    inference(backward_demodulation,[],[f92,f97])).
% 1.32/0.55  fof(f97,plain,(
% 1.32/0.55    k2_relat_1(sK1) = k11_relat_1(sK1,sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f94,f37])).
% 1.32/0.55  fof(f37,plain,(
% 1.32/0.55    v1_relat_1(sK1)),
% 1.32/0.55    inference(cnf_transformation,[],[f23])).
% 1.32/0.55  fof(f23,plain,(
% 1.32/0.55    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.32/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f22])).
% 1.32/0.55  % (17865)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.32/0.55  % (17860)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.32/0.55  fof(f22,plain,(
% 1.32/0.55    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f14,plain,(
% 1.32/0.55    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.32/0.55    inference(flattening,[],[f13])).
% 1.32/0.55  fof(f13,plain,(
% 1.32/0.55    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.32/0.55    inference(ennf_transformation,[],[f12])).
% 1.32/0.55  fof(f12,negated_conjecture,(
% 1.32/0.55    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.32/0.55    inference(negated_conjecture,[],[f11])).
% 1.32/0.55  fof(f11,conjecture,(
% 1.32/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 1.32/0.55  fof(f94,plain,(
% 1.32/0.55    k2_relat_1(sK1) = k11_relat_1(sK1,sK0) | ~v1_relat_1(sK1)),
% 1.32/0.55    inference(superposition,[],[f92,f42])).
% 1.32/0.55  fof(f42,plain,(
% 1.32/0.55    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f15])).
% 1.32/0.55  fof(f15,plain,(
% 1.32/0.55    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.32/0.55    inference(ennf_transformation,[],[f8])).
% 1.32/0.55  fof(f8,axiom,(
% 1.32/0.55    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 1.32/0.55  fof(f92,plain,(
% 1.32/0.55    k9_relat_1(sK1,k1_relat_1(sK1)) = k11_relat_1(sK1,sK0)),
% 1.32/0.55    inference(superposition,[],[f87,f64])).
% 1.32/0.55  fof(f64,plain,(
% 1.32/0.55    k1_relat_1(sK1) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.32/0.55    inference(definition_unfolding,[],[f39,f62])).
% 1.32/0.55  fof(f62,plain,(
% 1.32/0.55    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.32/0.55    inference(definition_unfolding,[],[f41,f61])).
% 1.32/0.55  fof(f61,plain,(
% 1.32/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.32/0.55    inference(definition_unfolding,[],[f44,f53])).
% 1.32/0.55  fof(f53,plain,(
% 1.32/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f4])).
% 1.32/0.55  fof(f4,axiom,(
% 1.32/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.32/0.55  fof(f44,plain,(
% 1.32/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f3])).
% 1.32/0.55  fof(f3,axiom,(
% 1.32/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.32/0.55  fof(f41,plain,(
% 1.32/0.55    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f2])).
% 1.32/0.55  fof(f2,axiom,(
% 1.32/0.55    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.32/0.55  fof(f39,plain,(
% 1.32/0.55    k1_tarski(sK0) = k1_relat_1(sK1)),
% 1.32/0.55    inference(cnf_transformation,[],[f23])).
% 1.32/0.55  fof(f87,plain,(
% 1.32/0.55    ( ! [X0] : (k11_relat_1(sK1,X0) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X0))) )),
% 1.32/0.55    inference(resolution,[],[f65,f37])).
% 1.32/0.55  fof(f65,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 1.32/0.55    inference(definition_unfolding,[],[f43,f62])).
% 1.32/0.55  fof(f43,plain,(
% 1.32/0.55    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f16])).
% 1.32/0.55  fof(f16,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 1.32/0.55    inference(ennf_transformation,[],[f6])).
% 1.32/0.55  fof(f6,axiom,(
% 1.32/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 1.32/0.55  fof(f181,plain,(
% 1.32/0.55    r2_hidden(k1_funct_1(sK1,sK0),k9_relat_1(sK1,k1_relat_1(sK1)))),
% 1.32/0.55    inference(resolution,[],[f172,f76])).
% 1.32/0.55  fof(f76,plain,(
% 1.32/0.55    r2_hidden(sK0,k1_relat_1(sK1))),
% 1.32/0.55    inference(superposition,[],[f73,f64])).
% 1.32/0.55  fof(f73,plain,(
% 1.32/0.55    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 1.32/0.55    inference(equality_resolution,[],[f72])).
% 1.32/0.55  fof(f72,plain,(
% 1.32/0.55    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 1.32/0.55    inference(equality_resolution,[],[f68])).
% 1.32/0.55  fof(f68,plain,(
% 1.32/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.32/0.55    inference(definition_unfolding,[],[f48,f62])).
% 1.32/0.55  fof(f48,plain,(
% 1.32/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.32/0.55    inference(cnf_transformation,[],[f28])).
% 1.32/0.55  fof(f28,plain,(
% 1.32/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.32/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).
% 1.32/0.55  fof(f27,plain,(
% 1.32/0.55    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f26,plain,(
% 1.32/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.32/0.55    inference(rectify,[],[f25])).
% 1.32/0.55  fof(f25,plain,(
% 1.32/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.32/0.55    inference(nnf_transformation,[],[f1])).
% 1.32/0.55  fof(f1,axiom,(
% 1.32/0.55    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.32/0.55  fof(f172,plain,(
% 1.32/0.55    ( ! [X2] : (~r2_hidden(sK0,X2) | r2_hidden(k1_funct_1(sK1,sK0),k9_relat_1(sK1,X2))) )),
% 1.32/0.55    inference(resolution,[],[f140,f76])).
% 1.32/0.55  fof(f140,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k1_funct_1(sK1,X0),k9_relat_1(sK1,X1)) | ~r2_hidden(X0,X1)) )),
% 1.32/0.55    inference(resolution,[],[f134,f117])).
% 1.32/0.55  fof(f117,plain,(
% 1.32/0.55    ( ! [X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) | ~r2_hidden(X0,k1_relat_1(sK1))) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f116,f37])).
% 1.32/0.55  fof(f116,plain,(
% 1.32/0.55    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) | ~v1_relat_1(sK1)) )),
% 1.32/0.55    inference(resolution,[],[f75,f38])).
% 1.32/0.55  fof(f38,plain,(
% 1.32/0.55    v1_funct_1(sK1)),
% 1.32/0.55    inference(cnf_transformation,[],[f23])).
% 1.32/0.55  fof(f75,plain,(
% 1.32/0.55    ( ! [X2,X0] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~v1_relat_1(X2)) )),
% 1.32/0.55    inference(equality_resolution,[],[f60])).
% 1.32/0.55  fof(f60,plain,(
% 1.32/0.55    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f36])).
% 1.32/0.55  fof(f36,plain,(
% 1.32/0.55    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.32/0.55    inference(flattening,[],[f35])).
% 1.32/0.55  fof(f35,plain,(
% 1.32/0.55    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.32/0.55    inference(nnf_transformation,[],[f21])).
% 1.32/0.55  fof(f21,plain,(
% 1.32/0.55    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.32/0.55    inference(flattening,[],[f20])).
% 1.32/0.55  fof(f20,plain,(
% 1.32/0.55    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.32/0.55    inference(ennf_transformation,[],[f10])).
% 1.32/0.55  fof(f10,axiom,(
% 1.32/0.55    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 1.32/0.55  fof(f134,plain,(
% 1.32/0.55    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X2),sK1) | ~r2_hidden(X0,X1) | r2_hidden(X2,k9_relat_1(sK1,X1))) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f133,f84])).
% 1.32/0.55  fof(f84,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | r2_hidden(X0,k1_relat_1(sK1))) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f83,f37])).
% 1.32/0.55  fof(f83,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 1.32/0.55    inference(resolution,[],[f58,f38])).
% 1.32/0.55  fof(f58,plain,(
% 1.32/0.55    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f36])).
% 1.32/0.55  fof(f133,plain,(
% 1.32/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(k4_tarski(X0,X2),sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(X2,k9_relat_1(sK1,X1))) )),
% 1.32/0.55    inference(resolution,[],[f57,f37])).
% 1.32/0.55  fof(f57,plain,(
% 1.32/0.55    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)) | r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 1.32/0.55    inference(cnf_transformation,[],[f34])).
% 1.32/0.55  fof(f34,plain,(
% 1.32/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.32/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).
% 1.32/0.55  fof(f33,plain,(
% 1.32/0.55    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))))),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f32,plain,(
% 1.32/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.32/0.55    inference(rectify,[],[f31])).
% 1.32/0.55  fof(f31,plain,(
% 1.32/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.32/0.55    inference(nnf_transformation,[],[f19])).
% 1.32/0.55  fof(f19,plain,(
% 1.32/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.32/0.55    inference(ennf_transformation,[],[f7])).
% 1.32/0.55  fof(f7,axiom,(
% 1.32/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 1.32/0.55  fof(f233,plain,(
% 1.32/0.55    ~r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))),
% 1.32/0.55    inference(subsumption_resolution,[],[f232,f63])).
% 1.32/0.55  fof(f63,plain,(
% 1.32/0.55    k2_relat_1(sK1) != k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 1.32/0.55    inference(definition_unfolding,[],[f40,f62])).
% 1.32/0.55  fof(f40,plain,(
% 1.32/0.55    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))),
% 1.32/0.55    inference(cnf_transformation,[],[f23])).
% 1.32/0.55  fof(f232,plain,(
% 1.32/0.55    k2_relat_1(sK1) = k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) | ~r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))),
% 1.32/0.55    inference(trivial_inequality_removal,[],[f231])).
% 1.32/0.55  fof(f231,plain,(
% 1.32/0.55    k1_funct_1(sK1,sK0) != k1_funct_1(sK1,sK0) | k2_relat_1(sK1) = k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) | ~r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))),
% 1.32/0.55    inference(superposition,[],[f66,f201])).
% 1.32/0.55  fof(f201,plain,(
% 1.32/0.55    k1_funct_1(sK1,sK0) = sK2(k1_funct_1(sK1,sK0),k2_relat_1(sK1))),
% 1.32/0.55    inference(resolution,[],[f196,f131])).
% 1.32/0.55  fof(f131,plain,(
% 1.32/0.55    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(sK1)) | k1_funct_1(sK1,sK0) = X2) )),
% 1.32/0.55    inference(superposition,[],[f124,f98])).
% 1.32/0.55  fof(f124,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK1,X1)) | k1_funct_1(sK1,sK0) = X0) )),
% 1.32/0.55    inference(resolution,[],[f123,f101])).
% 1.32/0.55  fof(f101,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | k1_funct_1(sK1,X0) = X1) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f100,f37])).
% 1.32/0.55  fof(f100,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | k1_funct_1(sK1,X0) = X1 | ~v1_relat_1(sK1)) )),
% 1.32/0.55    inference(resolution,[],[f59,f38])).
% 1.32/0.55  fof(f59,plain,(
% 1.32/0.55    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f36])).
% 1.32/0.55  fof(f123,plain,(
% 1.32/0.55    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK0,X0),sK1) | ~r2_hidden(X0,k9_relat_1(sK1,X1))) )),
% 1.32/0.55    inference(duplicate_literal_removal,[],[f122])).
% 1.32/0.55  fof(f122,plain,(
% 1.32/0.55    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK0,X0),sK1) | ~r2_hidden(X0,k9_relat_1(sK1,X1)) | ~r2_hidden(X0,k9_relat_1(sK1,X1))) )),
% 1.32/0.55    inference(superposition,[],[f107,f91])).
% 1.32/0.55  fof(f91,plain,(
% 1.32/0.55    ( ! [X0,X1] : (sK0 = sK4(X0,X1,sK1) | ~r2_hidden(X0,k9_relat_1(sK1,X1))) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f90,f37])).
% 1.32/0.55  fof(f90,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK1,X1)) | ~v1_relat_1(sK1) | sK0 = sK4(X0,X1,sK1)) )),
% 1.32/0.55    inference(resolution,[],[f54,f78])).
% 1.32/0.55  fof(f78,plain,(
% 1.32/0.55    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | sK0 = X0) )),
% 1.32/0.55    inference(superposition,[],[f74,f64])).
% 1.32/0.55  fof(f74,plain,(
% 1.32/0.55    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 1.32/0.55    inference(equality_resolution,[],[f69])).
% 1.32/0.55  fof(f69,plain,(
% 1.32/0.55    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.32/0.55    inference(definition_unfolding,[],[f47,f62])).
% 1.32/0.55  fof(f47,plain,(
% 1.32/0.55    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.32/0.55    inference(cnf_transformation,[],[f28])).
% 1.32/0.55  fof(f54,plain,(
% 1.32/0.55    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f34])).
% 1.32/0.55  fof(f107,plain,(
% 1.32/0.55    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1,sK1),X0),sK1) | ~r2_hidden(X0,k9_relat_1(sK1,X1))) )),
% 1.32/0.55    inference(resolution,[],[f55,f37])).
% 1.32/0.55  fof(f55,plain,(
% 1.32/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f34])).
% 1.32/0.55  fof(f196,plain,(
% 1.32/0.55    r2_hidden(sK2(k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1))),
% 1.32/0.55    inference(subsumption_resolution,[],[f195,f63])).
% 1.32/0.55  fof(f195,plain,(
% 1.32/0.55    k2_relat_1(sK1) = k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) | r2_hidden(sK2(k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1))),
% 1.32/0.55    inference(resolution,[],[f185,f128])).
% 1.32/0.55  fof(f128,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_enumset1(X0,X0,X0,X0) = X1 | r2_hidden(sK2(X0,X1),X1)) )),
% 1.32/0.55    inference(trivial_inequality_removal,[],[f127])).
% 1.32/0.55  fof(f127,plain,(
% 1.32/0.55    ( ! [X0,X1] : (X0 != X0 | k2_enumset1(X0,X0,X0,X0) = X1 | ~r2_hidden(X0,X1) | r2_hidden(sK2(X0,X1),X1)) )),
% 1.32/0.55    inference(duplicate_literal_removal,[],[f126])).
% 1.32/0.55  fof(f126,plain,(
% 1.32/0.55    ( ! [X0,X1] : (X0 != X0 | k2_enumset1(X0,X0,X0,X0) = X1 | ~r2_hidden(X0,X1) | k2_enumset1(X0,X0,X0,X0) = X1 | r2_hidden(sK2(X0,X1),X1)) )),
% 1.32/0.55    inference(superposition,[],[f66,f67])).
% 1.32/0.55  fof(f67,plain,(
% 1.32/0.55    ( ! [X0,X1] : (sK2(X0,X1) = X0 | k2_enumset1(X0,X0,X0,X0) = X1 | r2_hidden(sK2(X0,X1),X1)) )),
% 1.32/0.55    inference(definition_unfolding,[],[f49,f62])).
% 1.32/0.55  fof(f49,plain,(
% 1.32/0.55    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f28])).
% 1.32/0.55  fof(f66,plain,(
% 1.32/0.55    ( ! [X0,X1] : (sK2(X0,X1) != X0 | k2_enumset1(X0,X0,X0,X0) = X1 | ~r2_hidden(sK2(X0,X1),X1)) )),
% 1.32/0.55    inference(definition_unfolding,[],[f50,f62])).
% 1.32/0.55  fof(f50,plain,(
% 1.32/0.55    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f28])).
% 1.32/0.55  % SZS output end Proof for theBenchmark
% 1.32/0.55  % (17880)------------------------------
% 1.32/0.55  % (17880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (17880)Termination reason: Refutation
% 1.32/0.55  
% 1.32/0.55  % (17880)Memory used [KB]: 6396
% 1.32/0.55  % (17880)Time elapsed: 0.107 s
% 1.32/0.55  % (17880)------------------------------
% 1.32/0.55  % (17880)------------------------------
% 1.32/0.55  % (17870)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.32/0.56  % (17868)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.32/0.56  % (17881)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.32/0.56  % (17875)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.32/0.56  % (17853)Success in time 0.188 s
%------------------------------------------------------------------------------
