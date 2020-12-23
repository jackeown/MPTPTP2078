%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 732 expanded)
%              Number of leaves         :   11 ( 195 expanded)
%              Depth                    :   18
%              Number of atoms          :  292 (2589 expanded)
%              Number of equality atoms :   95 (1208 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f173,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f160,f161,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | k1_funct_1(sK1,X0) = X1 ) ),
    inference(subsumption_resolution,[],[f79,f31])).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))
    & k1_tarski(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f19])).

fof(f19,plain,
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

fof(f12,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

% (12023)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | k1_funct_1(sK1,X0) = X1
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f49,f32])).

fof(f32,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

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
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f161,plain,(
    r2_hidden(k4_tarski(sK0,sK2(k1_funct_1(sK1,sK0),k2_relat_1(sK1))),sK1) ),
    inference(backward_demodulation,[],[f156,f157])).

fof(f157,plain,(
    sK0 = sK3(sK2(k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k1_relat_1(sK1),sK1) ),
    inference(resolution,[],[f142,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | sK0 = sK3(X0,k1_relat_1(sK1),sK1) ) ),
    inference(resolution,[],[f69,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | sK0 = X0 ) ),
    inference(superposition,[],[f61,f54])).

fof(f54,plain,(
    k1_relat_1(sK1) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f33,f52])).

% (12043)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    k1_tarski(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f61,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f39,f52])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).

fof(f23,plain,(
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

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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

fof(f69,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0,k1_relat_1(sK1),sK1),k1_relat_1(sK1))
      | ~ r2_hidden(X0,k2_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f68,f31])).

fof(f68,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | r2_hidden(sK3(X0,k1_relat_1(sK1),sK1),k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f67,f36])).

fof(f36,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(sK1,X1))
      | r2_hidden(sK3(X0,X1,sK1),X1) ) ),
    inference(resolution,[],[f46,f31])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK3(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
            & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
        & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f142,plain,(
    r2_hidden(sK2(k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f140,f53])).

fof(f53,plain,(
    k2_relat_1(sK1) != k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(definition_unfolding,[],[f34,f52])).

fof(f34,plain,(
    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f140,plain,
    ( k2_relat_1(sK1) = k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))
    | r2_hidden(sK2(k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) ),
    inference(resolution,[],[f135,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_enumset1(X0,X0,X0,X0) = X1
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(trivial_inequality_removal,[],[f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 != X0
      | k2_enumset1(X0,X0,X0,X0) = X1
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 != X0
      | k2_enumset1(X0,X0,X0,X0) = X1
      | k2_enumset1(X0,X0,X0,X0) = X1
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(superposition,[],[f55,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) = X0
      | k2_enumset1(X0,X0,X0,X0) = X1
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f41,f52])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK2(X0,X1) = X0
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | sK2(X0,X1) != X0
      | k2_enumset1(X0,X0,X0,X0) = X1 ) ),
    inference(definition_unfolding,[],[f42,f52])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK2(X0,X1) != X0
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f135,plain,(
    r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f132,f31])).

fof(f132,plain,
    ( r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f123,f36])).

fof(f123,plain,(
    r2_hidden(k1_funct_1(sK1,sK0),k9_relat_1(sK1,k1_relat_1(sK1))) ),
    inference(resolution,[],[f119,f63])).

fof(f63,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(superposition,[],[f60,f54])).

fof(f60,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f40,f52])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f119,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,X0)
      | r2_hidden(k1_funct_1(sK1,sK0),k9_relat_1(sK1,X0)) ) ),
    inference(resolution,[],[f108,f63])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | r2_hidden(k1_funct_1(sK1,X0),k9_relat_1(sK1,X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f107,f87])).

fof(f87,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f86,f31])).

fof(f86,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f62,f32])).

fof(f62,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X2),sK1)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X2,k9_relat_1(sK1,X1)) ) ),
    inference(subsumption_resolution,[],[f106,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f70,f31])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f48,f32])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(k4_tarski(X0,X2),sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | r2_hidden(X2,k9_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f47,f31])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f156,plain,(
    r2_hidden(k4_tarski(sK3(sK2(k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k1_relat_1(sK1),sK1),sK2(k1_funct_1(sK1,sK0),k2_relat_1(sK1))),sK1) ),
    inference(resolution,[],[f142,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | r2_hidden(k4_tarski(sK3(X0,k1_relat_1(sK1),sK1),X0),sK1) ) ),
    inference(subsumption_resolution,[],[f84,f31])).

fof(f84,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | r2_hidden(k4_tarski(sK3(X0,k1_relat_1(sK1),sK1),X0),sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f83,f36])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(sK1,X1))
      | r2_hidden(k4_tarski(sK3(X0,X1,sK1),X0),sK1) ) ),
    inference(resolution,[],[f45,f31])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f160,plain,(
    k1_funct_1(sK1,sK0) != sK2(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f155,f53])).

fof(f155,plain,
    ( k1_funct_1(sK1,sK0) != sK2(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | k2_relat_1(sK1) = k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(resolution,[],[f142,f55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (12029)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.51  % (12026)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.51  % (12038)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (12045)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (12045)Refutation not found, incomplete strategy% (12045)------------------------------
% 0.20/0.51  % (12045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (12045)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (12045)Memory used [KB]: 1663
% 0.20/0.51  % (12045)Time elapsed: 0.109 s
% 0.20/0.51  % (12045)------------------------------
% 0.20/0.51  % (12045)------------------------------
% 0.20/0.52  % (12030)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (12038)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f173,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f160,f161,f80])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | k1_funct_1(sK1,X0) = X1) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f79,f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    v1_relat_1(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.52    inference(flattening,[],[f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  % (12023)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  fof(f10,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.20/0.52    inference(negated_conjecture,[],[f9])).
% 0.20/0.52  fof(f9,conjecture,(
% 0.20/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | k1_funct_1(sK1,X0) = X1 | ~v1_relat_1(sK1)) )),
% 0.20/0.52    inference(resolution,[],[f49,f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    v1_funct_1(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.52    inference(flattening,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.52    inference(nnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.52    inference(flattening,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.20/0.52  fof(f161,plain,(
% 0.20/0.52    r2_hidden(k4_tarski(sK0,sK2(k1_funct_1(sK1,sK0),k2_relat_1(sK1))),sK1)),
% 0.20/0.52    inference(backward_demodulation,[],[f156,f157])).
% 0.20/0.52  fof(f157,plain,(
% 0.20/0.52    sK0 = sK3(sK2(k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k1_relat_1(sK1),sK1)),
% 0.20/0.52    inference(resolution,[],[f142,f72])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | sK0 = sK3(X0,k1_relat_1(sK1),sK1)) )),
% 0.20/0.52    inference(resolution,[],[f69,f65])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | sK0 = X0) )),
% 0.20/0.52    inference(superposition,[],[f61,f54])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    k1_relat_1(sK1) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.20/0.52    inference(definition_unfolding,[],[f33,f52])).
% 0.20/0.52  % (12043)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f35,f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f37,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    k1_tarski(sK0) = k1_relat_1(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 0.20/0.52    inference(equality_resolution,[],[f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.20/0.52    inference(definition_unfolding,[],[f39,f52])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.52    inference(rectify,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.52    inference(nnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK3(X0,k1_relat_1(sK1),sK1),k1_relat_1(sK1)) | ~r2_hidden(X0,k2_relat_1(sK1))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f68,f31])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | r2_hidden(sK3(X0,k1_relat_1(sK1),sK1),k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 0.20/0.52    inference(superposition,[],[f67,f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK1,X1)) | r2_hidden(sK3(X0,X1,sK1),X1)) )),
% 0.20/0.52    inference(resolution,[],[f46,f31])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK3(X0,X1,X2),X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.52    inference(rectify,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.52    inference(nnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.20/0.52  fof(f142,plain,(
% 0.20/0.52    r2_hidden(sK2(k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1))),
% 0.20/0.52    inference(subsumption_resolution,[],[f140,f53])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    k2_relat_1(sK1) != k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 0.20/0.52    inference(definition_unfolding,[],[f34,f52])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f140,plain,(
% 0.20/0.52    k2_relat_1(sK1) = k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) | r2_hidden(sK2(k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1))),
% 0.20/0.52    inference(resolution,[],[f135,f99])).
% 0.20/0.52  fof(f99,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_enumset1(X0,X0,X0,X0) = X1 | r2_hidden(sK2(X0,X1),X1)) )),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f98])).
% 0.20/0.52  fof(f98,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | X0 != X0 | k2_enumset1(X0,X0,X0,X0) = X1 | r2_hidden(sK2(X0,X1),X1)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f97])).
% 0.20/0.52  fof(f97,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | X0 != X0 | k2_enumset1(X0,X0,X0,X0) = X1 | k2_enumset1(X0,X0,X0,X0) = X1 | r2_hidden(sK2(X0,X1),X1)) )),
% 0.20/0.52    inference(superposition,[],[f55,f56])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ( ! [X0,X1] : (sK2(X0,X1) = X0 | k2_enumset1(X0,X0,X0,X0) = X1 | r2_hidden(sK2(X0,X1),X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f41,f52])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | sK2(X0,X1) != X0 | k2_enumset1(X0,X0,X0,X0) = X1) )),
% 0.20/0.52    inference(definition_unfolding,[],[f42,f52])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f135,plain,(
% 0.20/0.52    r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))),
% 0.20/0.52    inference(subsumption_resolution,[],[f132,f31])).
% 0.20/0.52  fof(f132,plain,(
% 0.20/0.52    r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 0.20/0.52    inference(superposition,[],[f123,f36])).
% 0.20/0.52  fof(f123,plain,(
% 0.20/0.52    r2_hidden(k1_funct_1(sK1,sK0),k9_relat_1(sK1,k1_relat_1(sK1)))),
% 0.20/0.52    inference(resolution,[],[f119,f63])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.52    inference(superposition,[],[f60,f54])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 0.20/0.52    inference(equality_resolution,[],[f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 0.20/0.52    inference(equality_resolution,[],[f57])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.20/0.52    inference(definition_unfolding,[],[f40,f52])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f119,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(sK0,X0) | r2_hidden(k1_funct_1(sK1,sK0),k9_relat_1(sK1,X0))) )),
% 0.20/0.52    inference(resolution,[],[f108,f63])).
% 0.20/0.52  fof(f108,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k1_funct_1(sK1,X0),k9_relat_1(sK1,X1)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(resolution,[],[f107,f87])).
% 0.20/0.52  fof(f87,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) | ~r2_hidden(X0,k1_relat_1(sK1))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f86,f31])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) | ~v1_relat_1(sK1)) )),
% 0.20/0.52    inference(resolution,[],[f62,f32])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ( ! [X2,X0] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~v1_relat_1(X2)) )),
% 0.20/0.52    inference(equality_resolution,[],[f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f107,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X2),sK1) | ~r2_hidden(X0,X1) | r2_hidden(X2,k9_relat_1(sK1,X1))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f106,f71])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | r2_hidden(X0,k1_relat_1(sK1))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f70,f31])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 0.20/0.52    inference(resolution,[],[f48,f32])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(k4_tarski(X0,X2),sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(X2,k9_relat_1(sK1,X1))) )),
% 0.20/0.52    inference(resolution,[],[f47,f31])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)) | r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f28])).
% 0.20/0.52  fof(f156,plain,(
% 0.20/0.52    r2_hidden(k4_tarski(sK3(sK2(k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k1_relat_1(sK1),sK1),sK2(k1_funct_1(sK1,sK0),k2_relat_1(sK1))),sK1)),
% 0.20/0.52    inference(resolution,[],[f142,f85])).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | r2_hidden(k4_tarski(sK3(X0,k1_relat_1(sK1),sK1),X0),sK1)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f84,f31])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | r2_hidden(k4_tarski(sK3(X0,k1_relat_1(sK1),sK1),X0),sK1) | ~v1_relat_1(sK1)) )),
% 0.20/0.52    inference(superposition,[],[f83,f36])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK1,X1)) | r2_hidden(k4_tarski(sK3(X0,X1,sK1),X0),sK1)) )),
% 0.20/0.52    inference(resolution,[],[f45,f31])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f28])).
% 0.20/0.52  fof(f160,plain,(
% 0.20/0.52    k1_funct_1(sK1,sK0) != sK2(k1_funct_1(sK1,sK0),k2_relat_1(sK1))),
% 0.20/0.52    inference(subsumption_resolution,[],[f155,f53])).
% 0.20/0.52  fof(f155,plain,(
% 0.20/0.52    k1_funct_1(sK1,sK0) != sK2(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | k2_relat_1(sK1) = k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 0.20/0.52    inference(resolution,[],[f142,f55])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (12038)------------------------------
% 0.20/0.52  % (12038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (12038)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (12038)Memory used [KB]: 6396
% 0.20/0.52  % (12038)Time elapsed: 0.112 s
% 0.20/0.52  % (12038)------------------------------
% 0.20/0.52  % (12038)------------------------------
% 0.20/0.52  % (12015)Success in time 0.163 s
%------------------------------------------------------------------------------
