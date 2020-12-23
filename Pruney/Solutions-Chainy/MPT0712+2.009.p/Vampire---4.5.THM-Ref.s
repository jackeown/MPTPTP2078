%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:44 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 291 expanded)
%              Number of leaves         :   18 (  78 expanded)
%              Depth                    :   14
%              Number of atoms          :  243 ( 735 expanded)
%              Number of equality atoms :   49 ( 129 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f866,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f76,f181,f182,f215,f339,f295])).

fof(f295,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(k1_relat_1(X6),X8)
      | ~ r1_tarski(k1_relat_1(X6),X7)
      | ~ v1_relat_1(X6)
      | ~ r1_xboole_0(X8,X7)
      | k1_xboole_0 = X6 ) ),
    inference(duplicate_literal_removal,[],[f273])).

fof(f273,plain,(
    ! [X6,X8,X7] :
      ( k1_xboole_0 = X6
      | ~ r1_tarski(k1_relat_1(X6),X7)
      | ~ v1_relat_1(X6)
      | ~ r1_xboole_0(X8,X7)
      | ~ v1_relat_1(X6)
      | ~ r1_tarski(k1_relat_1(X6),X8) ) ),
    inference(superposition,[],[f50,f131])).

fof(f131,plain,(
    ! [X4,X5,X3] :
      ( k1_xboole_0 = k7_relat_1(X3,X5)
      | ~ r1_xboole_0(X4,X5)
      | ~ v1_relat_1(X3)
      | ~ r1_tarski(k1_relat_1(X3),X4) ) ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,(
    ! [X4,X5,X3] :
      ( k1_xboole_0 = k7_relat_1(X3,X5)
      | ~ r1_xboole_0(X4,X5)
      | ~ v1_relat_1(X3)
      | ~ r1_tarski(k1_relat_1(X3),X4)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f62,f50])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f339,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f76,f117,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f117,plain,(
    ! [X0] : v4_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f42,f77,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).

fof(f77,plain,(
    v4_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f42,f74,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f42,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f35])).

fof(f35,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).

fof(f215,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f76,f118,f51])).

fof(f118,plain,(
    ! [X0] : v4_relat_1(k7_relat_1(sK1,X0),X0) ),
    inference(unit_resulting_resolution,[],[f42,f77,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(k7_relat_1(X2,X0),X0)
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f182,plain,(
    k1_xboole_0 != k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f42,f177,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

% (28136)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% (28144)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
fof(f177,plain,(
    ~ r1_xboole_0(k1_relat_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(subsumption_resolution,[],[f176,f42])).

fof(f176,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f173,f45])).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f173,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | ~ r1_xboole_0(k1_relat_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f167,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(f167,plain,(
    ~ r1_tarski(k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f71,f84])).

fof(f84,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(unit_resulting_resolution,[],[f42,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f71,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    inference(definition_unfolding,[],[f44,f70,f70])).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f61,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f44,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f181,plain,(
    r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f180,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f70])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f180,plain,(
    ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f179,f42])).

fof(f179,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f178,f43])).

fof(f43,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f178,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f175,f74])).

fof(f175,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(duplicate_literal_removal,[],[f174])).

fof(f174,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f167,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k3_enumset1(X0,X0,X0,X0,X1)) = k3_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f63,f69,f69])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X1,k1_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) )
       => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).

fof(f76,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f42,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:28:44 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (28127)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.51  % (28135)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.52  % (28135)Refutation not found, incomplete strategy% (28135)------------------------------
% 0.22/0.52  % (28135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (28134)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.52  % (28135)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (28135)Memory used [KB]: 10746
% 0.22/0.52  % (28135)Time elapsed: 0.096 s
% 0.22/0.52  % (28135)------------------------------
% 0.22/0.52  % (28135)------------------------------
% 0.22/0.52  % (28129)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (28130)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (28132)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (28125)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (28131)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (28143)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.53  % (28126)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (28149)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (28148)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (28142)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  % (28153)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (28140)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (28146)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (28147)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (28153)Refutation not found, incomplete strategy% (28153)------------------------------
% 0.22/0.54  % (28153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (28153)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (28153)Memory used [KB]: 10746
% 0.22/0.54  % (28153)Time elapsed: 0.131 s
% 0.22/0.54  % (28153)------------------------------
% 0.22/0.54  % (28153)------------------------------
% 0.22/0.55  % (28133)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (28141)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (28141)Refutation not found, incomplete strategy% (28141)------------------------------
% 0.22/0.55  % (28141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (28141)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (28141)Memory used [KB]: 10618
% 0.22/0.55  % (28141)Time elapsed: 0.130 s
% 0.22/0.55  % (28141)------------------------------
% 0.22/0.55  % (28141)------------------------------
% 0.22/0.55  % (28145)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (28128)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.55  % (28154)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.56  % (28154)Refutation not found, incomplete strategy% (28154)------------------------------
% 0.22/0.56  % (28154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (28154)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (28154)Memory used [KB]: 1663
% 0.22/0.56  % (28154)Time elapsed: 0.142 s
% 0.22/0.56  % (28154)------------------------------
% 0.22/0.56  % (28154)------------------------------
% 0.22/0.56  % (28138)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.56  % (28139)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.56  % (28149)Refutation not found, incomplete strategy% (28149)------------------------------
% 0.22/0.56  % (28149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (28151)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (28149)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (28149)Memory used [KB]: 10618
% 0.22/0.56  % (28137)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.56  % (28150)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.56  % (28139)Refutation not found, incomplete strategy% (28139)------------------------------
% 0.22/0.56  % (28139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (28139)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (28139)Memory used [KB]: 1663
% 0.22/0.56  % (28139)Time elapsed: 0.150 s
% 0.22/0.56  % (28139)------------------------------
% 0.22/0.56  % (28139)------------------------------
% 0.22/0.57  % (28152)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.57  % (28152)Refutation not found, incomplete strategy% (28152)------------------------------
% 0.22/0.57  % (28152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (28152)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (28152)Memory used [KB]: 6140
% 0.22/0.57  % (28152)Time elapsed: 0.148 s
% 0.22/0.57  % (28152)------------------------------
% 0.22/0.57  % (28152)------------------------------
% 1.58/0.57  % (28149)Time elapsed: 0.141 s
% 1.58/0.57  % (28149)------------------------------
% 1.58/0.57  % (28149)------------------------------
% 1.58/0.58  % (28129)Refutation found. Thanks to Tanya!
% 1.58/0.58  % SZS status Theorem for theBenchmark
% 1.58/0.58  % SZS output start Proof for theBenchmark
% 1.58/0.58  fof(f866,plain,(
% 1.58/0.58    $false),
% 1.58/0.58    inference(unit_resulting_resolution,[],[f76,f181,f182,f215,f339,f295])).
% 1.58/0.58  fof(f295,plain,(
% 1.58/0.58    ( ! [X6,X8,X7] : (~r1_tarski(k1_relat_1(X6),X8) | ~r1_tarski(k1_relat_1(X6),X7) | ~v1_relat_1(X6) | ~r1_xboole_0(X8,X7) | k1_xboole_0 = X6) )),
% 1.58/0.58    inference(duplicate_literal_removal,[],[f273])).
% 1.58/0.58  fof(f273,plain,(
% 1.58/0.58    ( ! [X6,X8,X7] : (k1_xboole_0 = X6 | ~r1_tarski(k1_relat_1(X6),X7) | ~v1_relat_1(X6) | ~r1_xboole_0(X8,X7) | ~v1_relat_1(X6) | ~r1_tarski(k1_relat_1(X6),X8)) )),
% 1.58/0.58    inference(superposition,[],[f50,f131])).
% 1.58/0.58  fof(f131,plain,(
% 1.58/0.58    ( ! [X4,X5,X3] : (k1_xboole_0 = k7_relat_1(X3,X5) | ~r1_xboole_0(X4,X5) | ~v1_relat_1(X3) | ~r1_tarski(k1_relat_1(X3),X4)) )),
% 1.58/0.58    inference(duplicate_literal_removal,[],[f121])).
% 1.58/0.58  fof(f121,plain,(
% 1.58/0.58    ( ! [X4,X5,X3] : (k1_xboole_0 = k7_relat_1(X3,X5) | ~r1_xboole_0(X4,X5) | ~v1_relat_1(X3) | ~r1_tarski(k1_relat_1(X3),X4) | ~v1_relat_1(X3)) )),
% 1.58/0.58    inference(superposition,[],[f62,f50])).
% 1.58/0.58  fof(f62,plain,(
% 1.58/0.58    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f30])).
% 1.58/0.58  fof(f30,plain,(
% 1.58/0.58    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 1.58/0.58    inference(flattening,[],[f29])).
% 1.58/0.58  fof(f29,plain,(
% 1.58/0.58    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.58/0.58    inference(ennf_transformation,[],[f13])).
% 1.58/0.58  fof(f13,axiom,(
% 1.58/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 1.58/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).
% 1.58/0.58  fof(f50,plain,(
% 1.58/0.58    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f24])).
% 1.58/0.58  fof(f24,plain,(
% 1.58/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.58/0.58    inference(flattening,[],[f23])).
% 1.58/0.58  fof(f23,plain,(
% 1.58/0.58    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.58/0.58    inference(ennf_transformation,[],[f15])).
% 1.58/0.58  fof(f15,axiom,(
% 1.58/0.58    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.58/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 1.58/0.58  fof(f339,plain,(
% 1.58/0.58    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK1))) )),
% 1.58/0.58    inference(unit_resulting_resolution,[],[f76,f117,f51])).
% 1.58/0.58  fof(f51,plain,(
% 1.58/0.58    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f37])).
% 1.58/0.58  fof(f37,plain,(
% 1.58/0.58    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.58/0.58    inference(nnf_transformation,[],[f25])).
% 1.58/0.58  fof(f25,plain,(
% 1.58/0.58    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.58/0.58    inference(ennf_transformation,[],[f8])).
% 1.58/0.58  fof(f8,axiom,(
% 1.58/0.58    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.58/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.58/0.58  fof(f117,plain,(
% 1.58/0.58    ( ! [X0] : (v4_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 1.58/0.58    inference(unit_resulting_resolution,[],[f42,f77,f66])).
% 1.58/0.58  fof(f66,plain,(
% 1.58/0.58    ( ! [X2,X0,X1] : (v4_relat_1(k7_relat_1(X2,X0),X1) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f34])).
% 1.58/0.58  fof(f34,plain,(
% 1.58/0.58    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 1.58/0.58    inference(flattening,[],[f33])).
% 1.58/0.58  fof(f33,plain,(
% 1.58/0.58    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | (~v4_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 1.58/0.58    inference(ennf_transformation,[],[f10])).
% 1.58/0.58  fof(f10,axiom,(
% 1.58/0.58    ! [X0,X1,X2] : ((v4_relat_1(X2,X1) & v1_relat_1(X2)) => (v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))))),
% 1.58/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).
% 1.58/0.58  fof(f77,plain,(
% 1.58/0.58    v4_relat_1(sK1,k1_relat_1(sK1))),
% 1.58/0.58    inference(unit_resulting_resolution,[],[f42,f74,f52])).
% 1.58/0.58  fof(f52,plain,(
% 1.58/0.58    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f37])).
% 1.58/0.58  fof(f74,plain,(
% 1.58/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.58/0.58    inference(equality_resolution,[],[f59])).
% 1.58/0.58  fof(f59,plain,(
% 1.58/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.58/0.58    inference(cnf_transformation,[],[f41])).
% 1.58/0.58  fof(f41,plain,(
% 1.58/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.58/0.58    inference(flattening,[],[f40])).
% 1.58/0.58  fof(f40,plain,(
% 1.58/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.58/0.58    inference(nnf_transformation,[],[f1])).
% 1.58/0.58  fof(f1,axiom,(
% 1.58/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.58/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.58/0.58  fof(f42,plain,(
% 1.58/0.58    v1_relat_1(sK1)),
% 1.58/0.58    inference(cnf_transformation,[],[f36])).
% 1.58/0.58  fof(f36,plain,(
% 1.58/0.58    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.58/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f35])).
% 1.58/0.58  fof(f35,plain,(
% 1.58/0.58    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.58/0.58    introduced(choice_axiom,[])).
% 1.58/0.58  fof(f20,plain,(
% 1.58/0.58    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.58/0.58    inference(flattening,[],[f19])).
% 1.58/0.58  fof(f19,plain,(
% 1.58/0.58    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.58/0.58    inference(ennf_transformation,[],[f18])).
% 1.58/0.58  fof(f18,negated_conjecture,(
% 1.58/0.58    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 1.58/0.58    inference(negated_conjecture,[],[f17])).
% 1.58/0.58  fof(f17,conjecture,(
% 1.58/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 1.58/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).
% 1.58/0.58  fof(f215,plain,(
% 1.58/0.58    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0)) )),
% 1.58/0.58    inference(unit_resulting_resolution,[],[f76,f118,f51])).
% 1.58/0.58  fof(f118,plain,(
% 1.58/0.58    ( ! [X0] : (v4_relat_1(k7_relat_1(sK1,X0),X0)) )),
% 1.58/0.58    inference(unit_resulting_resolution,[],[f42,f77,f65])).
% 1.58/0.58  fof(f65,plain,(
% 1.58/0.58    ( ! [X2,X0,X1] : (v4_relat_1(k7_relat_1(X2,X0),X0) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f34])).
% 1.58/0.58  fof(f182,plain,(
% 1.58/0.58    k1_xboole_0 != k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.58/0.58    inference(unit_resulting_resolution,[],[f42,f177,f55])).
% 1.58/0.58  fof(f55,plain,(
% 1.58/0.58    ( ! [X0,X1] : (k1_xboole_0 != k7_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f39])).
% 1.58/0.58  fof(f39,plain,(
% 1.58/0.58    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.58/0.58    inference(nnf_transformation,[],[f27])).
% 1.58/0.58  fof(f27,plain,(
% 1.58/0.58    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.58/0.58    inference(ennf_transformation,[],[f14])).
% 1.58/0.58  fof(f14,axiom,(
% 1.58/0.58    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.58/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 1.58/0.59  % (28136)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.58/0.59  % (28144)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.78/0.60  fof(f177,plain,(
% 1.78/0.60    ~r1_xboole_0(k1_relat_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.78/0.60    inference(subsumption_resolution,[],[f176,f42])).
% 1.78/0.60  fof(f176,plain,(
% 1.78/0.60    ~r1_xboole_0(k1_relat_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK1)),
% 1.78/0.60    inference(subsumption_resolution,[],[f173,f45])).
% 1.78/0.60  fof(f45,plain,(
% 1.78/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f2])).
% 1.78/0.60  fof(f2,axiom,(
% 1.78/0.60    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.78/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.78/0.60  fof(f173,plain,(
% 1.78/0.60    ~r1_tarski(k1_xboole_0,k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) | ~r1_xboole_0(k1_relat_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK1)),
% 1.78/0.60    inference(superposition,[],[f167,f54])).
% 1.78/0.60  fof(f54,plain,(
% 1.78/0.60    ( ! [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f38])).
% 1.78/0.60  fof(f38,plain,(
% 1.78/0.60    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.78/0.60    inference(nnf_transformation,[],[f26])).
% 1.78/0.60  fof(f26,plain,(
% 1.78/0.60    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.78/0.60    inference(ennf_transformation,[],[f12])).
% 1.78/0.60  fof(f12,axiom,(
% 1.78/0.60    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.78/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).
% 1.78/0.60  fof(f167,plain,(
% 1.78/0.60    ~r1_tarski(k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))),
% 1.78/0.60    inference(backward_demodulation,[],[f71,f84])).
% 1.78/0.60  fof(f84,plain,(
% 1.78/0.60    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) )),
% 1.78/0.60    inference(unit_resulting_resolution,[],[f42,f49])).
% 1.78/0.60  fof(f49,plain,(
% 1.78/0.60    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f22])).
% 1.78/0.60  fof(f22,plain,(
% 1.78/0.60    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.78/0.60    inference(ennf_transformation,[],[f11])).
% 1.78/0.60  fof(f11,axiom,(
% 1.78/0.60    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.78/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.78/0.60  fof(f71,plain,(
% 1.78/0.60    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))),
% 1.78/0.60    inference(definition_unfolding,[],[f44,f70,f70])).
% 1.78/0.60  fof(f70,plain,(
% 1.78/0.60    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.78/0.60    inference(definition_unfolding,[],[f46,f69])).
% 1.78/0.60  fof(f69,plain,(
% 1.78/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.78/0.60    inference(definition_unfolding,[],[f47,f68])).
% 1.78/0.60  fof(f68,plain,(
% 1.78/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.78/0.60    inference(definition_unfolding,[],[f61,f67])).
% 1.78/0.60  fof(f67,plain,(
% 1.78/0.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f6])).
% 1.78/0.60  fof(f6,axiom,(
% 1.78/0.60    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.78/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.78/0.60  fof(f61,plain,(
% 1.78/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f5])).
% 1.78/0.60  fof(f5,axiom,(
% 1.78/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.78/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.78/0.60  fof(f47,plain,(
% 1.78/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f4])).
% 1.78/0.60  fof(f4,axiom,(
% 1.78/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.78/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.78/0.60  fof(f46,plain,(
% 1.78/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f3])).
% 1.78/0.60  fof(f3,axiom,(
% 1.78/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.78/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.78/0.60  fof(f44,plain,(
% 1.78/0.60    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),
% 1.78/0.60    inference(cnf_transformation,[],[f36])).
% 1.78/0.60  fof(f181,plain,(
% 1.78/0.60    r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1))),
% 1.78/0.60    inference(unit_resulting_resolution,[],[f180,f72])).
% 1.78/0.60  fof(f72,plain,(
% 1.78/0.60    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.78/0.60    inference(definition_unfolding,[],[f57,f70])).
% 1.78/0.60  fof(f57,plain,(
% 1.78/0.60    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f28])).
% 1.78/0.60  fof(f28,plain,(
% 1.78/0.60    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.78/0.60    inference(ennf_transformation,[],[f7])).
% 1.78/0.60  fof(f7,axiom,(
% 1.78/0.60    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.78/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.78/0.60  fof(f180,plain,(
% 1.78/0.60    ~r2_hidden(sK0,k1_relat_1(sK1))),
% 1.78/0.60    inference(subsumption_resolution,[],[f179,f42])).
% 1.78/0.60  fof(f179,plain,(
% 1.78/0.60    ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 1.78/0.60    inference(subsumption_resolution,[],[f178,f43])).
% 1.78/0.60  fof(f43,plain,(
% 1.78/0.60    v1_funct_1(sK1)),
% 1.78/0.60    inference(cnf_transformation,[],[f36])).
% 1.78/0.60  fof(f178,plain,(
% 1.78/0.60    ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.78/0.60    inference(subsumption_resolution,[],[f175,f74])).
% 1.78/0.60  fof(f175,plain,(
% 1.78/0.60    ~r1_tarski(k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.78/0.60    inference(duplicate_literal_removal,[],[f174])).
% 1.78/0.60  fof(f174,plain,(
% 1.78/0.60    ~r1_tarski(k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.78/0.60    inference(superposition,[],[f167,f73])).
% 1.78/0.60  fof(f73,plain,(
% 1.78/0.60    ( ! [X2,X0,X1] : (k9_relat_1(X2,k3_enumset1(X0,X0,X0,X0,X1)) = k3_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.78/0.60    inference(definition_unfolding,[],[f63,f69,f69])).
% 1.78/0.60  fof(f63,plain,(
% 1.78/0.60    ( ! [X2,X0,X1] : (k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f32])).
% 1.78/0.60  fof(f32,plain,(
% 1.78/0.60    ! [X0,X1,X2] : (k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.78/0.60    inference(flattening,[],[f31])).
% 1.78/0.60  fof(f31,plain,(
% 1.78/0.60    ! [X0,X1,X2] : ((k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | (~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.78/0.60    inference(ennf_transformation,[],[f16])).
% 1.78/0.60  fof(f16,axiom,(
% 1.78/0.60    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X1,k1_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))))),
% 1.78/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).
% 1.78/0.60  fof(f76,plain,(
% 1.78/0.60    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) )),
% 1.78/0.60    inference(unit_resulting_resolution,[],[f42,f48])).
% 1.78/0.60  fof(f48,plain,(
% 1.78/0.60    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f21])).
% 1.78/0.60  fof(f21,plain,(
% 1.78/0.60    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.78/0.60    inference(ennf_transformation,[],[f9])).
% 1.78/0.60  fof(f9,axiom,(
% 1.78/0.60    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.78/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.78/0.60  % SZS output end Proof for theBenchmark
% 1.78/0.60  % (28129)------------------------------
% 1.78/0.60  % (28129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.60  % (28129)Termination reason: Refutation
% 1.78/0.60  
% 1.78/0.60  % (28129)Memory used [KB]: 2174
% 1.78/0.60  % (28129)Time elapsed: 0.166 s
% 1.78/0.60  % (28129)------------------------------
% 1.78/0.60  % (28129)------------------------------
% 1.78/0.60  % (28124)Success in time 0.231 s
%------------------------------------------------------------------------------
