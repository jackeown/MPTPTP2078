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
% DateTime   : Thu Dec  3 12:48:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 353 expanded)
%              Number of leaves         :   17 (  93 expanded)
%              Depth                    :   24
%              Number of atoms          :  253 (1308 expanded)
%              Number of equality atoms :   49 ( 197 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1741,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1691,f1689])).

fof(f1689,plain,(
    ~ r1_xboole_0(k1_relat_1(sK3),sK2) ),
    inference(trivial_inequality_removal,[],[f1632])).

fof(f1632,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(sK3),sK2) ),
    inference(backward_demodulation,[],[f47,f1631])).

fof(f1631,plain,(
    k1_xboole_0 = k7_relat_1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f1630,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f1630,plain,
    ( v1_xboole_0(k7_relat_1(sK3,sK2))
    | k1_xboole_0 = k7_relat_1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f1629,f77])).

fof(f77,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(resolution,[],[f62,f45])).

fof(f45,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK3),sK2)
      | k1_xboole_0 != k7_relat_1(sK3,sK2) )
    & ( r1_xboole_0(k1_relat_1(sK3),sK2)
      | k1_xboole_0 = k7_relat_1(sK3,sK2) )
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f32,f33])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k7_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK3),sK2)
        | k1_xboole_0 != k7_relat_1(sK3,sK2) )
      & ( r1_xboole_0(k1_relat_1(sK3),sK2)
        | k1_xboole_0 = k7_relat_1(sK3,sK2) )
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f1629,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | v1_xboole_0(k7_relat_1(sK3,sK2))
    | k1_xboole_0 = k7_relat_1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f1610,f48])).

fof(f48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1610,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | v1_xboole_0(k7_relat_1(sK3,sK2))
    | k1_xboole_0 = k7_relat_1(sK3,sK2) ),
    inference(superposition,[],[f55,f1571])).

fof(f1571,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,sK2))
    | k1_xboole_0 = k7_relat_1(sK3,sK2) ),
    inference(superposition,[],[f1554,f92])).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f72,f53])).

fof(f53,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f52,f56])).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f1554,plain,(
    ! [X3] :
      ( k4_xboole_0(X3,k1_relat_1(k7_relat_1(sK3,sK2))) = X3
      | k1_xboole_0 = k7_relat_1(sK3,sK2) ) ),
    inference(resolution,[],[f1525,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

% (7074)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
fof(f1525,plain,(
    ! [X1] :
      ( r1_xboole_0(X1,k1_relat_1(k7_relat_1(sK3,sK2)))
      | k1_xboole_0 = k7_relat_1(sK3,sK2) ) ),
    inference(subsumption_resolution,[],[f1518,f1410])).

fof(f1410,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK5(X2,k1_relat_1(k7_relat_1(sK3,X3))),k1_relat_1(sK3))
      | r1_xboole_0(X2,k1_relat_1(k7_relat_1(sK3,X3))) ) ),
    inference(resolution,[],[f1283,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ r2_hidden(X1,k1_relat_1(X0))
        | ~ r2_hidden(X1,X2) )
      & ( ( r2_hidden(X1,k1_relat_1(X0))
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,X1) )
      & ( ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,X1) )
      & ( ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ( r2_hidden(X0,k1_relat_1(X2))
        & r2_hidden(X0,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1283,plain,(
    ! [X0,X1] :
      ( sP0(sK3,sK5(X0,k1_relat_1(k7_relat_1(sK3,X1))),X1)
      | r1_xboole_0(X0,k1_relat_1(k7_relat_1(sK3,X1))) ) ),
    inference(resolution,[],[f530,f84])).

fof(f84,plain,(
    ! [X0,X1] : sP1(X0,X1,sK3) ),
    inference(resolution,[],[f71,f45])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | sP1(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X0,X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f27,f29,f28])).

fof(f29,plain,(
    ! [X1,X0,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> sP0(X2,X0,X1) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(f530,plain,(
    ! [X4,X5,X3] :
      ( ~ sP1(X5,sK5(X4,k1_relat_1(k7_relat_1(X3,X5))),X3)
      | sP0(X3,sK5(X4,k1_relat_1(k7_relat_1(X3,X5))),X5)
      | r1_xboole_0(X4,k1_relat_1(k7_relat_1(X3,X5))) ) ),
    inference(resolution,[],[f66,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
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

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0)))
      | sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0)))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0))) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X1,X0,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ sP0(X2,X0,X1) )
        & ( sP0(X2,X0,X1)
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f1518,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK5(X1,k1_relat_1(k7_relat_1(sK3,sK2))),k1_relat_1(sK3))
      | k1_xboole_0 = k7_relat_1(sK3,sK2)
      | r1_xboole_0(X1,k1_relat_1(k7_relat_1(sK3,sK2))) ) ),
    inference(resolution,[],[f1366,f60])).

fof(f1366,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_relat_1(k7_relat_1(sK3,sK2)))
      | ~ r2_hidden(X2,k1_relat_1(sK3))
      | k1_xboole_0 = k7_relat_1(sK3,sK2) ) ),
    inference(resolution,[],[f1125,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1125,plain,
    ( r1_xboole_0(k1_relat_1(k7_relat_1(sK3,sK2)),k1_relat_1(sK3))
    | k1_xboole_0 = k7_relat_1(sK3,sK2) ),
    inference(duplicate_literal_removal,[],[f1104])).

fof(f1104,plain,
    ( r1_xboole_0(k1_relat_1(k7_relat_1(sK3,sK2)),k1_relat_1(sK3))
    | k1_xboole_0 = k7_relat_1(sK3,sK2)
    | r1_xboole_0(k1_relat_1(k7_relat_1(sK3,sK2)),k1_relat_1(sK3)) ),
    inference(resolution,[],[f1103,f118])).

fof(f118,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK5(X1,k1_relat_1(sK3)),sK2)
      | k1_xboole_0 = k7_relat_1(sK3,sK2)
      | r1_xboole_0(X1,k1_relat_1(sK3)) ) ),
    inference(resolution,[],[f111,f60])).

fof(f111,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_relat_1(sK3))
      | ~ r2_hidden(X4,sK2)
      | k1_xboole_0 = k7_relat_1(sK3,sK2) ) ),
    inference(resolution,[],[f61,f46])).

fof(f46,plain,
    ( r1_xboole_0(k1_relat_1(sK3),sK2)
    | k1_xboole_0 = k7_relat_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f1103,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK5(k1_relat_1(k7_relat_1(sK3,X4)),X5),X4)
      | r1_xboole_0(k1_relat_1(k7_relat_1(sK3,X4)),X5) ) ),
    inference(resolution,[],[f1092,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1092,plain,(
    ! [X0,X1] :
      ( sP0(sK3,sK5(k1_relat_1(k7_relat_1(sK3,X0)),X1),X0)
      | r1_xboole_0(k1_relat_1(k7_relat_1(sK3,X0)),X1) ) ),
    inference(resolution,[],[f529,f84])).

fof(f529,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X1,sK5(k1_relat_1(k7_relat_1(X0,X1)),X2),X0)
      | sP0(X0,sK5(k1_relat_1(k7_relat_1(X0,X1)),X2),X1)
      | r1_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X2) ) ),
    inference(resolution,[],[f66,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f47,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK3),sK2)
    | k1_xboole_0 != k7_relat_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f1691,plain,(
    r1_xboole_0(k1_relat_1(sK3),sK2) ),
    inference(subsumption_resolution,[],[f1690,f114])).

fof(f114,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f61,f51])).

fof(f51,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f1690,plain,
    ( r2_hidden(sK5(k1_relat_1(sK3),sK2),k1_xboole_0)
    | r1_xboole_0(k1_relat_1(sK3),sK2) ),
    inference(forward_demodulation,[],[f1652,f49])).

fof(f49,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f1652,plain,
    ( r2_hidden(sK5(k1_relat_1(sK3),sK2),k1_relat_1(k1_xboole_0))
    | r1_xboole_0(k1_relat_1(sK3),sK2) ),
    inference(superposition,[],[f788,f1631])).

fof(f788,plain,(
    ! [X4] :
      ( r2_hidden(sK5(k1_relat_1(sK3),X4),k1_relat_1(k7_relat_1(sK3,X4)))
      | r1_xboole_0(k1_relat_1(sK3),X4) ) ),
    inference(resolution,[],[f784,f772])).

fof(f772,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK3,X0,X1)
      | r2_hidden(X0,k1_relat_1(k7_relat_1(sK3,X1))) ) ),
    inference(resolution,[],[f67,f84])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f784,plain,(
    ! [X2,X3] :
      ( sP0(X2,sK5(k1_relat_1(X2),X3),X3)
      | r1_xboole_0(k1_relat_1(X2),X3) ) ),
    inference(duplicate_literal_removal,[],[f782])).

fof(f782,plain,(
    ! [X2,X3] :
      ( sP0(X2,sK5(k1_relat_1(X2),X3),X3)
      | r1_xboole_0(k1_relat_1(X2),X3)
      | r1_xboole_0(k1_relat_1(X2),X3) ) ),
    inference(resolution,[],[f171,f60])).

fof(f171,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(k1_relat_1(X0),X1),X2)
      | sP0(X0,sK5(k1_relat_1(X0),X1),X2)
      | r1_xboole_0(k1_relat_1(X0),X1) ) ),
    inference(resolution,[],[f70,f59])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n009.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:20:26 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.43  % (7076)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.46  % (7079)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (7077)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (7085)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (7073)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (7088)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.49  % (7078)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (7086)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (7080)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (7083)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (7075)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.50  % (7087)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.50  % (7081)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.51  % (7084)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.51  % (7089)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.51  % (7082)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.52  % (7085)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (7090)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f1741,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f1691,f1689])).
% 0.22/0.53  fof(f1689,plain,(
% 0.22/0.53    ~r1_xboole_0(k1_relat_1(sK3),sK2)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f1632])).
% 0.22/0.53  fof(f1632,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k1_relat_1(sK3),sK2)),
% 0.22/0.53    inference(backward_demodulation,[],[f47,f1631])).
% 0.22/0.53  fof(f1631,plain,(
% 0.22/0.53    k1_xboole_0 = k7_relat_1(sK3,sK2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f1630,f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.53  fof(f1630,plain,(
% 0.22/0.53    v1_xboole_0(k7_relat_1(sK3,sK2)) | k1_xboole_0 = k7_relat_1(sK3,sK2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f1629,f77])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0))) )),
% 0.22/0.53    inference(resolution,[],[f62,f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    v1_relat_1(sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    (~r1_xboole_0(k1_relat_1(sK3),sK2) | k1_xboole_0 != k7_relat_1(sK3,sK2)) & (r1_xboole_0(k1_relat_1(sK3),sK2) | k1_xboole_0 = k7_relat_1(sK3,sK2)) & v1_relat_1(sK3)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f32,f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK3),sK2) | k1_xboole_0 != k7_relat_1(sK3,sK2)) & (r1_xboole_0(k1_relat_1(sK3),sK2) | k1_xboole_0 = k7_relat_1(sK3,sK2)) & v1_relat_1(sK3))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.53    inference(negated_conjecture,[],[f15])).
% 0.22/0.53  fof(f15,conjecture,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.53  fof(f1629,plain,(
% 0.22/0.53    ~v1_relat_1(k7_relat_1(sK3,sK2)) | v1_xboole_0(k7_relat_1(sK3,sK2)) | k1_xboole_0 = k7_relat_1(sK3,sK2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f1610,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.53  fof(f1610,plain,(
% 0.22/0.53    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k7_relat_1(sK3,sK2)) | v1_xboole_0(k7_relat_1(sK3,sK2)) | k1_xboole_0 = k7_relat_1(sK3,sK2)),
% 0.22/0.53    inference(superposition,[],[f55,f1571])).
% 0.22/0.53  fof(f1571,plain,(
% 0.22/0.53    k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,sK2)) | k1_xboole_0 = k7_relat_1(sK3,sK2)),
% 0.22/0.53    inference(superposition,[],[f1554,f92])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.53    inference(forward_demodulation,[],[f72,f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f52,f56])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.53  fof(f1554,plain,(
% 0.22/0.53    ( ! [X3] : (k4_xboole_0(X3,k1_relat_1(k7_relat_1(sK3,sK2))) = X3 | k1_xboole_0 = k7_relat_1(sK3,sK2)) )),
% 0.22/0.53    inference(resolution,[],[f1525,f64])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.53  % (7074)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.53  fof(f1525,plain,(
% 0.22/0.53    ( ! [X1] : (r1_xboole_0(X1,k1_relat_1(k7_relat_1(sK3,sK2))) | k1_xboole_0 = k7_relat_1(sK3,sK2)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f1518,f1410])).
% 0.22/0.53  fof(f1410,plain,(
% 0.22/0.53    ( ! [X2,X3] : (r2_hidden(sK5(X2,k1_relat_1(k7_relat_1(sK3,X3))),k1_relat_1(sK3)) | r1_xboole_0(X2,k1_relat_1(k7_relat_1(sK3,X3)))) )),
% 0.22/0.53    inference(resolution,[],[f1283,f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,k1_relat_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ~r2_hidden(X1,k1_relat_1(X0)) | ~r2_hidden(X1,X2)) & ((r2_hidden(X1,k1_relat_1(X0)) & r2_hidden(X1,X2)) | ~sP0(X0,X1,X2)))),
% 0.22/0.53    inference(rectify,[],[f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ! [X2,X0,X1] : ((sP0(X2,X0,X1) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~sP0(X2,X0,X1)))),
% 0.22/0.53    inference(flattening,[],[f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ! [X2,X0,X1] : ((sP0(X2,X0,X1) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~sP0(X2,X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X2,X0,X1] : (sP0(X2,X0,X1) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.53  fof(f1283,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sP0(sK3,sK5(X0,k1_relat_1(k7_relat_1(sK3,X1))),X1) | r1_xboole_0(X0,k1_relat_1(k7_relat_1(sK3,X1)))) )),
% 0.22/0.53    inference(resolution,[],[f530,f84])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sP1(X0,X1,sK3)) )),
% 0.22/0.53    inference(resolution,[],[f71,f45])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | sP1(X1,X0,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (sP1(X1,X0,X2) | ~v1_relat_1(X2))),
% 0.22/0.53    inference(definition_folding,[],[f27,f29,f28])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X1,X0,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> sP0(X2,X0,X1)) | ~sP1(X1,X0,X2))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.22/0.53    inference(ennf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).
% 0.22/0.53  fof(f530,plain,(
% 0.22/0.53    ( ! [X4,X5,X3] : (~sP1(X5,sK5(X4,k1_relat_1(k7_relat_1(X3,X5))),X3) | sP0(X3,sK5(X4,k1_relat_1(k7_relat_1(X3,X5))),X5) | r1_xboole_0(X4,k1_relat_1(k7_relat_1(X3,X5)))) )),
% 0.22/0.53    inference(resolution,[],[f66,f60])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.53    inference(rectify,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0))) | sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0))) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0))))) | ~sP1(X0,X1,X2))),
% 0.22/0.53    inference(rectify,[],[f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ! [X1,X0,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~sP0(X2,X0,X1)) & (sP0(X2,X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~sP1(X1,X0,X2))),
% 0.22/0.53    inference(nnf_transformation,[],[f29])).
% 0.22/0.53  fof(f1518,plain,(
% 0.22/0.53    ( ! [X1] : (~r2_hidden(sK5(X1,k1_relat_1(k7_relat_1(sK3,sK2))),k1_relat_1(sK3)) | k1_xboole_0 = k7_relat_1(sK3,sK2) | r1_xboole_0(X1,k1_relat_1(k7_relat_1(sK3,sK2)))) )),
% 0.22/0.53    inference(resolution,[],[f1366,f60])).
% 0.22/0.53  fof(f1366,plain,(
% 0.22/0.53    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(k7_relat_1(sK3,sK2))) | ~r2_hidden(X2,k1_relat_1(sK3)) | k1_xboole_0 = k7_relat_1(sK3,sK2)) )),
% 0.22/0.53    inference(resolution,[],[f1125,f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f38])).
% 0.22/0.53  fof(f1125,plain,(
% 0.22/0.53    r1_xboole_0(k1_relat_1(k7_relat_1(sK3,sK2)),k1_relat_1(sK3)) | k1_xboole_0 = k7_relat_1(sK3,sK2)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f1104])).
% 0.22/0.53  fof(f1104,plain,(
% 0.22/0.53    r1_xboole_0(k1_relat_1(k7_relat_1(sK3,sK2)),k1_relat_1(sK3)) | k1_xboole_0 = k7_relat_1(sK3,sK2) | r1_xboole_0(k1_relat_1(k7_relat_1(sK3,sK2)),k1_relat_1(sK3))),
% 0.22/0.53    inference(resolution,[],[f1103,f118])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    ( ! [X1] : (~r2_hidden(sK5(X1,k1_relat_1(sK3)),sK2) | k1_xboole_0 = k7_relat_1(sK3,sK2) | r1_xboole_0(X1,k1_relat_1(sK3))) )),
% 0.22/0.53    inference(resolution,[],[f111,f60])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    ( ! [X4] : (~r2_hidden(X4,k1_relat_1(sK3)) | ~r2_hidden(X4,sK2) | k1_xboole_0 = k7_relat_1(sK3,sK2)) )),
% 0.22/0.53    inference(resolution,[],[f61,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    r1_xboole_0(k1_relat_1(sK3),sK2) | k1_xboole_0 = k7_relat_1(sK3,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f1103,plain,(
% 0.22/0.53    ( ! [X4,X5] : (r2_hidden(sK5(k1_relat_1(k7_relat_1(sK3,X4)),X5),X4) | r1_xboole_0(k1_relat_1(k7_relat_1(sK3,X4)),X5)) )),
% 0.22/0.53    inference(resolution,[],[f1092,f68])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f44])).
% 0.22/0.53  fof(f1092,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sP0(sK3,sK5(k1_relat_1(k7_relat_1(sK3,X0)),X1),X0) | r1_xboole_0(k1_relat_1(k7_relat_1(sK3,X0)),X1)) )),
% 0.22/0.53    inference(resolution,[],[f529,f84])).
% 0.22/0.53  fof(f529,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~sP1(X1,sK5(k1_relat_1(k7_relat_1(X0,X1)),X2),X0) | sP0(X0,sK5(k1_relat_1(k7_relat_1(X0,X1)),X2),X1) | r1_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X2)) )),
% 0.22/0.53    inference(resolution,[],[f66,f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f38])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.22/0.53    inference(flattening,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ~r1_xboole_0(k1_relat_1(sK3),sK2) | k1_xboole_0 != k7_relat_1(sK3,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f1691,plain,(
% 0.22/0.53    r1_xboole_0(k1_relat_1(sK3),sK2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f1690,f114])).
% 0.22/0.53  fof(f114,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(condensation,[],[f109])).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(resolution,[],[f61,f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.53  fof(f1690,plain,(
% 0.22/0.53    r2_hidden(sK5(k1_relat_1(sK3),sK2),k1_xboole_0) | r1_xboole_0(k1_relat_1(sK3),sK2)),
% 0.22/0.53    inference(forward_demodulation,[],[f1652,f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,axiom,(
% 0.22/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.53  fof(f1652,plain,(
% 0.22/0.53    r2_hidden(sK5(k1_relat_1(sK3),sK2),k1_relat_1(k1_xboole_0)) | r1_xboole_0(k1_relat_1(sK3),sK2)),
% 0.22/0.53    inference(superposition,[],[f788,f1631])).
% 0.22/0.53  fof(f788,plain,(
% 0.22/0.53    ( ! [X4] : (r2_hidden(sK5(k1_relat_1(sK3),X4),k1_relat_1(k7_relat_1(sK3,X4))) | r1_xboole_0(k1_relat_1(sK3),X4)) )),
% 0.22/0.53    inference(resolution,[],[f784,f772])).
% 0.22/0.53  fof(f772,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~sP0(sK3,X0,X1) | r2_hidden(X0,k1_relat_1(k7_relat_1(sK3,X1)))) )),
% 0.22/0.53    inference(resolution,[],[f67,f84])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f41])).
% 0.22/0.53  fof(f784,plain,(
% 0.22/0.53    ( ! [X2,X3] : (sP0(X2,sK5(k1_relat_1(X2),X3),X3) | r1_xboole_0(k1_relat_1(X2),X3)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f782])).
% 0.22/0.53  fof(f782,plain,(
% 0.22/0.53    ( ! [X2,X3] : (sP0(X2,sK5(k1_relat_1(X2),X3),X3) | r1_xboole_0(k1_relat_1(X2),X3) | r1_xboole_0(k1_relat_1(X2),X3)) )),
% 0.22/0.53    inference(resolution,[],[f171,f60])).
% 0.22/0.53  fof(f171,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(sK5(k1_relat_1(X0),X1),X2) | sP0(X0,sK5(k1_relat_1(X0),X1),X2) | r1_xboole_0(k1_relat_1(X0),X1)) )),
% 0.22/0.53    inference(resolution,[],[f70,f59])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_relat_1(X0)) | sP0(X0,X1,X2) | ~r2_hidden(X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f44])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (7085)------------------------------
% 0.22/0.53  % (7085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (7085)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (7085)Memory used [KB]: 2302
% 0.22/0.53  % (7085)Time elapsed: 0.102 s
% 0.22/0.53  % (7085)------------------------------
% 0.22/0.53  % (7085)------------------------------
% 0.22/0.54  % (7072)Success in time 0.171 s
%------------------------------------------------------------------------------
