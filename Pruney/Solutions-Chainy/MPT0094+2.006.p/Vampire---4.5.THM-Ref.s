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
% DateTime   : Thu Dec  3 12:31:45 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 217 expanded)
%              Number of leaves         :   16 (  57 expanded)
%              Depth                    :   25
%              Number of atoms          :  213 ( 684 expanded)
%              Number of equality atoms :   23 (  56 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f706,plain,(
    $false ),
    inference(subsumption_resolution,[],[f701,f73])).

fof(f73,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f47,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f701,plain,(
    ~ r1_tarski(sK2,sK2) ),
    inference(resolution,[],[f699,f36])).

fof(f36,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK1),sK2) != k4_xboole_0(k2_xboole_0(sK3,sK2),sK1)
    & r1_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k4_xboole_0(X2,X0),X1) != k4_xboole_0(k2_xboole_0(X2,X1),X0)
        & r1_xboole_0(X0,X1) )
   => ( k2_xboole_0(k4_xboole_0(sK3,sK1),sK2) != k4_xboole_0(k2_xboole_0(sK3,sK2),sK1)
      & r1_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) != k4_xboole_0(k2_xboole_0(X2,X1),X0)
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).

fof(f699,plain,(
    ! [X23] :
      ( ~ r1_xboole_0(sK1,X23)
      | ~ r1_tarski(sK2,X23) ) ),
    inference(resolution,[],[f683,f166])).

fof(f166,plain,(
    ~ r1_xboole_0(sK2,sK1) ),
    inference(trivial_inequality_removal,[],[f153])).

fof(f153,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK3,sK1),sK2)
    | ~ r1_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f37,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X2,X0),X1) = k2_xboole_0(k4_xboole_0(X2,X1),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f51,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f51,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f37,plain,(
    k2_xboole_0(k4_xboole_0(sK3,sK1),sK2) != k4_xboole_0(k2_xboole_0(sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f683,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X2,X0)
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1) ) ),
    inference(resolution,[],[f675,f343])).

fof(f343,plain,(
    ! [X0] : v1_xboole_0(k4_xboole_0(X0,X0)) ),
    inference(resolution,[],[f331,f42])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f331,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,X1)) ),
    inference(resolution,[],[f265,f73])).

fof(f265,plain,(
    ! [X21,X22,X20] :
      ( ~ r1_tarski(k4_xboole_0(X21,X22),k4_xboole_0(X22,X21))
      | ~ r2_hidden(X20,k4_xboole_0(X21,X22)) ) ),
    inference(resolution,[],[f258,f43])).

fof(f43,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_xboole_1)).

fof(f258,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X2) ) ),
    inference(subsumption_resolution,[],[f256,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f256,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f255,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X0)
        & r2_hidden(X1,X2) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X1,X2,X0] :
      ( ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ sP0(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X1,X2,X0] :
      ( ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ sP0(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f255,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X2,X0)
      | ~ r2_hidden(X2,X0)
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f251,f45])).

fof(f251,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | sP0(X1,X2,X0)
      | ~ r2_hidden(X2,X0)
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f56,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | sP0(X1,X2,X0)
      | ~ r2_hidden(X2,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X2,X0)
        & r2_hidden(X2,X1) )
      | sP0(X1,X2,X0)
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_folding,[],[f20,f21])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X2,X0)
        & r2_hidden(X2,X1) )
      | ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,X1) )
        & ~ ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) )
        & r2_hidden(X2,k2_xboole_0(X0,X1))
        & r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).

fof(f675,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_xboole_0(k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X3,X0)
      | ~ r1_tarski(X3,X2) ) ),
    inference(resolution,[],[f674,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(k3_xboole_0(X2,X1))
      | r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f52,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f39,f40])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f39,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f674,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(k3_xboole_0(X2,X1))
      | ~ v1_xboole_0(k4_xboole_0(X2,X0))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f662])).

fof(f662,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(k4_xboole_0(X2,X0))
      | ~ v1_xboole_0(k4_xboole_0(X2,X0))
      | v1_xboole_0(k3_xboole_0(X2,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f643,f48])).

fof(f643,plain,(
    ! [X6,X7,X5] :
      ( ~ v1_xboole_0(k4_xboole_0(X5,k4_xboole_0(X6,X7)))
      | ~ v1_xboole_0(k4_xboole_0(X5,X6))
      | v1_xboole_0(k3_xboole_0(X5,X7)) ) ),
    inference(superposition,[],[f635,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f635,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f630,f58])).

fof(f630,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_xboole_0(X1)
      | ~ r1_xboole_0(X1,k2_xboole_0(X1,X0))
      | ~ v1_xboole_0(k2_xboole_0(X1,X0)) ) ),
    inference(resolution,[],[f604,f58])).

fof(f604,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,k2_xboole_0(X0,X1))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0)
      | ~ r1_xboole_0(X0,k2_xboole_0(X0,X1)) ) ),
    inference(superposition,[],[f591,f48])).

fof(f591,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_xboole_0(X1,k2_xboole_0(X1,X0)))
      | v1_xboole_0(X0)
      | ~ r1_xboole_0(X0,k2_xboole_0(X1,X0)) ) ),
    inference(resolution,[],[f386,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f46,f41])).

fof(f41,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f386,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k4_xboole_0(X2,k2_xboole_0(X2,X3)),X3)
      | ~ r1_xboole_0(X3,k2_xboole_0(X2,X3))
      | v1_xboole_0(X3) ) ),
    inference(superposition,[],[f351,f44])).

fof(f351,plain,(
    ! [X6,X5] :
      ( v1_xboole_0(k2_xboole_0(k4_xboole_0(X5,k2_xboole_0(X5,X6)),X6))
      | ~ r1_xboole_0(X6,k2_xboole_0(X5,X6)) ) ),
    inference(superposition,[],[f343,f100])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:34:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (16227)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (16247)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (16243)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.52  % (16230)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (16235)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.23/0.53  % (16231)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.23/0.53  % (16228)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.23/0.53  % (16229)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.23/0.53  % (16250)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.23/0.53  % (16226)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.23/0.53  % (16236)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.23/0.54  % (16251)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.23/0.54  % (16240)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.23/0.54  % (16245)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.23/0.54  % (16239)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.23/0.54  % (16242)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.23/0.54  % (16246)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.36/0.54  % (16238)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.36/0.54  % (16252)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.54  % (16249)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.36/0.54  % (16232)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.36/0.54  % (16253)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.54  % (16241)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.36/0.54  % (16234)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.36/0.54  % (16224)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.36/0.55  % (16233)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.36/0.55  % (16237)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.36/0.55  % (16241)Refutation not found, incomplete strategy% (16241)------------------------------
% 1.36/0.55  % (16241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (16241)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (16241)Memory used [KB]: 10618
% 1.36/0.55  % (16241)Time elapsed: 0.102 s
% 1.36/0.55  % (16241)------------------------------
% 1.36/0.55  % (16241)------------------------------
% 1.36/0.55  % (16225)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.36/0.55  % (16248)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.36/0.55  % (16244)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.36/0.56  % (16246)Refutation not found, incomplete strategy% (16246)------------------------------
% 1.36/0.56  % (16246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.56  % (16246)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.56  
% 1.36/0.56  % (16246)Memory used [KB]: 10746
% 1.36/0.56  % (16246)Time elapsed: 0.143 s
% 1.36/0.56  % (16246)------------------------------
% 1.36/0.56  % (16246)------------------------------
% 1.36/0.59  % (16251)Refutation found. Thanks to Tanya!
% 1.36/0.59  % SZS status Theorem for theBenchmark
% 1.36/0.59  % SZS output start Proof for theBenchmark
% 1.36/0.59  fof(f706,plain,(
% 1.36/0.59    $false),
% 1.36/0.59    inference(subsumption_resolution,[],[f701,f73])).
% 1.36/0.59  fof(f73,plain,(
% 1.36/0.59    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.36/0.59    inference(duplicate_literal_removal,[],[f72])).
% 1.36/0.59  fof(f72,plain,(
% 1.36/0.59    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.36/0.59    inference(resolution,[],[f47,f46])).
% 1.36/0.59  fof(f46,plain,(
% 1.36/0.59    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.36/0.59    inference(cnf_transformation,[],[f32])).
% 1.36/0.59  fof(f32,plain,(
% 1.36/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.36/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).
% 1.36/0.59  fof(f31,plain,(
% 1.36/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.36/0.59    introduced(choice_axiom,[])).
% 1.36/0.59  fof(f30,plain,(
% 1.36/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.36/0.59    inference(rectify,[],[f29])).
% 1.36/0.59  fof(f29,plain,(
% 1.36/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.36/0.59    inference(nnf_transformation,[],[f18])).
% 1.36/0.59  fof(f18,plain,(
% 1.36/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.36/0.59    inference(ennf_transformation,[],[f2])).
% 1.36/0.59  fof(f2,axiom,(
% 1.36/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.36/0.59  fof(f47,plain,(
% 1.36/0.59    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.36/0.59    inference(cnf_transformation,[],[f32])).
% 1.36/0.59  fof(f701,plain,(
% 1.36/0.59    ~r1_tarski(sK2,sK2)),
% 1.36/0.59    inference(resolution,[],[f699,f36])).
% 1.36/0.59  fof(f36,plain,(
% 1.36/0.59    r1_xboole_0(sK1,sK2)),
% 1.36/0.59    inference(cnf_transformation,[],[f24])).
% 1.36/0.59  fof(f24,plain,(
% 1.36/0.59    k2_xboole_0(k4_xboole_0(sK3,sK1),sK2) != k4_xboole_0(k2_xboole_0(sK3,sK2),sK1) & r1_xboole_0(sK1,sK2)),
% 1.36/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f23])).
% 1.36/0.59  fof(f23,plain,(
% 1.36/0.59    ? [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) != k4_xboole_0(k2_xboole_0(X2,X1),X0) & r1_xboole_0(X0,X1)) => (k2_xboole_0(k4_xboole_0(sK3,sK1),sK2) != k4_xboole_0(k2_xboole_0(sK3,sK2),sK1) & r1_xboole_0(sK1,sK2))),
% 1.36/0.59    introduced(choice_axiom,[])).
% 1.36/0.59  fof(f15,plain,(
% 1.36/0.59    ? [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) != k4_xboole_0(k2_xboole_0(X2,X1),X0) & r1_xboole_0(X0,X1))),
% 1.36/0.59    inference(ennf_transformation,[],[f14])).
% 1.36/0.59  fof(f14,negated_conjecture,(
% 1.36/0.59    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0))),
% 1.36/0.59    inference(negated_conjecture,[],[f13])).
% 1.36/0.59  fof(f13,conjecture,(
% 1.36/0.59    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0))),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).
% 1.36/0.59  fof(f699,plain,(
% 1.36/0.59    ( ! [X23] : (~r1_xboole_0(sK1,X23) | ~r1_tarski(sK2,X23)) )),
% 1.36/0.59    inference(resolution,[],[f683,f166])).
% 1.36/0.59  fof(f166,plain,(
% 1.36/0.59    ~r1_xboole_0(sK2,sK1)),
% 1.36/0.59    inference(trivial_inequality_removal,[],[f153])).
% 1.36/0.59  fof(f153,plain,(
% 1.36/0.59    k2_xboole_0(k4_xboole_0(sK3,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK3,sK1),sK2) | ~r1_xboole_0(sK2,sK1)),
% 1.36/0.59    inference(superposition,[],[f37,f100])).
% 1.36/0.59  fof(f100,plain,(
% 1.36/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X2,X0),X1) = k2_xboole_0(k4_xboole_0(X2,X1),X0) | ~r1_xboole_0(X0,X1)) )),
% 1.36/0.59    inference(superposition,[],[f51,f48])).
% 1.36/0.59  fof(f48,plain,(
% 1.36/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.36/0.59    inference(cnf_transformation,[],[f33])).
% 1.36/0.59  fof(f33,plain,(
% 1.36/0.59    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.36/0.59    inference(nnf_transformation,[],[f12])).
% 1.36/0.59  fof(f12,axiom,(
% 1.36/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.36/0.59  fof(f51,plain,(
% 1.36/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 1.36/0.59    inference(cnf_transformation,[],[f7])).
% 1.36/0.59  fof(f7,axiom,(
% 1.36/0.59    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).
% 1.36/0.59  fof(f37,plain,(
% 1.36/0.59    k2_xboole_0(k4_xboole_0(sK3,sK1),sK2) != k4_xboole_0(k2_xboole_0(sK3,sK2),sK1)),
% 1.36/0.59    inference(cnf_transformation,[],[f24])).
% 1.36/0.59  fof(f683,plain,(
% 1.36/0.59    ( ! [X2,X0,X1] : (r1_xboole_0(X2,X0) | ~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1)) )),
% 1.36/0.59    inference(resolution,[],[f675,f343])).
% 1.36/0.59  fof(f343,plain,(
% 1.36/0.59    ( ! [X0] : (v1_xboole_0(k4_xboole_0(X0,X0))) )),
% 1.36/0.59    inference(resolution,[],[f331,f42])).
% 1.36/0.59  fof(f42,plain,(
% 1.36/0.59    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 1.36/0.59    inference(cnf_transformation,[],[f28])).
% 1.36/0.59  fof(f28,plain,(
% 1.36/0.59    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.36/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f27])).
% 1.36/0.59  fof(f27,plain,(
% 1.36/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.36/0.59    introduced(choice_axiom,[])).
% 1.36/0.59  fof(f26,plain,(
% 1.36/0.59    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.36/0.59    inference(rectify,[],[f25])).
% 1.36/0.59  fof(f25,plain,(
% 1.36/0.59    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.36/0.59    inference(nnf_transformation,[],[f1])).
% 1.36/0.59  fof(f1,axiom,(
% 1.36/0.59    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.36/0.59  fof(f331,plain,(
% 1.36/0.59    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X1))) )),
% 1.36/0.59    inference(resolution,[],[f265,f73])).
% 1.36/0.59  fof(f265,plain,(
% 1.36/0.59    ( ! [X21,X22,X20] : (~r1_tarski(k4_xboole_0(X21,X22),k4_xboole_0(X22,X21)) | ~r2_hidden(X20,k4_xboole_0(X21,X22))) )),
% 1.36/0.59    inference(resolution,[],[f258,f43])).
% 1.36/0.59  fof(f43,plain,(
% 1.36/0.59    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 1.36/0.59    inference(cnf_transformation,[],[f11])).
% 1.36/0.59  fof(f11,axiom,(
% 1.36/0.59    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_xboole_1)).
% 1.36/0.59  fof(f258,plain,(
% 1.36/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | ~r2_hidden(X0,X1) | ~r1_tarski(X1,X2)) )),
% 1.36/0.59    inference(subsumption_resolution,[],[f256,f45])).
% 1.36/0.59  fof(f45,plain,(
% 1.36/0.59    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 1.36/0.59    inference(cnf_transformation,[],[f32])).
% 1.36/0.59  fof(f256,plain,(
% 1.36/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.36/0.59    inference(resolution,[],[f255,f54])).
% 1.36/0.59  fof(f54,plain,(
% 1.36/0.59    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X1,X0)) )),
% 1.36/0.59    inference(cnf_transformation,[],[f35])).
% 1.36/0.59  fof(f35,plain,(
% 1.36/0.59    ! [X0,X1,X2] : ((~r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X1,X2))),
% 1.36/0.59    inference(rectify,[],[f34])).
% 1.36/0.59  fof(f34,plain,(
% 1.36/0.59    ! [X1,X2,X0] : ((~r2_hidden(X2,X1) & r2_hidden(X2,X0)) | ~sP0(X1,X2,X0))),
% 1.36/0.59    inference(nnf_transformation,[],[f21])).
% 1.36/0.59  fof(f21,plain,(
% 1.36/0.59    ! [X1,X2,X0] : ((~r2_hidden(X2,X1) & r2_hidden(X2,X0)) | ~sP0(X1,X2,X0))),
% 1.36/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.36/0.59  fof(f255,plain,(
% 1.36/0.59    ( ! [X2,X0,X1] : (sP0(X1,X2,X0) | ~r2_hidden(X2,X0) | ~r1_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 1.36/0.59    inference(subsumption_resolution,[],[f251,f45])).
% 1.36/0.59  fof(f251,plain,(
% 1.36/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | sP0(X1,X2,X0) | ~r2_hidden(X2,X0) | ~r1_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 1.36/0.59    inference(superposition,[],[f56,f44])).
% 1.36/0.59  fof(f44,plain,(
% 1.36/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.36/0.59    inference(cnf_transformation,[],[f17])).
% 1.36/0.59  fof(f17,plain,(
% 1.36/0.59    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.36/0.59    inference(ennf_transformation,[],[f6])).
% 1.36/0.59  fof(f6,axiom,(
% 1.36/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.36/0.59  fof(f56,plain,(
% 1.36/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_xboole_0(X0,X1)) | sP0(X1,X2,X0) | ~r2_hidden(X2,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.36/0.59    inference(cnf_transformation,[],[f22])).
% 1.36/0.59  fof(f22,plain,(
% 1.36/0.59    ! [X0,X1,X2] : ((~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | sP0(X1,X2,X0) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 1.36/0.59    inference(definition_folding,[],[f20,f21])).
% 1.36/0.59  fof(f20,plain,(
% 1.36/0.59    ! [X0,X1,X2] : ((~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 1.36/0.59    inference(ennf_transformation,[],[f5])).
% 1.36/0.59  fof(f5,axiom,(
% 1.36/0.59    ! [X0,X1,X2] : ~(~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & ~(~r2_hidden(X2,X1) & r2_hidden(X2,X0)) & r2_hidden(X2,k2_xboole_0(X0,X1)) & r1_xboole_0(X0,X1))),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).
% 1.36/0.59  fof(f675,plain,(
% 1.36/0.59    ( ! [X2,X0,X3,X1] : (~v1_xboole_0(k4_xboole_0(X0,X1)) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X3,X0) | ~r1_tarski(X3,X2)) )),
% 1.36/0.59    inference(resolution,[],[f674,f94])).
% 1.36/0.59  fof(f94,plain,(
% 1.36/0.59    ( ! [X2,X0,X1] : (~v1_xboole_0(k3_xboole_0(X2,X1)) | r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.36/0.59    inference(resolution,[],[f52,f58])).
% 1.36/0.59  fof(f58,plain,(
% 1.36/0.59    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.36/0.59    inference(superposition,[],[f39,f40])).
% 1.36/0.59  fof(f40,plain,(
% 1.36/0.59    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.36/0.59    inference(cnf_transformation,[],[f16])).
% 1.36/0.59  fof(f16,plain,(
% 1.36/0.59    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.36/0.59    inference(ennf_transformation,[],[f4])).
% 1.36/0.59  fof(f4,axiom,(
% 1.36/0.59    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.36/0.59  fof(f39,plain,(
% 1.36/0.59    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.36/0.59    inference(cnf_transformation,[],[f9])).
% 1.36/0.59  fof(f9,axiom,(
% 1.36/0.59    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.36/0.59  fof(f52,plain,(
% 1.36/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1)) )),
% 1.36/0.59    inference(cnf_transformation,[],[f19])).
% 1.36/0.59  fof(f19,plain,(
% 1.36/0.59    ! [X0,X1,X2] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1))),
% 1.36/0.59    inference(ennf_transformation,[],[f10])).
% 1.36/0.59  fof(f10,axiom,(
% 1.36/0.59    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).
% 1.36/0.59  fof(f674,plain,(
% 1.36/0.59    ( ! [X2,X0,X1] : (v1_xboole_0(k3_xboole_0(X2,X1)) | ~v1_xboole_0(k4_xboole_0(X2,X0)) | ~r1_xboole_0(X0,X1)) )),
% 1.36/0.59    inference(duplicate_literal_removal,[],[f662])).
% 1.36/0.59  fof(f662,plain,(
% 1.36/0.59    ( ! [X2,X0,X1] : (~v1_xboole_0(k4_xboole_0(X2,X0)) | ~v1_xboole_0(k4_xboole_0(X2,X0)) | v1_xboole_0(k3_xboole_0(X2,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.36/0.59    inference(superposition,[],[f643,f48])).
% 1.36/0.59  fof(f643,plain,(
% 1.36/0.59    ( ! [X6,X7,X5] : (~v1_xboole_0(k4_xboole_0(X5,k4_xboole_0(X6,X7))) | ~v1_xboole_0(k4_xboole_0(X5,X6)) | v1_xboole_0(k3_xboole_0(X5,X7))) )),
% 1.36/0.59    inference(superposition,[],[f635,f50])).
% 1.36/0.59  fof(f50,plain,(
% 1.36/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 1.36/0.59    inference(cnf_transformation,[],[f8])).
% 1.36/0.59  fof(f8,axiom,(
% 1.36/0.59    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 1.36/0.59  fof(f635,plain,(
% 1.36/0.59    ( ! [X0,X1] : (~v1_xboole_0(k2_xboole_0(X1,X0)) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.36/0.59    inference(subsumption_resolution,[],[f630,f58])).
% 1.36/0.59  fof(f630,plain,(
% 1.36/0.59    ( ! [X0,X1] : (v1_xboole_0(X0) | ~v1_xboole_0(X1) | ~r1_xboole_0(X1,k2_xboole_0(X1,X0)) | ~v1_xboole_0(k2_xboole_0(X1,X0))) )),
% 1.36/0.59    inference(resolution,[],[f604,f58])).
% 1.36/0.59  fof(f604,plain,(
% 1.36/0.59    ( ! [X0,X1] : (~r1_xboole_0(X1,k2_xboole_0(X0,X1)) | v1_xboole_0(X1) | ~v1_xboole_0(X0) | ~r1_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.36/0.59    inference(superposition,[],[f591,f48])).
% 1.36/0.59  fof(f591,plain,(
% 1.36/0.59    ( ! [X0,X1] : (~v1_xboole_0(k4_xboole_0(X1,k2_xboole_0(X1,X0))) | v1_xboole_0(X0) | ~r1_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 1.36/0.59    inference(resolution,[],[f386,f71])).
% 1.36/0.61  fof(f71,plain,(
% 1.36/0.61    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 1.36/0.61    inference(resolution,[],[f46,f41])).
% 1.36/0.61  fof(f41,plain,(
% 1.36/0.61    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f28])).
% 1.36/0.61  fof(f386,plain,(
% 1.36/0.61    ( ! [X2,X3] : (~r1_tarski(k4_xboole_0(X2,k2_xboole_0(X2,X3)),X3) | ~r1_xboole_0(X3,k2_xboole_0(X2,X3)) | v1_xboole_0(X3)) )),
% 1.36/0.61    inference(superposition,[],[f351,f44])).
% 1.36/0.61  fof(f351,plain,(
% 1.36/0.61    ( ! [X6,X5] : (v1_xboole_0(k2_xboole_0(k4_xboole_0(X5,k2_xboole_0(X5,X6)),X6)) | ~r1_xboole_0(X6,k2_xboole_0(X5,X6))) )),
% 1.36/0.61    inference(superposition,[],[f343,f100])).
% 1.36/0.61  % SZS output end Proof for theBenchmark
% 1.36/0.61  % (16251)------------------------------
% 1.36/0.61  % (16251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.61  % (16251)Termination reason: Refutation
% 1.36/0.61  
% 1.36/0.61  % (16251)Memory used [KB]: 6652
% 1.36/0.61  % (16251)Time elapsed: 0.190 s
% 1.36/0.61  % (16251)------------------------------
% 1.36/0.61  % (16251)------------------------------
% 1.36/0.62  % (16223)Success in time 0.244 s
%------------------------------------------------------------------------------
