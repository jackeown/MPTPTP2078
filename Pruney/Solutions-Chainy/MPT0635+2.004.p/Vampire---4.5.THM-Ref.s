%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 194 expanded)
%              Number of leaves         :   16 (  59 expanded)
%              Depth                    :   15
%              Number of atoms          :  202 ( 489 expanded)
%              Number of equality atoms :   48 ( 152 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f139,plain,(
    $false ),
    inference(subsumption_resolution,[],[f138,f110])).

fof(f110,plain,(
    r2_hidden(sK2,sK3) ),
    inference(resolution,[],[f105,f82])).

fof(f82,plain,(
    r2_hidden(sK2,k1_setfam_1(k3_enumset1(sK3,sK3,sK3,sK3,k1_relat_1(sK4)))) ),
    inference(backward_demodulation,[],[f60,f61])).

fof(f61,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f40,f58,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f60,plain,(
    r2_hidden(sK2,k1_setfam_1(k3_enumset1(k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),sK3))) ),
    inference(definition_unfolding,[],[f34,f59])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f58])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f34,plain,(
    r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2)
    & r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3))
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f15,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
        & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(sK4,sK2) != k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2)
      & r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3))
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
         => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_1)).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f74,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r2_hidden(X1,X0)
          & ~ r2_hidden(X1,X2) ) )
      & ( r2_hidden(X1,X0)
        | r2_hidden(X1,X2)
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X3,X0) ) )
      & ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0)
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X3,X0) ) )
      & ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0)
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),X2,X0)
      | r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f69,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f41,f59])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_xboole_0(X2,X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f48,f63])).

fof(f63,plain,(
    ! [X0,X1] : sP1(X0,X1,k2_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f1,f20,f19])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X1,X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sP0(X1,sK5(X0,X1,X2),X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sP0(X1,sK5(X0,X1,X2),X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X1,X3,X0) )
            & ( sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f138,plain,(
    ~ r2_hidden(sK2,sK3) ),
    inference(trivial_inequality_removal,[],[f137])).

fof(f137,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(sK4,sK2)
    | ~ r2_hidden(sK2,sK3) ),
    inference(superposition,[],[f136,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).

fof(f136,plain,(
    k1_funct_1(sK4,sK2) != k1_funct_1(sK4,k1_funct_1(k6_relat_1(sK3),sK2)) ),
    inference(subsumption_resolution,[],[f135,f110])).

fof(f135,plain,
    ( ~ r2_hidden(sK2,sK3)
    | k1_funct_1(sK4,sK2) != k1_funct_1(sK4,k1_funct_1(k6_relat_1(sK3),sK2)) ),
    inference(forward_demodulation,[],[f134,f38])).

fof(f38,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f134,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(sK4,k1_funct_1(k6_relat_1(sK3),sK2))
    | ~ r2_hidden(sK2,k1_relat_1(k6_relat_1(sK3))) ),
    inference(subsumption_resolution,[],[f133,f36])).

fof(f36,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f133,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(sK4,k1_funct_1(k6_relat_1(sK3),sK2))
    | ~ r2_hidden(sK2,k1_relat_1(k6_relat_1(sK3)))
    | ~ v1_relat_1(k6_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f132,f37])).

fof(f37,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f132,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(sK4,k1_funct_1(k6_relat_1(sK3),sK2))
    | ~ r2_hidden(sK2,k1_relat_1(k6_relat_1(sK3)))
    | ~ v1_funct_1(k6_relat_1(sK3))
    | ~ v1_relat_1(k6_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f131,f32])).

fof(f32,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f131,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(sK4,k1_funct_1(k6_relat_1(sK3),sK2))
    | ~ r2_hidden(sK2,k1_relat_1(k6_relat_1(sK3)))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(k6_relat_1(sK3))
    | ~ v1_relat_1(k6_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f130,f33])).

fof(f33,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f130,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(sK4,k1_funct_1(k6_relat_1(sK3),sK2))
    | ~ r2_hidden(sK2,k1_relat_1(k6_relat_1(sK3)))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(k6_relat_1(sK3))
    | ~ v1_relat_1(k6_relat_1(sK3)) ),
    inference(superposition,[],[f35,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(f35,plain,(
    k1_funct_1(sK4,sK2) != k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:08:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (13394)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.49  % (13415)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.49  % (13390)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (13411)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.50  % (13390)Refutation not found, incomplete strategy% (13390)------------------------------
% 0.20/0.50  % (13390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (13402)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.50  % (13390)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (13390)Memory used [KB]: 10618
% 0.20/0.50  % (13390)Time elapsed: 0.084 s
% 0.20/0.50  % (13390)------------------------------
% 0.20/0.50  % (13390)------------------------------
% 0.20/0.50  % (13398)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.50  % (13391)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (13408)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.51  % (13393)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (13404)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (13398)Refutation not found, incomplete strategy% (13398)------------------------------
% 0.20/0.51  % (13398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (13398)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (13398)Memory used [KB]: 10618
% 0.20/0.51  % (13398)Time elapsed: 0.098 s
% 0.20/0.51  % (13398)------------------------------
% 0.20/0.51  % (13398)------------------------------
% 0.20/0.51  % (13395)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (13415)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f139,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(subsumption_resolution,[],[f138,f110])).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    r2_hidden(sK2,sK3)),
% 0.20/0.51    inference(resolution,[],[f105,f82])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    r2_hidden(sK2,k1_setfam_1(k3_enumset1(sK3,sK3,sK3,sK3,k1_relat_1(sK4))))),
% 0.20/0.51    inference(backward_demodulation,[],[f60,f61])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f40,f58,f58])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f43,f57])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f46,f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    r2_hidden(sK2,k1_setfam_1(k3_enumset1(k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),sK3)))),
% 0.20/0.51    inference(definition_unfolding,[],[f34,f59])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f42,f58])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3))),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    k1_funct_1(sK4,sK2) != k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2) & r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3)) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f15,f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(sK4,sK2) != k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2) & r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3)) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.51    inference(flattening,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ? [X0,X1,X2] : ((k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)))),
% 0.20/0.51    inference(negated_conjecture,[],[f12])).
% 0.20/0.51  fof(f12,conjecture,(
% 0.20/0.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_1)).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))) | r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(resolution,[],[f74,f53])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | ~r2_hidden(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (~r2_hidden(X1,X0) & ~r2_hidden(X1,X2))) & (r2_hidden(X1,X0) | r2_hidden(X1,X2) | ~sP0(X0,X1,X2)))),
% 0.20/0.51    inference(rectify,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~sP0(X1,X3,X0)))),
% 0.20/0.51    inference(flattening,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 0.20/0.51    inference(nnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X1,X3,X0] : (sP0(X1,X3,X0) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0)))),
% 0.20/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~sP0(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),X2,X0) | r2_hidden(X2,X0)) )),
% 0.20/0.51    inference(superposition,[],[f69,f62])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) = X0) )),
% 0.20/0.51    inference(definition_unfolding,[],[f41,f59])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_xboole_0(X2,X0)) | ~sP0(X0,X1,X2)) )),
% 0.20/0.51    inference(resolution,[],[f48,f63])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ( ! [X0,X1] : (sP1(X0,X1,k2_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(equality_resolution,[],[f54])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.51    inference(nnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 0.20/0.51    inference(definition_folding,[],[f1,f20,f19])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X3,X0)))),
% 0.20/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X1,X4,X0) | r2_hidden(X4,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sP0(X1,sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP0(X1,sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sP0(X1,sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.20/0.51    inference(rectify,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X3,X0)) & (sP0(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 0.20/0.51    inference(nnf_transformation,[],[f20])).
% 0.20/0.51  fof(f138,plain,(
% 0.20/0.51    ~r2_hidden(sK2,sK3)),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f137])).
% 0.20/0.51  fof(f137,plain,(
% 0.20/0.51    k1_funct_1(sK4,sK2) != k1_funct_1(sK4,sK2) | ~r2_hidden(sK2,sK3)),
% 0.20/0.51    inference(superposition,[],[f136,f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_funct_1(k6_relat_1(X1),X0) = X0 | ~r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1] : (k1_funct_1(k6_relat_1(X1),X0) = X0 | ~r2_hidden(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => k1_funct_1(k6_relat_1(X1),X0) = X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).
% 0.20/0.51  fof(f136,plain,(
% 0.20/0.51    k1_funct_1(sK4,sK2) != k1_funct_1(sK4,k1_funct_1(k6_relat_1(sK3),sK2))),
% 0.20/0.51    inference(subsumption_resolution,[],[f135,f110])).
% 0.20/0.51  fof(f135,plain,(
% 0.20/0.51    ~r2_hidden(sK2,sK3) | k1_funct_1(sK4,sK2) != k1_funct_1(sK4,k1_funct_1(k6_relat_1(sK3),sK2))),
% 0.20/0.51    inference(forward_demodulation,[],[f134,f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    k1_funct_1(sK4,sK2) != k1_funct_1(sK4,k1_funct_1(k6_relat_1(sK3),sK2)) | ~r2_hidden(sK2,k1_relat_1(k6_relat_1(sK3)))),
% 0.20/0.51    inference(subsumption_resolution,[],[f133,f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    k1_funct_1(sK4,sK2) != k1_funct_1(sK4,k1_funct_1(k6_relat_1(sK3),sK2)) | ~r2_hidden(sK2,k1_relat_1(k6_relat_1(sK3))) | ~v1_relat_1(k6_relat_1(sK3))),
% 0.20/0.51    inference(subsumption_resolution,[],[f132,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f132,plain,(
% 0.20/0.51    k1_funct_1(sK4,sK2) != k1_funct_1(sK4,k1_funct_1(k6_relat_1(sK3),sK2)) | ~r2_hidden(sK2,k1_relat_1(k6_relat_1(sK3))) | ~v1_funct_1(k6_relat_1(sK3)) | ~v1_relat_1(k6_relat_1(sK3))),
% 0.20/0.51    inference(subsumption_resolution,[],[f131,f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    v1_relat_1(sK4)),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f131,plain,(
% 0.20/0.51    k1_funct_1(sK4,sK2) != k1_funct_1(sK4,k1_funct_1(k6_relat_1(sK3),sK2)) | ~r2_hidden(sK2,k1_relat_1(k6_relat_1(sK3))) | ~v1_relat_1(sK4) | ~v1_funct_1(k6_relat_1(sK3)) | ~v1_relat_1(k6_relat_1(sK3))),
% 0.20/0.51    inference(subsumption_resolution,[],[f130,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    v1_funct_1(sK4)),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f130,plain,(
% 0.20/0.51    k1_funct_1(sK4,sK2) != k1_funct_1(sK4,k1_funct_1(k6_relat_1(sK3),sK2)) | ~r2_hidden(sK2,k1_relat_1(k6_relat_1(sK3))) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(k6_relat_1(sK3)) | ~v1_relat_1(k6_relat_1(sK3))),
% 0.20/0.51    inference(superposition,[],[f35,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(flattening,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    k1_funct_1(sK4,sK2) != k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (13415)------------------------------
% 0.20/0.51  % (13415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (13415)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (13415)Memory used [KB]: 6268
% 0.20/0.51  % (13415)Time elapsed: 0.114 s
% 0.20/0.51  % (13415)------------------------------
% 0.20/0.51  % (13415)------------------------------
% 0.20/0.51  % (13387)Success in time 0.154 s
%------------------------------------------------------------------------------
