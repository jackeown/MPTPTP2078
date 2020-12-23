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
% DateTime   : Thu Dec  3 12:53:38 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 284 expanded)
%              Number of leaves         :   18 (  88 expanded)
%              Depth                    :   15
%              Number of atoms          :  203 ( 626 expanded)
%              Number of equality atoms :   43 ( 199 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f305,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f91,f286,f302])).

fof(f302,plain,
    ( ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f301])).

fof(f301,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(global_subsumption,[],[f31,f256,f193])).

fof(f193,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl4_3 ),
    inference(trivial_inequality_removal,[],[f192])).

fof(f192,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl4_3 ),
    inference(superposition,[],[f42,f75])).

fof(f75,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl4_3
  <=> k1_xboole_0 = k10_relat_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) != k1_xboole_0
      | r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( k10_relat_1(X1,X0) = k1_xboole_0
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k10_relat_1(X1,X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f256,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f70,f231,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
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
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
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

fof(f231,plain,(
    ! [X0] : r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)) ),
    inference(global_subsumption,[],[f55,f230])).

fof(f230,plain,(
    ! [X0] :
      ( r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X0,X0))
      | v1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0)) ) ),
    inference(resolution,[],[f226,f37])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
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

fof(f226,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(k4_enumset1(X0,X0,X0,X0,X0,X0)),X1)
      | r2_hidden(X0,X1) ) ),
    inference(global_subsumption,[],[f55,f223])).

fof(f223,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(k4_enumset1(X0,X0,X0,X0,X0,X0)),X1)
      | r2_hidden(X0,X1)
      | v1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0)) ) ),
    inference(resolution,[],[f63,f37])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_enumset1(X0,X0,X0,X0,X0,X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f56,f41])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f52])).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f55,plain,(
    ! [X0] : ~ v1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f34,f52])).

fof(f34,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f70,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl4_2
  <=> r2_hidden(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
      | ~ r2_hidden(sK0,k2_relat_1(sK1)) )
    & ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
      | r2_hidden(sK0,k2_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
          | ~ r2_hidden(X0,k2_relat_1(X1)) )
        & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
          | r2_hidden(X0,k2_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
        | ~ r2_hidden(sK0,k2_relat_1(sK1)) )
      & ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
        | r2_hidden(sK0,k2_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k2_relat_1(X1))
        <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

fof(f286,plain,(
    ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | ~ spl4_5 ),
    inference(global_subsumption,[],[f171,f258])).

fof(f258,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f90,f231,f41])).

fof(f90,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl4_5
  <=> r1_xboole_0(k2_relat_1(sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f171,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl4_5 ),
    inference(trivial_inequality_removal,[],[f170])).

fof(f170,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f54,f169])).

fof(f169,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl4_5 ),
    inference(global_subsumption,[],[f31,f162])).

fof(f162,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl4_5 ),
    inference(resolution,[],[f90,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_relat_1(X1),X0)
      | k10_relat_1(X1,X0) = k1_xboole_0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f54,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(definition_unfolding,[],[f32,f52])).

fof(f32,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f91,plain,
    ( spl4_5
    | spl4_2 ),
    inference(avatar_split_clause,[],[f77,f69,f88])).

fof(f77,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f71,f64])).

fof(f64,plain,(
    ! [X4,X3] :
      ( r1_xboole_0(X4,k4_enumset1(X3,X3,X3,X3,X3,X3))
      | r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f56,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f71,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f76,plain,
    ( ~ spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f53,f73,f69])).

fof(f53,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(definition_unfolding,[],[f33,f52])).

fof(f33,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:16:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.41  % (10385)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.42  % (10385)Refutation found. Thanks to Tanya!
% 0.19/0.42  % SZS status Theorem for theBenchmark
% 0.19/0.42  % SZS output start Proof for theBenchmark
% 0.19/0.42  fof(f305,plain,(
% 0.19/0.42    $false),
% 0.19/0.42    inference(avatar_sat_refutation,[],[f76,f91,f286,f302])).
% 0.19/0.42  fof(f302,plain,(
% 0.19/0.42    ~spl4_2 | ~spl4_3),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f301])).
% 0.19/0.42  fof(f301,plain,(
% 0.19/0.42    $false | (~spl4_2 | ~spl4_3)),
% 0.19/0.42    inference(global_subsumption,[],[f31,f256,f193])).
% 0.19/0.42  fof(f193,plain,(
% 0.19/0.42    r1_xboole_0(k2_relat_1(sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK1) | ~spl4_3),
% 0.19/0.42    inference(trivial_inequality_removal,[],[f192])).
% 0.19/0.42  fof(f192,plain,(
% 0.19/0.42    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_relat_1(sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK1) | ~spl4_3),
% 0.19/0.42    inference(superposition,[],[f42,f75])).
% 0.19/0.42  fof(f75,plain,(
% 0.19/0.42    k1_xboole_0 = k10_relat_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl4_3),
% 0.19/0.42    inference(avatar_component_clause,[],[f73])).
% 0.19/0.42  fof(f73,plain,(
% 0.19/0.42    spl4_3 <=> k1_xboole_0 = k10_relat_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.19/0.42  fof(f42,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k10_relat_1(X1,X0) != k1_xboole_0 | r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f30])).
% 0.19/0.42  fof(f30,plain,(
% 0.19/0.42    ! [X0,X1] : (((k10_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k10_relat_1(X1,X0) != k1_xboole_0)) | ~v1_relat_1(X1))),
% 0.19/0.42    inference(nnf_transformation,[],[f17])).
% 0.19/0.42  fof(f17,plain,(
% 0.19/0.42    ! [X0,X1] : ((k10_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f11])).
% 0.19/0.42  fof(f11,axiom,(
% 0.19/0.42    ! [X0,X1] : (v1_relat_1(X1) => (k10_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 0.19/0.42  fof(f256,plain,(
% 0.19/0.42    ~r1_xboole_0(k2_relat_1(sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl4_2),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f70,f231,f41])).
% 0.19/0.42  fof(f41,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f29])).
% 0.19/0.42  fof(f29,plain,(
% 0.19/0.42    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f28])).
% 0.19/0.42  fof(f28,plain,(
% 0.19/0.42    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f16,plain,(
% 0.19/0.42    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.19/0.42    inference(ennf_transformation,[],[f14])).
% 0.19/0.42  fof(f14,plain,(
% 0.19/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.42    inference(rectify,[],[f3])).
% 0.19/0.42  fof(f3,axiom,(
% 0.19/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.19/0.42  fof(f231,plain,(
% 0.19/0.42    ( ! [X0] : (r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X0,X0))) )),
% 0.19/0.42    inference(global_subsumption,[],[f55,f230])).
% 0.19/0.42  fof(f230,plain,(
% 0.19/0.42    ( ! [X0] : (r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)) | v1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0))) )),
% 0.19/0.42    inference(resolution,[],[f226,f37])).
% 0.19/0.42  fof(f37,plain,(
% 0.19/0.42    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f27])).
% 0.19/0.42  fof(f27,plain,(
% 0.19/0.42    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).
% 0.19/0.42  fof(f26,plain,(
% 0.19/0.42    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f25,plain,(
% 0.19/0.42    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.19/0.42    inference(rectify,[],[f24])).
% 0.19/0.42  fof(f24,plain,(
% 0.19/0.42    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.19/0.42    inference(nnf_transformation,[],[f1])).
% 0.19/0.42  fof(f1,axiom,(
% 0.19/0.42    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.19/0.42  fof(f226,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~r2_hidden(sK2(k4_enumset1(X0,X0,X0,X0,X0,X0)),X1) | r2_hidden(X0,X1)) )),
% 0.19/0.42    inference(global_subsumption,[],[f55,f223])).
% 0.19/0.42  fof(f223,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~r2_hidden(sK2(k4_enumset1(X0,X0,X0,X0,X0,X0)),X1) | r2_hidden(X0,X1) | v1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0))) )),
% 0.19/0.42    inference(resolution,[],[f63,f37])).
% 0.19/0.42  fof(f63,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_enumset1(X0,X0,X0,X0,X0,X0)) | ~r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 0.19/0.42    inference(resolution,[],[f56,f41])).
% 0.19/0.42  fof(f56,plain,(
% 0.19/0.42    ( ! [X0,X1] : (r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.19/0.42    inference(definition_unfolding,[],[f44,f52])).
% 0.19/0.42  fof(f52,plain,(
% 0.19/0.42    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 0.19/0.42    inference(definition_unfolding,[],[f35,f51])).
% 0.19/0.42  fof(f51,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.19/0.42    inference(definition_unfolding,[],[f38,f50])).
% 0.19/0.42  fof(f50,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.19/0.42    inference(definition_unfolding,[],[f46,f49])).
% 0.19/0.42  fof(f49,plain,(
% 0.19/0.42    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.19/0.42    inference(definition_unfolding,[],[f47,f48])).
% 0.19/0.42  fof(f48,plain,(
% 0.19/0.42    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f8])).
% 0.19/0.42  fof(f8,axiom,(
% 0.19/0.42    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.19/0.42  fof(f47,plain,(
% 0.19/0.42    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f7])).
% 0.19/0.42  fof(f7,axiom,(
% 0.19/0.42    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.19/0.42  fof(f46,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f6])).
% 0.19/0.42  fof(f6,axiom,(
% 0.19/0.42    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.19/0.42  fof(f38,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f5])).
% 0.19/0.42  fof(f5,axiom,(
% 0.19/0.42    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.42  fof(f35,plain,(
% 0.19/0.42    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f4])).
% 0.19/0.42  fof(f4,axiom,(
% 0.19/0.42    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.42  fof(f44,plain,(
% 0.19/0.42    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f18])).
% 0.19/0.42  fof(f18,plain,(
% 0.19/0.42    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f10])).
% 0.19/0.42  fof(f10,axiom,(
% 0.19/0.42    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.19/0.42  fof(f55,plain,(
% 0.19/0.42    ( ! [X0] : (~v1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0))) )),
% 0.19/0.42    inference(definition_unfolding,[],[f34,f52])).
% 0.19/0.42  fof(f34,plain,(
% 0.19/0.42    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f9])).
% 0.19/0.42  fof(f9,axiom,(
% 0.19/0.42    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.19/0.42  fof(f70,plain,(
% 0.19/0.42    r2_hidden(sK0,k2_relat_1(sK1)) | ~spl4_2),
% 0.19/0.42    inference(avatar_component_clause,[],[f69])).
% 0.19/0.42  fof(f69,plain,(
% 0.19/0.42    spl4_2 <=> r2_hidden(sK0,k2_relat_1(sK1))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.42  fof(f31,plain,(
% 0.19/0.42    v1_relat_1(sK1)),
% 0.19/0.42    inference(cnf_transformation,[],[f23])).
% 0.19/0.42  fof(f23,plain,(
% 0.19/0.42    (k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))) & (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))) & v1_relat_1(sK1)),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).
% 0.19/0.42  fof(f22,plain,(
% 0.19/0.42    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))) & (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f21,plain,(
% 0.19/0.42    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1))),
% 0.19/0.42    inference(flattening,[],[f20])).
% 0.19/0.42  fof(f20,plain,(
% 0.19/0.42    ? [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1)))) & v1_relat_1(X1))),
% 0.19/0.42    inference(nnf_transformation,[],[f15])).
% 0.19/0.42  fof(f15,plain,(
% 0.19/0.42    ? [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))) & v1_relat_1(X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f13])).
% 0.19/0.42  fof(f13,negated_conjecture,(
% 0.19/0.42    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.19/0.42    inference(negated_conjecture,[],[f12])).
% 0.19/0.42  fof(f12,conjecture,(
% 0.19/0.42    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).
% 0.19/0.42  fof(f286,plain,(
% 0.19/0.42    ~spl4_5),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f285])).
% 0.19/0.42  fof(f285,plain,(
% 0.19/0.42    $false | ~spl4_5),
% 0.19/0.42    inference(global_subsumption,[],[f171,f258])).
% 0.19/0.42  fof(f258,plain,(
% 0.19/0.42    ~r2_hidden(sK0,k2_relat_1(sK1)) | ~spl4_5),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f90,f231,f41])).
% 0.19/0.42  fof(f90,plain,(
% 0.19/0.42    r1_xboole_0(k2_relat_1(sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl4_5),
% 0.19/0.42    inference(avatar_component_clause,[],[f88])).
% 0.19/0.42  fof(f88,plain,(
% 0.19/0.42    spl4_5 <=> r1_xboole_0(k2_relat_1(sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.19/0.42  fof(f171,plain,(
% 0.19/0.42    r2_hidden(sK0,k2_relat_1(sK1)) | ~spl4_5),
% 0.19/0.42    inference(trivial_inequality_removal,[],[f170])).
% 0.19/0.42  fof(f170,plain,(
% 0.19/0.42    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK0,k2_relat_1(sK1)) | ~spl4_5),
% 0.19/0.42    inference(forward_demodulation,[],[f54,f169])).
% 0.19/0.42  fof(f169,plain,(
% 0.19/0.42    k1_xboole_0 = k10_relat_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl4_5),
% 0.19/0.42    inference(global_subsumption,[],[f31,f162])).
% 0.19/0.42  fof(f162,plain,(
% 0.19/0.42    k1_xboole_0 = k10_relat_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK1) | ~spl4_5),
% 0.19/0.42    inference(resolution,[],[f90,f43])).
% 0.19/0.42  fof(f43,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~r1_xboole_0(k2_relat_1(X1),X0) | k10_relat_1(X1,X0) = k1_xboole_0 | ~v1_relat_1(X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f30])).
% 0.19/0.42  fof(f54,plain,(
% 0.19/0.42    k1_xboole_0 != k10_relat_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) | r2_hidden(sK0,k2_relat_1(sK1))),
% 0.19/0.42    inference(definition_unfolding,[],[f32,f52])).
% 0.19/0.42  fof(f32,plain,(
% 0.19/0.42    k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))),
% 0.19/0.42    inference(cnf_transformation,[],[f23])).
% 0.19/0.42  fof(f91,plain,(
% 0.19/0.42    spl4_5 | spl4_2),
% 0.19/0.42    inference(avatar_split_clause,[],[f77,f69,f88])).
% 0.19/0.42  fof(f77,plain,(
% 0.19/0.42    r1_xboole_0(k2_relat_1(sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) | spl4_2),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f71,f64])).
% 0.19/0.42  fof(f64,plain,(
% 0.19/0.42    ( ! [X4,X3] : (r1_xboole_0(X4,k4_enumset1(X3,X3,X3,X3,X3,X3)) | r2_hidden(X3,X4)) )),
% 0.19/0.42    inference(resolution,[],[f56,f45])).
% 0.19/0.42  fof(f45,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f19])).
% 0.19/0.42  fof(f19,plain,(
% 0.19/0.42    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f2])).
% 0.19/0.42  fof(f2,axiom,(
% 0.19/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.19/0.42  fof(f71,plain,(
% 0.19/0.42    ~r2_hidden(sK0,k2_relat_1(sK1)) | spl4_2),
% 0.19/0.42    inference(avatar_component_clause,[],[f69])).
% 0.19/0.42  fof(f76,plain,(
% 0.19/0.42    ~spl4_2 | spl4_3),
% 0.19/0.42    inference(avatar_split_clause,[],[f53,f73,f69])).
% 0.19/0.42  fof(f53,plain,(
% 0.19/0.42    k1_xboole_0 = k10_relat_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))),
% 0.19/0.42    inference(definition_unfolding,[],[f33,f52])).
% 0.19/0.42  fof(f33,plain,(
% 0.19/0.42    k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))),
% 0.19/0.42    inference(cnf_transformation,[],[f23])).
% 0.19/0.42  % SZS output end Proof for theBenchmark
% 0.19/0.42  % (10385)------------------------------
% 0.19/0.42  % (10385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.42  % (10385)Termination reason: Refutation
% 0.19/0.42  
% 0.19/0.42  % (10385)Memory used [KB]: 10874
% 0.19/0.42  % (10385)Time elapsed: 0.010 s
% 0.19/0.42  % (10385)------------------------------
% 0.19/0.42  % (10385)------------------------------
% 0.19/0.42  % (10367)Success in time 0.071 s
%------------------------------------------------------------------------------
