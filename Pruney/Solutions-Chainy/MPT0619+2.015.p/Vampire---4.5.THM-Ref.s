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
% DateTime   : Thu Dec  3 12:51:48 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 307 expanded)
%              Number of leaves         :   14 (  86 expanded)
%              Depth                    :   16
%              Number of atoms          :  306 (1062 expanded)
%              Number of equality atoms :  155 ( 611 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f348,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f181,f185,f344,f347])).

fof(f347,plain,
    ( spl3_3
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f346])).

fof(f346,plain,
    ( $false
    | spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f345,f208])).

fof(f208,plain,(
    r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f206,f122])).

fof(f122,plain,(
    k2_relat_1(sK1) = k11_relat_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f121,f75])).

fof(f75,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f30,f35])).

fof(f35,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f30,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))
    & k1_tarski(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f20])).

fof(f20,plain,
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

fof(f13,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f121,plain,(
    k9_relat_1(sK1,k1_relat_1(sK1)) = k11_relat_1(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f30,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,sK0) = k9_relat_1(X0,k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f58,f57])).

fof(f57,plain,(
    k1_relat_1(sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f32,f55])).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f34,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f38,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f32,plain,(
    k1_tarski(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f36,f55])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f206,plain,(
    r2_hidden(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f30,f119,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(f119,plain,(
    r2_hidden(k4_tarski(sK0,k1_funct_1(sK1,sK0)),sK1) ),
    inference(unit_resulting_resolution,[],[f30,f31,f86,f67])).

fof(f67,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f86,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(superposition,[],[f69,f57])).

fof(f69,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f48,f53])).

fof(f48,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK2(X0,X1,X2,X3) != X2
              & sK2(X0,X1,X2,X3) != X1
              & sK2(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( sK2(X0,X1,X2,X3) = X2
            | sK2(X0,X1,X2,X3) = X1
            | sK2(X0,X1,X2,X3) = X0
            | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).

fof(f28,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f31,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f345,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | spl3_3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f176,f179])).

fof(f179,plain,
    ( k1_funct_1(sK1,sK0) = sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl3_4
  <=> k1_funct_1(sK1,sK0) = sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f176,plain,
    ( ~ r2_hidden(sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl3_3
  <=> r2_hidden(sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f344,plain,
    ( ~ spl3_3
    | spl3_4 ),
    inference(avatar_contradiction_clause,[],[f343])).

fof(f343,plain,
    ( $false
    | ~ spl3_3
    | spl3_4 ),
    inference(subsumption_resolution,[],[f340,f221])).

fof(f221,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1))),sK1)
    | spl3_4 ),
    inference(unit_resulting_resolution,[],[f30,f31,f180,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f180,plain,
    ( k1_funct_1(sK1,sK0) != sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f178])).

fof(f340,plain,
    ( r2_hidden(k4_tarski(sK0,sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1))),sK1)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f175,f202])).

fof(f202,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK1))
      | r2_hidden(k4_tarski(sK0,X1),sK1) ) ),
    inference(subsumption_resolution,[],[f200,f30])).

fof(f200,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK1))
      | r2_hidden(k4_tarski(sK0,X1),sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f40,f122])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f175,plain,
    ( r2_hidden(sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f174])).

fof(f185,plain,
    ( spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f182,f178,f174])).

fof(f182,plain,
    ( k1_funct_1(sK1,sK0) = sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | r2_hidden(sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X0] :
      ( k2_relat_1(sK1) != X0
      | k1_funct_1(sK1,sK0) = sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X0)
      | r2_hidden(sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,(
    ! [X0] :
      ( k2_relat_1(sK1) != X0
      | k1_funct_1(sK1,sK0) = sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X0)
      | k1_funct_1(sK1,sK0) = sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X0)
      | k1_funct_1(sK1,sK0) = sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X0)
      | r2_hidden(sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X0),X0) ) ),
    inference(superposition,[],[f56,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_enumset1(X0,X0,X0,X1,X2) = X3
      | sK2(X0,X1,X2,X3) = X2
      | sK2(X0,X1,X2,X3) = X1
      | sK2(X0,X1,X2,X3) = X0
      | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ),
    inference(definition_unfolding,[],[f49,f53])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK2(X0,X1,X2,X3) = X2
      | sK2(X0,X1,X2,X3) = X1
      | sK2(X0,X1,X2,X3) = X0
      | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
    k2_relat_1(sK1) != k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(definition_unfolding,[],[f33,f55])).

fof(f33,plain,(
    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f181,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f172,f178,f174])).

fof(f172,plain,
    ( k1_funct_1(sK1,sK0) != sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | ~ r2_hidden(sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X1] :
      ( k2_relat_1(sK1) != X1
      | k1_funct_1(sK1,sK0) != sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X1)
      | ~ r2_hidden(sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X1),X1) ) ),
    inference(superposition,[],[f56,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_enumset1(X0,X0,X0,X1,X2) = X3
      | sK2(X0,X1,X2,X3) != X0
      | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) ) ),
    inference(definition_unfolding,[],[f50,f53])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK2(X0,X1,X2,X3) != X0
      | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:45:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.50  % (26723)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.50  % (26706)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (26715)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (26701)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (26702)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (26705)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.41/0.54  % (26724)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.41/0.54  % (26703)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.41/0.54  % (26716)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.41/0.54  % (26728)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.41/0.54  % (26714)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.41/0.54  % (26722)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.41/0.54  % (26717)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.41/0.54  % (26727)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.41/0.54  % (26713)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.41/0.54  % (26720)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.54  % (26709)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.41/0.55  % (26716)Refutation not found, incomplete strategy% (26716)------------------------------
% 1.41/0.55  % (26716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (26716)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (26716)Memory used [KB]: 6268
% 1.41/0.55  % (26716)Time elapsed: 0.099 s
% 1.41/0.55  % (26716)------------------------------
% 1.41/0.55  % (26716)------------------------------
% 1.41/0.55  % (26705)Refutation not found, incomplete strategy% (26705)------------------------------
% 1.41/0.55  % (26705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (26705)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (26705)Memory used [KB]: 6268
% 1.41/0.55  % (26705)Time elapsed: 0.145 s
% 1.41/0.55  % (26705)------------------------------
% 1.41/0.55  % (26705)------------------------------
% 1.41/0.55  % (26708)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.41/0.55  % (26707)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.41/0.55  % (26718)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.41/0.55  % (26712)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.41/0.55  % (26710)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.57/0.55  % (26726)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.57/0.55  % (26725)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.57/0.55  % (26730)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.57/0.55  % (26719)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.57/0.55  % (26712)Refutation not found, incomplete strategy% (26712)------------------------------
% 1.57/0.55  % (26712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.55  % (26704)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.57/0.56  % (26711)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.57/0.56  % (26712)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.56  
% 1.57/0.56  % (26712)Memory used [KB]: 10618
% 1.57/0.56  % (26712)Time elapsed: 0.124 s
% 1.57/0.56  % (26712)------------------------------
% 1.57/0.56  % (26712)------------------------------
% 1.57/0.56  % (26711)Refutation not found, incomplete strategy% (26711)------------------------------
% 1.57/0.56  % (26711)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.56  % (26711)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.56  
% 1.57/0.56  % (26711)Memory used [KB]: 10618
% 1.57/0.56  % (26711)Time elapsed: 0.158 s
% 1.57/0.56  % (26711)------------------------------
% 1.57/0.56  % (26711)------------------------------
% 1.57/0.56  % (26722)Refutation not found, incomplete strategy% (26722)------------------------------
% 1.57/0.56  % (26722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.56  % (26722)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.56  
% 1.57/0.56  % (26722)Memory used [KB]: 1791
% 1.57/0.56  % (26722)Time elapsed: 0.157 s
% 1.57/0.56  % (26722)------------------------------
% 1.57/0.56  % (26722)------------------------------
% 1.57/0.57  % (26718)Refutation not found, incomplete strategy% (26718)------------------------------
% 1.57/0.57  % (26718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (26718)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.57  
% 1.57/0.57  % (26718)Memory used [KB]: 10746
% 1.57/0.57  % (26718)Time elapsed: 0.150 s
% 1.57/0.57  % (26718)------------------------------
% 1.57/0.57  % (26718)------------------------------
% 1.57/0.57  % (26721)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.57/0.57  % (26729)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.57/0.57  % (26727)Refutation found. Thanks to Tanya!
% 1.57/0.57  % SZS status Theorem for theBenchmark
% 1.57/0.57  % SZS output start Proof for theBenchmark
% 1.57/0.57  fof(f348,plain,(
% 1.57/0.57    $false),
% 1.57/0.57    inference(avatar_sat_refutation,[],[f181,f185,f344,f347])).
% 1.57/0.57  fof(f347,plain,(
% 1.57/0.57    spl3_3 | ~spl3_4),
% 1.57/0.57    inference(avatar_contradiction_clause,[],[f346])).
% 1.57/0.57  fof(f346,plain,(
% 1.57/0.57    $false | (spl3_3 | ~spl3_4)),
% 1.57/0.57    inference(subsumption_resolution,[],[f345,f208])).
% 1.57/0.57  fof(f208,plain,(
% 1.57/0.57    r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))),
% 1.57/0.57    inference(forward_demodulation,[],[f206,f122])).
% 1.57/0.57  fof(f122,plain,(
% 1.57/0.57    k2_relat_1(sK1) = k11_relat_1(sK1,sK0)),
% 1.57/0.57    inference(forward_demodulation,[],[f121,f75])).
% 1.57/0.57  fof(f75,plain,(
% 1.57/0.57    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1))),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f30,f35])).
% 1.57/0.57  fof(f35,plain,(
% 1.57/0.57    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f14])).
% 1.57/0.57  fof(f14,plain,(
% 1.57/0.57    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.57/0.57    inference(ennf_transformation,[],[f7])).
% 1.57/0.57  fof(f7,axiom,(
% 1.57/0.57    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 1.57/0.57  fof(f30,plain,(
% 1.57/0.57    v1_relat_1(sK1)),
% 1.57/0.57    inference(cnf_transformation,[],[f21])).
% 1.57/0.57  fof(f21,plain,(
% 1.57/0.57    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.57/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f20])).
% 1.57/0.57  fof(f20,plain,(
% 1.57/0.57    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.57/0.57    introduced(choice_axiom,[])).
% 1.57/0.57  fof(f13,plain,(
% 1.57/0.57    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.57/0.57    inference(flattening,[],[f12])).
% 1.57/0.57  fof(f12,plain,(
% 1.57/0.57    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.57/0.57    inference(ennf_transformation,[],[f11])).
% 1.57/0.57  fof(f11,negated_conjecture,(
% 1.57/0.57    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.57/0.57    inference(negated_conjecture,[],[f10])).
% 1.57/0.57  fof(f10,conjecture,(
% 1.57/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 1.57/0.57  fof(f121,plain,(
% 1.57/0.57    k9_relat_1(sK1,k1_relat_1(sK1)) = k11_relat_1(sK1,sK0)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f30,f81])).
% 1.57/0.57  fof(f81,plain,(
% 1.57/0.57    ( ! [X0] : (~v1_relat_1(X0) | k11_relat_1(X0,sK0) = k9_relat_1(X0,k1_relat_1(sK1))) )),
% 1.57/0.57    inference(superposition,[],[f58,f57])).
% 1.57/0.57  fof(f57,plain,(
% 1.57/0.57    k1_relat_1(sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.57/0.57    inference(definition_unfolding,[],[f32,f55])).
% 1.57/0.57  fof(f55,plain,(
% 1.57/0.57    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.57/0.57    inference(definition_unfolding,[],[f34,f54])).
% 1.57/0.57  fof(f54,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.57/0.57    inference(definition_unfolding,[],[f37,f53])).
% 1.57/0.57  fof(f53,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.57/0.57    inference(definition_unfolding,[],[f38,f44])).
% 1.57/0.57  fof(f44,plain,(
% 1.57/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f5])).
% 1.57/0.57  fof(f5,axiom,(
% 1.57/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.57/0.57  fof(f38,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f4])).
% 1.57/0.57  fof(f4,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.57/0.57  fof(f37,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f3])).
% 1.57/0.57  fof(f3,axiom,(
% 1.57/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.57/0.57  fof(f34,plain,(
% 1.57/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f2])).
% 1.57/0.57  fof(f2,axiom,(
% 1.57/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.57/0.57  fof(f32,plain,(
% 1.57/0.57    k1_tarski(sK0) = k1_relat_1(sK1)),
% 1.57/0.57    inference(cnf_transformation,[],[f21])).
% 1.57/0.57  fof(f58,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k3_enumset1(X1,X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 1.57/0.57    inference(definition_unfolding,[],[f36,f55])).
% 1.57/0.57  fof(f36,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f15])).
% 1.57/0.57  fof(f15,plain,(
% 1.57/0.57    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 1.57/0.57    inference(ennf_transformation,[],[f6])).
% 1.57/0.57  fof(f6,axiom,(
% 1.57/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 1.57/0.57  fof(f206,plain,(
% 1.57/0.57    r2_hidden(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0))),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f30,f119,f39])).
% 1.57/0.57  fof(f39,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f22])).
% 1.57/0.57  fof(f22,plain,(
% 1.57/0.57    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 1.57/0.57    inference(nnf_transformation,[],[f16])).
% 1.57/0.57  fof(f16,plain,(
% 1.57/0.57    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 1.57/0.57    inference(ennf_transformation,[],[f8])).
% 1.57/0.57  fof(f8,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).
% 1.57/0.57  fof(f119,plain,(
% 1.57/0.57    r2_hidden(k4_tarski(sK0,k1_funct_1(sK1,sK0)),sK1)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f30,f31,f86,f67])).
% 1.57/0.57  fof(f67,plain,(
% 1.57/0.57    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.57/0.57    inference(equality_resolution,[],[f43])).
% 1.57/0.57  fof(f43,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f24])).
% 1.57/0.57  fof(f24,plain,(
% 1.57/0.57    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.57/0.57    inference(flattening,[],[f23])).
% 1.57/0.57  fof(f23,plain,(
% 1.57/0.57    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.57/0.57    inference(nnf_transformation,[],[f18])).
% 1.57/0.57  fof(f18,plain,(
% 1.57/0.57    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.57/0.57    inference(flattening,[],[f17])).
% 1.57/0.57  fof(f17,plain,(
% 1.57/0.57    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.57/0.57    inference(ennf_transformation,[],[f9])).
% 1.57/0.57  fof(f9,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 1.57/0.57  fof(f86,plain,(
% 1.57/0.57    r2_hidden(sK0,k1_relat_1(sK1))),
% 1.57/0.57    inference(superposition,[],[f69,f57])).
% 1.57/0.57  fof(f69,plain,(
% 1.57/0.57    ( ! [X0,X5,X1] : (r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5))) )),
% 1.57/0.57    inference(equality_resolution,[],[f68])).
% 1.57/0.57  fof(f68,plain,(
% 1.57/0.57    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X5) != X3) )),
% 1.57/0.57    inference(equality_resolution,[],[f63])).
% 1.57/0.57  fof(f63,plain,(
% 1.57/0.57    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.57/0.57    inference(definition_unfolding,[],[f48,f53])).
% 1.57/0.57  fof(f48,plain,(
% 1.57/0.57    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.57/0.57    inference(cnf_transformation,[],[f29])).
% 1.57/0.57  fof(f29,plain,(
% 1.57/0.57    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.57/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).
% 1.57/0.57  fof(f28,plain,(
% 1.57/0.57    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 1.57/0.57    introduced(choice_axiom,[])).
% 1.57/0.57  fof(f27,plain,(
% 1.57/0.57    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.57/0.57    inference(rectify,[],[f26])).
% 1.57/0.57  fof(f26,plain,(
% 1.57/0.57    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.57/0.57    inference(flattening,[],[f25])).
% 1.57/0.57  fof(f25,plain,(
% 1.57/0.57    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.57/0.57    inference(nnf_transformation,[],[f19])).
% 1.57/0.57  fof(f19,plain,(
% 1.57/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.57/0.57    inference(ennf_transformation,[],[f1])).
% 1.57/0.57  fof(f1,axiom,(
% 1.57/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.57/0.57  fof(f31,plain,(
% 1.57/0.57    v1_funct_1(sK1)),
% 1.57/0.57    inference(cnf_transformation,[],[f21])).
% 1.57/0.57  fof(f345,plain,(
% 1.57/0.57    ~r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | (spl3_3 | ~spl3_4)),
% 1.57/0.57    inference(forward_demodulation,[],[f176,f179])).
% 1.57/0.57  fof(f179,plain,(
% 1.57/0.57    k1_funct_1(sK1,sK0) = sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | ~spl3_4),
% 1.57/0.57    inference(avatar_component_clause,[],[f178])).
% 1.57/0.57  fof(f178,plain,(
% 1.57/0.57    spl3_4 <=> k1_funct_1(sK1,sK0) = sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.57/0.57  fof(f176,plain,(
% 1.57/0.57    ~r2_hidden(sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) | spl3_3),
% 1.57/0.57    inference(avatar_component_clause,[],[f174])).
% 1.57/0.57  fof(f174,plain,(
% 1.57/0.57    spl3_3 <=> r2_hidden(sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.57/0.57  fof(f344,plain,(
% 1.57/0.57    ~spl3_3 | spl3_4),
% 1.57/0.57    inference(avatar_contradiction_clause,[],[f343])).
% 1.57/0.57  fof(f343,plain,(
% 1.57/0.57    $false | (~spl3_3 | spl3_4)),
% 1.57/0.57    inference(subsumption_resolution,[],[f340,f221])).
% 1.57/0.57  fof(f221,plain,(
% 1.57/0.57    ~r2_hidden(k4_tarski(sK0,sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1))),sK1) | spl3_4),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f30,f31,f180,f42])).
% 1.57/0.57  fof(f42,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f24])).
% 1.57/0.57  fof(f180,plain,(
% 1.57/0.57    k1_funct_1(sK1,sK0) != sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | spl3_4),
% 1.57/0.57    inference(avatar_component_clause,[],[f178])).
% 1.57/0.57  fof(f340,plain,(
% 1.57/0.57    r2_hidden(k4_tarski(sK0,sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1))),sK1) | ~spl3_3),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f175,f202])).
% 1.57/0.57  fof(f202,plain,(
% 1.57/0.57    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK1)) | r2_hidden(k4_tarski(sK0,X1),sK1)) )),
% 1.57/0.57    inference(subsumption_resolution,[],[f200,f30])).
% 1.57/0.57  fof(f200,plain,(
% 1.57/0.57    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK1)) | r2_hidden(k4_tarski(sK0,X1),sK1) | ~v1_relat_1(sK1)) )),
% 1.57/0.57    inference(superposition,[],[f40,f122])).
% 1.57/0.57  fof(f40,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f22])).
% 1.57/0.57  fof(f175,plain,(
% 1.57/0.57    r2_hidden(sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) | ~spl3_3),
% 1.57/0.57    inference(avatar_component_clause,[],[f174])).
% 1.57/0.57  fof(f185,plain,(
% 1.57/0.57    spl3_3 | spl3_4),
% 1.57/0.57    inference(avatar_split_clause,[],[f182,f178,f174])).
% 1.57/0.57  fof(f182,plain,(
% 1.57/0.57    k1_funct_1(sK1,sK0) = sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | r2_hidden(sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1))),
% 1.57/0.57    inference(equality_resolution,[],[f116])).
% 1.57/0.57  fof(f116,plain,(
% 1.57/0.57    ( ! [X0] : (k2_relat_1(sK1) != X0 | k1_funct_1(sK1,sK0) = sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X0) | r2_hidden(sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X0),X0)) )),
% 1.57/0.57    inference(duplicate_literal_removal,[],[f112])).
% 1.57/0.57  fof(f112,plain,(
% 1.57/0.57    ( ! [X0] : (k2_relat_1(sK1) != X0 | k1_funct_1(sK1,sK0) = sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X0) | k1_funct_1(sK1,sK0) = sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X0) | k1_funct_1(sK1,sK0) = sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X0) | r2_hidden(sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X0),X0)) )),
% 1.57/0.57    inference(superposition,[],[f56,f62])).
% 1.57/0.57  fof(f62,plain,(
% 1.57/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = X3 | sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)) )),
% 1.57/0.57    inference(definition_unfolding,[],[f49,f53])).
% 1.57/0.57  fof(f49,plain,(
% 1.57/0.57    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f29])).
% 1.57/0.57  fof(f56,plain,(
% 1.57/0.57    k2_relat_1(sK1) != k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 1.57/0.57    inference(definition_unfolding,[],[f33,f55])).
% 1.57/0.57  fof(f33,plain,(
% 1.57/0.57    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))),
% 1.57/0.57    inference(cnf_transformation,[],[f21])).
% 1.57/0.57  fof(f181,plain,(
% 1.57/0.57    ~spl3_3 | ~spl3_4),
% 1.57/0.57    inference(avatar_split_clause,[],[f172,f178,f174])).
% 1.57/0.57  fof(f172,plain,(
% 1.57/0.57    k1_funct_1(sK1,sK0) != sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | ~r2_hidden(sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1))),
% 1.57/0.57    inference(equality_resolution,[],[f113])).
% 1.57/0.57  fof(f113,plain,(
% 1.57/0.57    ( ! [X1] : (k2_relat_1(sK1) != X1 | k1_funct_1(sK1,sK0) != sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X1) | ~r2_hidden(sK2(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X1),X1)) )),
% 1.57/0.57    inference(superposition,[],[f56,f61])).
% 1.57/0.57  fof(f61,plain,(
% 1.57/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = X3 | sK2(X0,X1,X2,X3) != X0 | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) )),
% 1.57/0.57    inference(definition_unfolding,[],[f50,f53])).
% 1.57/0.57  fof(f50,plain,(
% 1.57/0.57    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK2(X0,X1,X2,X3) != X0 | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f29])).
% 1.57/0.57  % SZS output end Proof for theBenchmark
% 1.57/0.57  % (26727)------------------------------
% 1.57/0.57  % (26727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (26727)Termination reason: Refutation
% 1.57/0.57  
% 1.57/0.57  % (26727)Memory used [KB]: 10874
% 1.57/0.57  % (26727)Time elapsed: 0.161 s
% 1.57/0.57  % (26727)------------------------------
% 1.57/0.57  % (26727)------------------------------
% 1.57/0.59  % (26721)Refutation not found, incomplete strategy% (26721)------------------------------
% 1.57/0.59  % (26721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.59  % (26721)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.59  
% 1.57/0.59  % (26721)Memory used [KB]: 10746
% 1.57/0.59  % (26721)Time elapsed: 0.160 s
% 1.57/0.59  % (26721)------------------------------
% 1.57/0.59  % (26721)------------------------------
% 1.57/0.60  % (26700)Success in time 0.238 s
%------------------------------------------------------------------------------
