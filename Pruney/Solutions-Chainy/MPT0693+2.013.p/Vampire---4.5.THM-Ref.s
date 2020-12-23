%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 807 expanded)
%              Number of leaves         :   14 ( 226 expanded)
%              Depth                    :   21
%              Number of atoms          :  271 (2457 expanded)
%              Number of equality atoms :   65 ( 786 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f445,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f334,f340,f422,f442])).

fof(f442,plain,(
    spl3_13 ),
    inference(avatar_contradiction_clause,[],[f441])).

fof(f441,plain,
    ( $false
    | spl3_13 ),
    inference(subsumption_resolution,[],[f440,f55])).

fof(f55,plain,(
    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k2_relat_1(sK1))) ),
    inference(backward_demodulation,[],[f42,f54])).

fof(f54,plain,(
    k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1) ),
    inference(resolution,[],[f27,f24])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
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

fof(f42,plain,(
    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k9_relat_1(sK1,k1_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f26,f41])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f29,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f26,plain,(
    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f440,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k2_relat_1(sK1)))
    | spl3_13 ),
    inference(subsumption_resolution,[],[f435,f344])).

fof(f344,plain,
    ( ~ r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k2_relat_1(sK1))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f343])).

fof(f343,plain,
    ( spl3_13
  <=> r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f435,plain,
    ( r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k2_relat_1(sK1))
    | k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k2_relat_1(sK1)))
    | spl3_13 ),
    inference(resolution,[],[f431,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f38,f41])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f431,plain,
    ( ! [X0] : ~ r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k9_relat_1(sK1,k10_relat_1(sK1,X0)))
    | spl3_13 ),
    inference(resolution,[],[f344,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k2_relat_1(sK1))
      | ~ r2_hidden(X1,k9_relat_1(sK1,k10_relat_1(sK1,X0))) ) ),
    inference(superposition,[],[f53,f60])).

fof(f60,plain,(
    ! [X0] : k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k1_setfam_1(k2_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),X0)) ),
    inference(subsumption_resolution,[],[f59,f24])).

fof(f59,plain,(
    ! [X0] :
      ( k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k1_setfam_1(k2_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),X0))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f58,f25])).

fof(f25,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f58,plain,(
    ! [X0] :
      ( k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k1_setfam_1(k2_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),X0))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f57,f43])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f28,f41])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f57,plain,(
    ! [X0] :
      ( k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k1_setfam_1(k2_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),X0))
      | ~ r1_tarski(k1_setfam_1(k2_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),X0)),k2_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f32,f56])).

fof(f56,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k1_setfam_1(k2_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),X0))) ),
    inference(resolution,[],[f44,f24])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f31,f41])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f34,f41])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f422,plain,
    ( ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f421])).

fof(f421,plain,
    ( $false
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f420,f55])).

fof(f420,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k2_relat_1(sK1)))
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f419,f220])).

fof(f220,plain,(
    r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),sK0) ),
    inference(trivial_inequality_removal,[],[f218])).

fof(f218,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k9_relat_1(sK1,k10_relat_1(sK1,sK0))
    | r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),sK0) ),
    inference(superposition,[],[f55,f197])).

fof(f197,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k9_relat_1(sK1,k10_relat_1(sK1,X0))
      | r2_hidden(sK2(X0,X1,k9_relat_1(sK1,k10_relat_1(sK1,X0))),X0) ) ),
    inference(factoring,[],[f139])).

fof(f139,plain,(
    ! [X24,X23,X22] :
      ( r2_hidden(sK2(X22,X23,k9_relat_1(sK1,k10_relat_1(sK1,X24))),X24)
      | k9_relat_1(sK1,k10_relat_1(sK1,X24)) = k1_setfam_1(k2_enumset1(X22,X22,X22,X23))
      | r2_hidden(sK2(X22,X23,k9_relat_1(sK1,k10_relat_1(sK1,X24))),X22) ) ),
    inference(resolution,[],[f47,f63])).

fof(f63,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k9_relat_1(sK1,k10_relat_1(sK1,X2)))
      | r2_hidden(X3,X2) ) ),
    inference(superposition,[],[f52,f60])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f35,f41])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f37,f41])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f419,plain,
    ( ~ r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),sK0)
    | k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k2_relat_1(sK1)))
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f409,f345])).

fof(f345,plain,
    ( r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k2_relat_1(sK1))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f343])).

fof(f409,plain,
    ( ~ r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k2_relat_1(sK1))
    | ~ r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),sK0)
    | k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k2_relat_1(sK1)))
    | ~ spl3_12 ),
    inference(resolution,[],[f339,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f39,f41])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f339,plain,
    ( r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f337])).

fof(f337,plain,
    ( spl3_12
  <=> r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f340,plain,
    ( spl3_7
    | spl3_12 ),
    inference(avatar_split_clause,[],[f335,f337,f235])).

fof(f235,plain,
    ( spl3_7
  <=> ! [X0] : ~ r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k9_relat_1(sK1,k10_relat_1(sK1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f335,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
      | ~ r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k9_relat_1(sK1,k10_relat_1(sK1,X0))) ) ),
    inference(forward_demodulation,[],[f330,f60])).

fof(f330,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k1_setfam_1(k2_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),sK0)))
      | ~ r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k9_relat_1(sK1,k10_relat_1(sK1,X0))) ) ),
    inference(resolution,[],[f223,f62])).

fof(f223,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),X1)
      | r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k1_setfam_1(k2_enumset1(X1,X1,X1,sK0))) ) ),
    inference(resolution,[],[f220,f51])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | r2_hidden(X4,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f36,f41])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f334,plain,(
    ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f333])).

fof(f333,plain,
    ( $false
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f332,f236])).

fof(f236,plain,
    ( ! [X0] : ~ r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k9_relat_1(sK1,k10_relat_1(sK1,X0)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f235])).

fof(f332,plain,
    ( r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f329,f60])).

fof(f329,plain,
    ( r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k1_setfam_1(k2_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),sK0)))
    | ~ spl3_7 ),
    inference(resolution,[],[f223,f255])).

fof(f255,plain,
    ( r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k2_relat_1(sK1))
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f251,f55])).

fof(f251,plain,
    ( r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k2_relat_1(sK1))
    | k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k2_relat_1(sK1)))
    | ~ spl3_7 ),
    inference(resolution,[],[f236,f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n011.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:01:42 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.51  % (4256)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (4248)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (4239)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (4239)Refutation not found, incomplete strategy% (4239)------------------------------
% 0.21/0.53  % (4239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4239)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (4239)Memory used [KB]: 10618
% 0.21/0.53  % (4239)Time elapsed: 0.099 s
% 0.21/0.53  % (4239)------------------------------
% 0.21/0.53  % (4239)------------------------------
% 0.21/0.54  % (4227)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (4232)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (4231)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (4228)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (4233)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (4241)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (4238)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (4255)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (4235)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (4257)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (4247)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (4244)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (4246)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (4244)Refutation not found, incomplete strategy% (4244)------------------------------
% 0.21/0.55  % (4244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (4244)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (4244)Memory used [KB]: 6140
% 0.21/0.55  % (4244)Time elapsed: 0.002 s
% 0.21/0.55  % (4244)------------------------------
% 0.21/0.55  % (4244)------------------------------
% 0.21/0.55  % (4246)Refutation not found, incomplete strategy% (4246)------------------------------
% 0.21/0.55  % (4246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (4246)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (4246)Memory used [KB]: 10618
% 0.21/0.55  % (4246)Time elapsed: 0.127 s
% 0.21/0.55  % (4246)------------------------------
% 0.21/0.55  % (4246)------------------------------
% 0.21/0.55  % (4249)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (4229)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (4253)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (4229)Refutation not found, incomplete strategy% (4229)------------------------------
% 0.21/0.55  % (4229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (4229)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (4229)Memory used [KB]: 10618
% 0.21/0.55  % (4229)Time elapsed: 0.135 s
% 0.21/0.55  % (4229)------------------------------
% 0.21/0.55  % (4229)------------------------------
% 0.21/0.55  % (4250)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (4249)Refutation not found, incomplete strategy% (4249)------------------------------
% 0.21/0.55  % (4249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (4249)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (4249)Memory used [KB]: 10746
% 0.21/0.55  % (4249)Time elapsed: 0.140 s
% 0.21/0.55  % (4249)------------------------------
% 0.21/0.55  % (4249)------------------------------
% 0.21/0.55  % (4232)Refutation not found, incomplete strategy% (4232)------------------------------
% 0.21/0.55  % (4232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (4232)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (4232)Memory used [KB]: 6140
% 0.21/0.55  % (4232)Time elapsed: 0.134 s
% 0.21/0.55  % (4232)------------------------------
% 0.21/0.55  % (4232)------------------------------
% 0.21/0.55  % (4240)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (4237)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (4238)Refutation not found, incomplete strategy% (4238)------------------------------
% 0.21/0.55  % (4238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (4238)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (4238)Memory used [KB]: 10618
% 0.21/0.55  % (4238)Time elapsed: 0.140 s
% 0.21/0.55  % (4238)------------------------------
% 0.21/0.55  % (4238)------------------------------
% 0.21/0.55  % (4233)Refutation not found, incomplete strategy% (4233)------------------------------
% 0.21/0.55  % (4233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (4233)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (4233)Memory used [KB]: 6140
% 0.21/0.55  % (4233)Time elapsed: 0.136 s
% 0.21/0.55  % (4233)------------------------------
% 0.21/0.55  % (4233)------------------------------
% 0.21/0.56  % (4237)Refutation not found, incomplete strategy% (4237)------------------------------
% 0.21/0.56  % (4237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (4237)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (4237)Memory used [KB]: 10618
% 0.21/0.56  % (4237)Time elapsed: 0.140 s
% 0.21/0.56  % (4237)------------------------------
% 0.21/0.56  % (4237)------------------------------
% 0.21/0.56  % (4227)Refutation not found, incomplete strategy% (4227)------------------------------
% 0.21/0.56  % (4227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (4227)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (4227)Memory used [KB]: 1663
% 0.21/0.56  % (4227)Time elapsed: 0.134 s
% 0.21/0.56  % (4227)------------------------------
% 0.21/0.56  % (4227)------------------------------
% 0.21/0.56  % (4254)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (4236)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (4258)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (4252)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.56  % (4236)Refutation not found, incomplete strategy% (4236)------------------------------
% 0.21/0.56  % (4236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (4236)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (4236)Memory used [KB]: 10618
% 0.21/0.56  % (4236)Time elapsed: 0.139 s
% 0.21/0.56  % (4236)------------------------------
% 0.21/0.56  % (4236)------------------------------
% 0.21/0.56  % (4245)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (4251)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (4234)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.56  % (4243)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (4251)Refutation not found, incomplete strategy% (4251)------------------------------
% 0.21/0.56  % (4251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (4251)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (4251)Memory used [KB]: 10746
% 0.21/0.56  % (4251)Time elapsed: 0.069 s
% 0.21/0.56  % (4251)------------------------------
% 0.21/0.56  % (4251)------------------------------
% 0.21/0.57  % (4231)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f445,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f334,f340,f422,f442])).
% 0.21/0.57  fof(f442,plain,(
% 0.21/0.57    spl3_13),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f441])).
% 0.21/0.57  fof(f441,plain,(
% 0.21/0.57    $false | spl3_13),
% 0.21/0.57    inference(subsumption_resolution,[],[f440,f55])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k2_relat_1(sK1)))),
% 0.21/0.57    inference(backward_demodulation,[],[f42,f54])).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1)),
% 0.21/0.57    inference(resolution,[],[f27,f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    v1_relat_1(sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) & v1_funct_1(X1) & v1_relat_1(X1)) => (k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f12,plain,(
% 0.21/0.57    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.57    inference(flattening,[],[f11])).
% 0.21/0.57  fof(f11,plain,(
% 0.21/0.57    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 0.21/0.57    inference(negated_conjecture,[],[f9])).
% 0.21/0.57  fof(f9,conjecture,(
% 0.21/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,plain,(
% 0.21/0.57    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k9_relat_1(sK1,k1_relat_1(sK1))))),
% 0.21/0.57    inference(definition_unfolding,[],[f26,f41])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f29,f40])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f30,f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f440,plain,(
% 0.21/0.57    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k2_relat_1(sK1))) | spl3_13),
% 0.21/0.57    inference(subsumption_resolution,[],[f435,f344])).
% 0.21/0.57  fof(f344,plain,(
% 0.21/0.57    ~r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k2_relat_1(sK1)) | spl3_13),
% 0.21/0.57    inference(avatar_component_clause,[],[f343])).
% 0.21/0.57  fof(f343,plain,(
% 0.21/0.57    spl3_13 <=> r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k2_relat_1(sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.57  fof(f435,plain,(
% 0.21/0.57    r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k2_relat_1(sK1)) | k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k2_relat_1(sK1))) | spl3_13),
% 0.21/0.57    inference(resolution,[],[f431,f46])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X1) | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2) )),
% 0.21/0.57    inference(definition_unfolding,[],[f38,f41])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.57    inference(rectify,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.57    inference(flattening,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.57    inference(nnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.57  fof(f431,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k9_relat_1(sK1,k10_relat_1(sK1,X0)))) ) | spl3_13),
% 0.21/0.57    inference(resolution,[],[f344,f62])).
% 0.21/0.57  fof(f62,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(X1,k2_relat_1(sK1)) | ~r2_hidden(X1,k9_relat_1(sK1,k10_relat_1(sK1,X0)))) )),
% 0.21/0.57    inference(superposition,[],[f53,f60])).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    ( ! [X0] : (k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k1_setfam_1(k2_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),X0))) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f59,f24])).
% 0.21/0.57  fof(f59,plain,(
% 0.21/0.57    ( ! [X0] : (k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k1_setfam_1(k2_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),X0)) | ~v1_relat_1(sK1)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f58,f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    v1_funct_1(sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f58,plain,(
% 0.21/0.57    ( ! [X0] : (k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k1_setfam_1(k2_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),X0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f57,f43])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f28,f41])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.57  fof(f57,plain,(
% 0.21/0.57    ( ! [X0] : (k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k1_setfam_1(k2_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),X0)) | ~r1_tarski(k1_setfam_1(k2_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),X0)),k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.21/0.57    inference(superposition,[],[f32,f56])).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    ( ! [X0] : (k10_relat_1(sK1,X0) = k10_relat_1(sK1,k1_setfam_1(k2_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),X0)))) )),
% 0.21/0.57    inference(resolution,[],[f44,f24])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0)))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f31,f41])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(flattening,[],[f15])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | r2_hidden(X4,X0)) )),
% 0.21/0.57    inference(equality_resolution,[],[f50])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) != X2) )),
% 0.21/0.57    inference(definition_unfolding,[],[f34,f41])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f422,plain,(
% 0.21/0.57    ~spl3_12 | ~spl3_13),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f421])).
% 0.21/0.57  fof(f421,plain,(
% 0.21/0.57    $false | (~spl3_12 | ~spl3_13)),
% 0.21/0.57    inference(subsumption_resolution,[],[f420,f55])).
% 0.21/0.57  fof(f420,plain,(
% 0.21/0.57    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k2_relat_1(sK1))) | (~spl3_12 | ~spl3_13)),
% 0.21/0.57    inference(subsumption_resolution,[],[f419,f220])).
% 0.21/0.57  fof(f220,plain,(
% 0.21/0.57    r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),sK0)),
% 0.21/0.57    inference(trivial_inequality_removal,[],[f218])).
% 0.21/0.57  fof(f218,plain,(
% 0.21/0.57    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k9_relat_1(sK1,k10_relat_1(sK1,sK0)) | r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),sK0)),
% 0.21/0.57    inference(superposition,[],[f55,f197])).
% 0.21/0.57  fof(f197,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k9_relat_1(sK1,k10_relat_1(sK1,X0)) | r2_hidden(sK2(X0,X1,k9_relat_1(sK1,k10_relat_1(sK1,X0))),X0)) )),
% 0.21/0.57    inference(factoring,[],[f139])).
% 0.21/0.57  fof(f139,plain,(
% 0.21/0.57    ( ! [X24,X23,X22] : (r2_hidden(sK2(X22,X23,k9_relat_1(sK1,k10_relat_1(sK1,X24))),X24) | k9_relat_1(sK1,k10_relat_1(sK1,X24)) = k1_setfam_1(k2_enumset1(X22,X22,X22,X23)) | r2_hidden(sK2(X22,X23,k9_relat_1(sK1,k10_relat_1(sK1,X24))),X22)) )),
% 0.21/0.57    inference(resolution,[],[f47,f63])).
% 0.21/0.57  fof(f63,plain,(
% 0.21/0.57    ( ! [X2,X3] : (~r2_hidden(X3,k9_relat_1(sK1,k10_relat_1(sK1,X2))) | r2_hidden(X3,X2)) )),
% 0.21/0.57    inference(superposition,[],[f52,f60])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | r2_hidden(X4,X1)) )),
% 0.21/0.57    inference(equality_resolution,[],[f49])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) != X2) )),
% 0.21/0.57    inference(definition_unfolding,[],[f35,f41])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2) )),
% 0.21/0.57    inference(definition_unfolding,[],[f37,f41])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f419,plain,(
% 0.21/0.57    ~r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),sK0) | k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k2_relat_1(sK1))) | (~spl3_12 | ~spl3_13)),
% 0.21/0.57    inference(subsumption_resolution,[],[f409,f345])).
% 0.21/0.57  fof(f345,plain,(
% 0.21/0.57    r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k2_relat_1(sK1)) | ~spl3_13),
% 0.21/0.57    inference(avatar_component_clause,[],[f343])).
% 0.21/0.57  fof(f409,plain,(
% 0.21/0.57    ~r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k2_relat_1(sK1)) | ~r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),sK0) | k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k2_relat_1(sK1))) | ~spl3_12),
% 0.21/0.57    inference(resolution,[],[f339,f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2) )),
% 0.21/0.57    inference(definition_unfolding,[],[f39,f41])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f339,plain,(
% 0.21/0.57    r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k9_relat_1(sK1,k10_relat_1(sK1,sK0))) | ~spl3_12),
% 0.21/0.57    inference(avatar_component_clause,[],[f337])).
% 0.21/0.57  fof(f337,plain,(
% 0.21/0.57    spl3_12 <=> r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k9_relat_1(sK1,k10_relat_1(sK1,sK0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.57  fof(f340,plain,(
% 0.21/0.57    spl3_7 | spl3_12),
% 0.21/0.57    inference(avatar_split_clause,[],[f335,f337,f235])).
% 0.21/0.57  fof(f235,plain,(
% 0.21/0.57    spl3_7 <=> ! [X0] : ~r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k9_relat_1(sK1,k10_relat_1(sK1,X0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.57  fof(f335,plain,(
% 0.21/0.57    ( ! [X0] : (r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k9_relat_1(sK1,k10_relat_1(sK1,sK0))) | ~r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k9_relat_1(sK1,k10_relat_1(sK1,X0)))) )),
% 0.21/0.57    inference(forward_demodulation,[],[f330,f60])).
% 0.21/0.57  fof(f330,plain,(
% 0.21/0.57    ( ! [X0] : (r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k1_setfam_1(k2_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),sK0))) | ~r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k9_relat_1(sK1,k10_relat_1(sK1,X0)))) )),
% 0.21/0.57    inference(resolution,[],[f223,f62])).
% 0.21/0.57  fof(f223,plain,(
% 0.21/0.57    ( ! [X1] : (~r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),X1) | r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k1_setfam_1(k2_enumset1(X1,X1,X1,sK0)))) )),
% 0.21/0.57    inference(resolution,[],[f220,f51])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | r2_hidden(X4,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 0.21/0.57    inference(equality_resolution,[],[f48])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) != X2) )),
% 0.21/0.57    inference(definition_unfolding,[],[f36,f41])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f334,plain,(
% 0.21/0.57    ~spl3_7),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f333])).
% 0.21/0.57  fof(f333,plain,(
% 0.21/0.57    $false | ~spl3_7),
% 0.21/0.57    inference(subsumption_resolution,[],[f332,f236])).
% 0.21/0.57  fof(f236,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k9_relat_1(sK1,k10_relat_1(sK1,X0)))) ) | ~spl3_7),
% 0.21/0.57    inference(avatar_component_clause,[],[f235])).
% 0.21/0.57  fof(f332,plain,(
% 0.21/0.57    r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k9_relat_1(sK1,k10_relat_1(sK1,sK0))) | ~spl3_7),
% 0.21/0.57    inference(forward_demodulation,[],[f329,f60])).
% 0.21/0.57  fof(f329,plain,(
% 0.21/0.57    r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k1_setfam_1(k2_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),sK0))) | ~spl3_7),
% 0.21/0.57    inference(resolution,[],[f223,f255])).
% 0.21/0.57  fof(f255,plain,(
% 0.21/0.57    r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k2_relat_1(sK1)) | ~spl3_7),
% 0.21/0.57    inference(subsumption_resolution,[],[f251,f55])).
% 0.21/0.57  fof(f251,plain,(
% 0.21/0.57    r2_hidden(sK2(sK0,k2_relat_1(sK1),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k2_relat_1(sK1)) | k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k2_relat_1(sK1))) | ~spl3_7),
% 0.21/0.57    inference(resolution,[],[f236,f46])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (4231)------------------------------
% 0.21/0.57  % (4231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (4231)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (4231)Memory used [KB]: 11001
% 0.21/0.57  % (4231)Time elapsed: 0.150 s
% 0.21/0.57  % (4231)------------------------------
% 0.21/0.57  % (4231)------------------------------
% 0.21/0.57  % (4224)Success in time 0.201 s
%------------------------------------------------------------------------------
