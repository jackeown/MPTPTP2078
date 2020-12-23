%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t138_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:50 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 118 expanded)
%              Number of leaves         :   14 (  32 expanded)
%              Depth                    :   17
%              Number of atoms          :  229 ( 483 expanded)
%              Number of equality atoms :   36 (  62 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f247,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f156,f178,f235,f246])).

fof(f246,plain,(
    ~ spl6_0 ),
    inference(avatar_contradiction_clause,[],[f243])).

fof(f243,plain,
    ( $false
    | ~ spl6_0 ),
    inference(resolution,[],[f144,f44])).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t138_relat_1.p',fc1_xboole_0)).

fof(f144,plain,
    ( ! [X7] : ~ v1_xboole_0(X7)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl6_0
  <=> ! [X7] : ~ v1_xboole_0(X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f235,plain,(
    ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f231,f44])).

fof(f231,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl6_6 ),
    inference(trivial_inequality_removal,[],[f222])).

fof(f222,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl6_6 ),
    inference(superposition,[],[f73,f214])).

fof(f214,plain,
    ( ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f208,f68])).

fof(f68,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f47,f44])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t138_relat_1.p',cc1_relat_1)).

fof(f208,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k1_xboole_0)
        | k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) )
    | ~ spl6_6 ),
    inference(resolution,[],[f155,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK1(k8_relat_1(X0,X1)),sK2(k8_relat_1(X0,X1))),X1)
      | ~ v1_relat_1(X1)
      | k1_xboole_0 = k8_relat_1(X0,X1) ) ),
    inference(subsumption_resolution,[],[f83,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t138_relat_1.p',dt_k8_relat_1)).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK1(k8_relat_1(X0,X1)),sK2(k8_relat_1(X0,X1))),X1)
      | ~ v1_relat_1(X1)
      | k1_xboole_0 = k8_relat_1(X0,X1)
      | ~ v1_relat_1(k8_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f66,f46])).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
     => r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t138_relat_1.p',t56_relat_1)).

fof(f66,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X5,X6),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f63,f50])).

fof(f63,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK5(X0,X1,X2),X0)
                  | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X1)
                    & r2_hidden(sK5(X0,X1,X2),X0) )
                  | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X1)
              & r2_hidden(X4,X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t138_relat_1.p',d12_relat_1)).

fof(f155,plain,
    ( ! [X14,X13] : ~ r2_hidden(k4_tarski(X13,X14),k1_xboole_0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl6_6
  <=> ! [X13,X14] : ~ r2_hidden(k4_tarski(X13,X14),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f73,plain,(
    ! [X0] :
      ( k8_relat_1(sK0,X0) != X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f43,f48])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t138_relat_1.p',t6_boole)).

fof(f43,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f32])).

fof(f32,plain,
    ( ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)
   => k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t138_relat_1.p',t138_relat_1)).

fof(f178,plain,(
    ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | ~ spl6_4 ),
    inference(resolution,[],[f152,f68])).

fof(f152,plain,
    ( ! [X12] : ~ v1_relat_1(X12)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl6_4
  <=> ! [X12] : ~ v1_relat_1(X12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f156,plain,
    ( spl6_0
    | spl6_4
    | spl6_6 ),
    inference(avatar_split_clause,[],[f149,f154,f151,f143])).

fof(f149,plain,(
    ! [X14,X12,X13,X11] :
      ( ~ r2_hidden(k4_tarski(X13,X14),k1_xboole_0)
      | ~ v1_relat_1(X12)
      | ~ v1_xboole_0(X11) ) ),
    inference(subsumption_resolution,[],[f136,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t138_relat_1.p',t7_boole)).

fof(f136,plain,(
    ! [X14,X12,X13,X11] :
      ( ~ r2_hidden(k4_tarski(X13,X14),k1_xboole_0)
      | r2_hidden(X14,X11)
      | ~ v1_relat_1(X12)
      | ~ v1_xboole_0(X11) ) ),
    inference(duplicate_literal_removal,[],[f133])).

fof(f133,plain,(
    ! [X14,X12,X13,X11] :
      ( ~ r2_hidden(k4_tarski(X13,X14),k1_xboole_0)
      | r2_hidden(X14,X11)
      | ~ v1_relat_1(X12)
      | ~ v1_relat_1(X12)
      | ~ v1_xboole_0(X11) ) ),
    inference(superposition,[],[f67,f119])).

fof(f119,plain,(
    ! [X4,X5] :
      ( k1_xboole_0 = k8_relat_1(X5,X4)
      | ~ v1_relat_1(X4)
      | ~ v1_xboole_0(X5) ) ),
    inference(resolution,[],[f82,f61])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | k1_xboole_0 = k8_relat_1(X0,X1) ) ),
    inference(subsumption_resolution,[],[f81,f50])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | k1_xboole_0 = k8_relat_1(X0,X1)
      | ~ v1_relat_1(k8_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f67,f46])).

fof(f67,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | r2_hidden(X6,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f64,f50])).

fof(f64,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
