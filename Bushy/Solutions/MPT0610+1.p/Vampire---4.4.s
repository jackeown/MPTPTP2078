%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t214_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:59 EDT 2019

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 117 expanded)
%              Number of leaves         :   14 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  213 ( 487 expanded)
%              Number of equality atoms :   15 (  30 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8242,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f5491,f6407,f8241])).

fof(f8241,plain,(
    ~ spl9_108 ),
    inference(avatar_contradiction_clause,[],[f8240])).

fof(f8240,plain,
    ( $false
    | ~ spl9_108 ),
    inference(subsumption_resolution,[],[f8239,f51])).

fof(f51,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_xboole_0(X0,X1)
            & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_xboole_0(sK0,X1)
          & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
     => ( ~ r1_xboole_0(X0,sK1)
        & r1_xboole_0(k1_relat_1(X0),k1_relat_1(sK1))
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
             => r1_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
           => r1_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t214_relat_1.p',t214_relat_1)).

fof(f8239,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl9_108 ),
    inference(resolution,[],[f7237,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t214_relat_1.p',symmetry_r1_xboole_0)).

fof(f7237,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl9_108 ),
    inference(subsumption_resolution,[],[f7235,f49])).

fof(f49,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f7235,plain,
    ( ~ v1_relat_1(sK1)
    | r1_xboole_0(sK1,sK0)
    | ~ spl9_108 ),
    inference(resolution,[],[f5490,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t214_relat_1.p',t3_xboole_0)).

fof(f5490,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK5(sK1,sK0),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl9_108 ),
    inference(avatar_component_clause,[],[f5489])).

fof(f5489,plain,
    ( spl9_108
  <=> ! [X1] :
        ( ~ r2_hidden(sK5(sK1,sK0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_108])])).

fof(f6407,plain,(
    ~ spl9_106 ),
    inference(avatar_contradiction_clause,[],[f6406])).

fof(f6406,plain,
    ( $false
    | ~ spl9_106 ),
    inference(subsumption_resolution,[],[f6405,f51])).

fof(f6405,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl9_106 ),
    inference(resolution,[],[f5487,f60])).

fof(f5487,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl9_106 ),
    inference(avatar_component_clause,[],[f5486])).

fof(f5486,plain,
    ( spl9_106
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_106])])).

fof(f5491,plain,
    ( spl9_106
    | spl9_108
    | spl9_108 ),
    inference(avatar_split_clause,[],[f5484,f5489,f5489,f5486])).

fof(f5484,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(sK5(sK1,sK0),X0)
      | ~ r2_hidden(sK5(sK1,sK0),X1)
      | ~ v1_relat_1(X1)
      | r1_xboole_0(sK1,sK0) ) ),
    inference(duplicate_literal_removal,[],[f5483])).

fof(f5483,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(sK5(sK1,sK0),X0)
      | ~ r2_hidden(sK5(sK1,sK0),X1)
      | ~ v1_relat_1(X1)
      | r1_xboole_0(sK1,sK0)
      | r1_xboole_0(sK1,sK0) ) ),
    inference(resolution,[],[f3365,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f3365,plain,(
    ! [X10,X8,X9] :
      ( ~ r2_hidden(sK5(sK1,X8),sK0)
      | ~ v1_relat_1(X9)
      | ~ r2_hidden(sK5(sK1,X8),X9)
      | ~ r2_hidden(sK5(sK1,X8),X10)
      | ~ v1_relat_1(X10)
      | r1_xboole_0(sK1,X8) ) ),
    inference(resolution,[],[f3304,f56])).

fof(f3304,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X1,X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X1,X2)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f389,f50])).

fof(f50,plain,(
    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f389,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_xboole_0(k1_relat_1(X2),k1_relat_1(X3))
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X3)
      | ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X4)
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f133,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0),k1_relat_1(X1))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f69,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_tarski(sK2(X1),sK3(X1)) = X1
      | ~ r2_hidden(X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_tarski(sK2(X1),sK3(X1)) = X1
          | ~ r2_hidden(X1,X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f36])).

fof(f36,plain,(
    ! [X1] :
      ( ? [X2,X3] : k4_tarski(X2,X3) = X1
     => k4_tarski(sK2(X1),sK3(X1)) = X1 ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t214_relat_1.p',d1_relat_1)).

fof(f69,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f43,f46,f45,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t214_relat_1.p',d4_relat_1)).

fof(f133,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r2_hidden(sK2(X3),X6)
      | ~ r2_hidden(X3,X5)
      | ~ v1_relat_1(X5)
      | ~ r1_xboole_0(X6,k1_relat_1(X4))
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f90,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
