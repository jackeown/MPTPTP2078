%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t67_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:04 EDT 2019

% Result     : Theorem 4.95s
% Output     : Refutation 4.95s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 199 expanded)
%              Number of leaves         :   29 (  67 expanded)
%              Depth                    :   14
%              Number of atoms          :  477 ( 857 expanded)
%              Number of equality atoms :   59 ( 137 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3225,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f206,f213,f2400,f3224])).

fof(f3224,plain,
    ( ~ spl17_2
    | ~ spl17_18 ),
    inference(avatar_contradiction_clause,[],[f3208])).

fof(f3208,plain,
    ( $false
    | ~ spl17_2
    | ~ spl17_18 ),
    inference(unit_resulting_resolution,[],[f1008,f1036,f3199,f312])).

fof(f312,plain,(
    ! [X10,X11,X9] :
      ( ~ v1_xboole_0(k3_xboole_0(X11,X10))
      | ~ r2_hidden(X9,X11)
      | ~ r2_hidden(X9,X10) ) ),
    inference(resolution,[],[f122,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t67_relat_1.p',t7_boole)).

fof(f122,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK15(X0,X1,X2),X1)
            | ~ r2_hidden(sK15(X0,X1,X2),X0)
            | ~ r2_hidden(sK15(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK15(X0,X1,X2),X1)
              & r2_hidden(sK15(X0,X1,X2),X0) )
            | r2_hidden(sK15(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f72,f73])).

fof(f73,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK15(X0,X1,X2),X1)
          | ~ r2_hidden(sK15(X0,X1,X2),X0)
          | ~ r2_hidden(sK15(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK15(X0,X1,X2),X1)
            & r2_hidden(sK15(X0,X1,X2),X0) )
          | r2_hidden(sK15(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
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
    inference(rectify,[],[f71])).

fof(f71,plain,(
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
    inference(flattening,[],[f70])).

fof(f70,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t67_relat_1.p',d4_xboole_0)).

fof(f3199,plain,
    ( v1_xboole_0(k3_xboole_0(k2_relat_1(sK0),k1_relat_1(sK1)))
    | ~ spl17_18 ),
    inference(resolution,[],[f2487,f77])).

fof(f77,plain,(
    r1_xboole_0(k2_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( k5_relat_1(sK0,sK1) != k1_xboole_0
    & r1_xboole_0(k2_relat_1(sK0),k1_relat_1(sK1))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f45,f44])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k5_relat_1(X0,X1) != k1_xboole_0
            & r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k5_relat_1(sK0,X1) != k1_xboole_0
          & r1_xboole_0(k2_relat_1(sK0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k5_relat_1(X0,X1) != k1_xboole_0
          & r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
     => ( k5_relat_1(X0,sK1) != k1_xboole_0
        & r1_xboole_0(k2_relat_1(X0),k1_relat_1(sK1))
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k5_relat_1(X0,X1) != k1_xboole_0
          & r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k5_relat_1(X0,X1) != k1_xboole_0
          & r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
             => k5_relat_1(X0,X1) = k1_xboole_0 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
           => k5_relat_1(X0,X1) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t67_relat_1.p',t67_relat_1)).

fof(f2487,plain,
    ( ! [X2,X1] :
        ( ~ r1_xboole_0(X1,X2)
        | v1_xboole_0(k3_xboole_0(X1,X2)) )
    | ~ spl17_18 ),
    inference(resolution,[],[f2402,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( sQ16_eqProxy(k1_xboole_0,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f97,f125])).

fof(f125,plain,(
    ! [X1,X0] :
      ( sQ16_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ16_eqProxy])])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k3_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k3_xboole_0(X0,X1) )
      & ( k1_xboole_0 = k3_xboole_0(X0,X1)
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k1_xboole_0 = k3_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t67_relat_1.p',d7_xboole_0)).

fof(f2402,plain,
    ( ! [X1] :
        ( ~ sQ16_eqProxy(k1_xboole_0,X1)
        | v1_xboole_0(X1) )
    | ~ spl17_18 ),
    inference(resolution,[],[f2362,f167])).

fof(f167,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ sQ16_eqProxy(X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(equality_proxy_axiom,[],[f125])).

fof(f2362,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl17_18 ),
    inference(avatar_component_clause,[],[f2361])).

fof(f2361,plain,
    ( spl17_18
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_18])])).

fof(f1036,plain,
    ( r2_hidden(sK7(sK0,sK1,sK2(k5_relat_1(sK0,sK1)),sK3(k5_relat_1(sK0,sK1))),k2_relat_1(sK0))
    | ~ spl17_2 ),
    inference(resolution,[],[f251,f120])).

fof(f120,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK12(X0,X1)),X0)
            | ~ r2_hidden(sK12(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK13(X0,X1),sK12(X0,X1)),X0)
            | r2_hidden(sK12(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK14(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13,sK14])],[f65,f68,f67,f66])).

fof(f66,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK12(X0,X1)),X0)
          | ~ r2_hidden(sK12(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK12(X0,X1)),X0)
          | r2_hidden(sK12(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK13(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK14(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t67_relat_1.p',d5_relat_1)).

fof(f251,plain,
    ( r2_hidden(k4_tarski(sK2(k5_relat_1(sK0,sK1)),sK7(sK0,sK1,sK2(k5_relat_1(sK0,sK1)),sK3(k5_relat_1(sK0,sK1)))),sK0)
    | ~ spl17_2 ),
    inference(subsumption_resolution,[],[f250,f75])).

fof(f75,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f250,plain,
    ( r2_hidden(k4_tarski(sK2(k5_relat_1(sK0,sK1)),sK7(sK0,sK1,sK2(k5_relat_1(sK0,sK1)),sK3(k5_relat_1(sK0,sK1)))),sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl17_2 ),
    inference(subsumption_resolution,[],[f249,f76])).

fof(f76,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f249,plain,
    ( r2_hidden(k4_tarski(sK2(k5_relat_1(sK0,sK1)),sK7(sK0,sK1,sK2(k5_relat_1(sK0,sK1)),sK3(k5_relat_1(sK0,sK1)))),sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl17_2 ),
    inference(resolution,[],[f242,f205])).

fof(f205,plain,
    ( r2_hidden(k4_tarski(sK2(k5_relat_1(sK0,sK1)),sK3(k5_relat_1(sK0,sK1))),k5_relat_1(sK0,sK1))
    | ~ spl17_2 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl17_2
  <=> r2_hidden(k4_tarski(sK2(k5_relat_1(sK0,sK1)),sK3(k5_relat_1(sK0,sK1))),k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_2])])).

fof(f242,plain,(
    ! [X0,X8,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f117,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t67_relat_1.p',dt_k5_relat_1)).

fof(f117,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK6(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f50,f53,f52,f51])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK5(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK4(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK6(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK6(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X3,X4] :
                      ( ( r2_hidden(k4_tarski(X3,X4),X2)
                        | ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t67_relat_1.p',d8_relat_1)).

fof(f1008,plain,
    ( r2_hidden(sK7(sK0,sK1,sK2(k5_relat_1(sK0,sK1)),sK3(k5_relat_1(sK0,sK1))),k1_relat_1(sK1))
    | ~ spl17_2 ),
    inference(resolution,[],[f241,f118])).

fof(f118,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK9(X0,X1),X3),X0)
            | ~ r2_hidden(sK9(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0)
            | r2_hidden(sK9(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK11(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f59,f62,f61,f60])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK9(X0,X1),X3),X0)
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK9(X0,X1),X4),X0)
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK10(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK11(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
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
    inference(rectify,[],[f58])).

fof(f58,plain,(
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
    file('/export/starexec/sandbox/benchmark/relat_1__t67_relat_1.p',d4_relat_1)).

fof(f241,plain,
    ( r2_hidden(k4_tarski(sK7(sK0,sK1,sK2(k5_relat_1(sK0,sK1)),sK3(k5_relat_1(sK0,sK1))),sK3(k5_relat_1(sK0,sK1))),sK1)
    | ~ spl17_2 ),
    inference(subsumption_resolution,[],[f240,f75])).

fof(f240,plain,
    ( r2_hidden(k4_tarski(sK7(sK0,sK1,sK2(k5_relat_1(sK0,sK1)),sK3(k5_relat_1(sK0,sK1))),sK3(k5_relat_1(sK0,sK1))),sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl17_2 ),
    inference(subsumption_resolution,[],[f239,f76])).

fof(f239,plain,
    ( r2_hidden(k4_tarski(sK7(sK0,sK1,sK2(k5_relat_1(sK0,sK1)),sK3(k5_relat_1(sK0,sK1))),sK3(k5_relat_1(sK0,sK1))),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl17_2 ),
    inference(resolution,[],[f233,f205])).

fof(f233,plain,(
    ! [X0,X8,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f116,f96])).

fof(f116,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f2400,plain,(
    spl17_19 ),
    inference(avatar_contradiction_clause,[],[f2399])).

fof(f2399,plain,
    ( $false
    | ~ spl17_19 ),
    inference(subsumption_resolution,[],[f2393,f79])).

fof(f79,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t67_relat_1.p',dt_o_0_0_xboole_0)).

fof(f2393,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl17_19 ),
    inference(resolution,[],[f2372,f128])).

fof(f128,plain,(
    ! [X0] :
      ( sQ16_eqProxy(k1_xboole_0,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f81,f125])).

fof(f81,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t67_relat_1.p',t6_boole)).

fof(f2372,plain,
    ( ~ sQ16_eqProxy(k1_xboole_0,o_0_0_xboole_0)
    | ~ spl17_19 ),
    inference(resolution,[],[f2365,f178])).

fof(f178,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ sQ16_eqProxy(X0,o_0_0_xboole_0) ) ),
    inference(resolution,[],[f176,f170])).

fof(f170,plain,(
    ! [X0,X1] :
      ( sQ16_eqProxy(X1,X0)
      | ~ sQ16_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f125])).

fof(f176,plain,(
    ! [X0] :
      ( ~ sQ16_eqProxy(o_0_0_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f167,f79])).

fof(f2365,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl17_19 ),
    inference(avatar_component_clause,[],[f2364])).

fof(f2364,plain,
    ( spl17_19
  <=> ~ v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_19])])).

fof(f213,plain,(
    spl17_1 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | ~ spl17_1 ),
    inference(subsumption_resolution,[],[f211,f75])).

fof(f211,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl17_1 ),
    inference(subsumption_resolution,[],[f208,f76])).

fof(f208,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl17_1 ),
    inference(resolution,[],[f199,f96])).

fof(f199,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl17_1 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl17_1
  <=> ~ v1_relat_1(k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_1])])).

fof(f206,plain,
    ( ~ spl17_1
    | spl17_2 ),
    inference(avatar_split_clause,[],[f193,f204,f198])).

fof(f193,plain,
    ( r2_hidden(k4_tarski(sK2(k5_relat_1(sK0,sK1)),sK3(k5_relat_1(sK0,sK1))),k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f129,f172])).

fof(f172,plain,(
    ~ sQ16_eqProxy(k1_xboole_0,k5_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f170,f126])).

fof(f126,plain,(
    ~ sQ16_eqProxy(k5_relat_1(sK0,sK1),k1_xboole_0) ),
    inference(equality_proxy_replacement,[],[f78,f125])).

fof(f78,plain,(
    k5_relat_1(sK0,sK1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

fof(f129,plain,(
    ! [X0] :
      ( sQ16_eqProxy(k1_xboole_0,X0)
      | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f82,f125])).

fof(f82,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f33,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
     => r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t67_relat_1.p',t56_relat_1)).
%------------------------------------------------------------------------------
