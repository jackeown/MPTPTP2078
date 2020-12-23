%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 209 expanded)
%              Number of leaves         :   14 (  60 expanded)
%              Depth                    :   17
%              Number of atoms          :  261 ( 796 expanded)
%              Number of equality atoms :   41 ( 115 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f202,plain,(
    $false ),
    inference(resolution,[],[f201,f41])).

fof(f41,plain,(
    ~ v4_relat_2(k2_wellord1(sK5,sK4)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ v4_relat_2(k2_wellord1(sK5,sK4))
    & v4_relat_2(sK5)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f8,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ~ v4_relat_2(k2_wellord1(X1,X0))
        & v4_relat_2(X1)
        & v1_relat_1(X1) )
   => ( ~ v4_relat_2(k2_wellord1(sK5,sK4))
      & v4_relat_2(sK5)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ v4_relat_2(k2_wellord1(X1,X0))
      & v4_relat_2(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ v4_relat_2(k2_wellord1(X1,X0))
      & v4_relat_2(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( v4_relat_2(X1)
         => v4_relat_2(k2_wellord1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_2(X1)
       => v4_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_wellord1)).

fof(f201,plain,(
    ! [X0] : v4_relat_2(k2_wellord1(sK5,X0)) ),
    inference(resolution,[],[f200,f131])).

fof(f131,plain,(
    ! [X0] :
      ( ~ sP0(k2_wellord1(sK5,X0))
      | v4_relat_2(k2_wellord1(sK5,X0)) ) ),
    inference(resolution,[],[f130,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ sP0(X0)
      | v4_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v4_relat_2(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f130,plain,(
    ! [X2] : sP1(k2_wellord1(sK5,X2)) ),
    inference(resolution,[],[f128,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f10,f14,f13])).

fof(f13,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1,X2] :
          ( X1 = X2
          | ~ r2_hidden(k4_tarski(X2,X1),X0)
          | ~ r2_hidden(k4_tarski(X1,X2),X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f10,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( ( r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_wellord1)).

fof(f128,plain,(
    ! [X11] : v1_relat_1(k2_wellord1(sK5,X11)) ),
    inference(subsumption_resolution,[],[f127,f52])).

fof(f52,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK8(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK8(X0)
          & r2_hidden(sK8(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK9(X4),sK10(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f27,f29,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK8(X0)
        & r2_hidden(sK8(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK9(X4),sK10(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(f127,plain,(
    ! [X11] :
      ( sK8(k2_wellord1(sK5,X11)) = k4_tarski(sK9(sK8(k2_wellord1(sK5,X11))),sK10(sK8(k2_wellord1(sK5,X11))))
      | v1_relat_1(k2_wellord1(sK5,X11)) ) ),
    inference(subsumption_resolution,[],[f123,f39])).

fof(f39,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f20])).

fof(f123,plain,(
    ! [X11] :
      ( sK8(k2_wellord1(sK5,X11)) = k4_tarski(sK9(sK8(k2_wellord1(sK5,X11))),sK10(sK8(k2_wellord1(sK5,X11))))
      | ~ v1_relat_1(sK5)
      | v1_relat_1(k2_wellord1(sK5,X11)) ) ),
    inference(resolution,[],[f50,f81])).

fof(f81,plain,(
    ! [X0] :
      ( r2_hidden(sK8(k2_wellord1(sK5,X0)),sK5)
      | v1_relat_1(k2_wellord1(sK5,X0)) ) ),
    inference(resolution,[],[f80,f51])).

fof(f51,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k2_wellord1(sK5,X3))
      | r2_hidden(X2,sK5) ) ),
    inference(resolution,[],[f74,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X1,X3,X0] :
      ( ( sP2(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP2(X1,X3,X0) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X1,X3,X0] :
      ( ( sP2(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP2(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X1,X3,X0] :
      ( sP2(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f74,plain,(
    ! [X4,X3] :
      ( sP2(k2_zfmisc_1(X4,X4),X3,sK5)
      | ~ r2_hidden(X3,k2_wellord1(sK5,X4)) ) ),
    inference(resolution,[],[f53,f71])).

fof(f71,plain,(
    ! [X0] : sP3(sK5,k2_zfmisc_1(X0,X0),k2_wellord1(sK5,X0)) ),
    inference(superposition,[],[f62,f70])).

fof(f70,plain,(
    ! [X0] : k2_wellord1(sK5,X0) = k3_xboole_0(sK5,k2_zfmisc_1(X0,X0)) ),
    inference(resolution,[],[f49,f39])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_wellord1)).

fof(f62,plain,(
    ! [X0,X1] : sP3(X0,X1,k3_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP3(X0,X1,X2) )
      & ( sP3(X0,X1,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP3(X0,X1,X2) ) ),
    inference(definition_folding,[],[f1,f17,f16])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( sP3(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP2(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP2(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( ( ~ sP2(X1,sK11(X0,X1,X2),X0)
            | ~ r2_hidden(sK11(X0,X1,X2),X2) )
          & ( sP2(X1,sK11(X0,X1,X2),X0)
            | r2_hidden(sK11(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP2(X1,X4,X0) )
            & ( sP2(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP2(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP2(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP2(X1,sK11(X0,X1,X2),X0)
          | ~ r2_hidden(sK11(X0,X1,X2),X2) )
        & ( sP2(X1,sK11(X0,X1,X2),X0)
          | r2_hidden(sK11(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP2(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP2(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP2(X1,X4,X0) )
            & ( sP2(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP2(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP2(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP2(X1,X3,X0) )
            & ( sP2(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X4,X0] :
      ( ~ r2_hidden(X4,X0)
      | k4_tarski(sK9(X4),sK10(X4)) = X4
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f200,plain,(
    ! [X0] : sP0(k2_wellord1(sK5,X0)) ),
    inference(subsumption_resolution,[],[f199,f83])).

fof(f83,plain,(
    ! [X2] :
      ( r2_hidden(k4_tarski(sK7(k2_wellord1(sK5,X2)),sK6(k2_wellord1(sK5,X2))),sK5)
      | sP0(k2_wellord1(sK5,X2)) ) ),
    inference(resolution,[],[f80,f46])).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK7(X0),sK6(X0)),X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( sK6(X0) != sK7(X0)
          & r2_hidden(k4_tarski(sK7(X0),sK6(X0)),X0)
          & r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) ) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | ~ r2_hidden(k4_tarski(X4,X3),X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X0) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f23,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & r2_hidden(k4_tarski(X2,X1),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( sK6(X0) != sK7(X0)
        & r2_hidden(k4_tarski(sK7(X0),sK6(X0)),X0)
        & r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1,X2] :
            ( X1 != X2
            & r2_hidden(k4_tarski(X2,X1),X0)
            & r2_hidden(k4_tarski(X1,X2),X0) ) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | ~ r2_hidden(k4_tarski(X4,X3),X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X0) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1,X2] :
            ( X1 != X2
            & r2_hidden(k4_tarski(X2,X1),X0)
            & r2_hidden(k4_tarski(X1,X2),X0) ) )
      & ( ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f199,plain,(
    ! [X0] :
      ( sP0(k2_wellord1(sK5,X0))
      | ~ r2_hidden(k4_tarski(sK7(k2_wellord1(sK5,X0)),sK6(k2_wellord1(sK5,X0))),sK5) ) ),
    inference(subsumption_resolution,[],[f198,f47])).

fof(f47,plain,(
    ! [X0] :
      ( sK6(X0) != sK7(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f198,plain,(
    ! [X0] :
      ( sP0(k2_wellord1(sK5,X0))
      | sK6(k2_wellord1(sK5,X0)) = sK7(k2_wellord1(sK5,X0))
      | ~ r2_hidden(k4_tarski(sK7(k2_wellord1(sK5,X0)),sK6(k2_wellord1(sK5,X0))),sK5) ) ),
    inference(subsumption_resolution,[],[f196,f65])).

fof(f65,plain,(
    sP0(sK5) ),
    inference(subsumption_resolution,[],[f64,f40])).

fof(f40,plain,(
    v4_relat_2(sK5) ),
    inference(cnf_transformation,[],[f20])).

fof(f64,plain,
    ( ~ v4_relat_2(sK5)
    | sP0(sK5) ),
    inference(resolution,[],[f42,f63])).

fof(f63,plain,(
    sP1(sK5) ),
    inference(resolution,[],[f48,f39])).

fof(f42,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ v4_relat_2(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f196,plain,(
    ! [X0] :
      ( sP0(k2_wellord1(sK5,X0))
      | sK6(k2_wellord1(sK5,X0)) = sK7(k2_wellord1(sK5,X0))
      | ~ r2_hidden(k4_tarski(sK7(k2_wellord1(sK5,X0)),sK6(k2_wellord1(sK5,X0))),sK5)
      | ~ sP0(sK5) ) ),
    inference(resolution,[],[f82,f44])).

fof(f44,plain,(
    ! [X4,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X4,X3),X0)
      | X3 = X4
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f82,plain,(
    ! [X1] :
      ( r2_hidden(k4_tarski(sK6(k2_wellord1(sK5,X1)),sK7(k2_wellord1(sK5,X1))),sK5)
      | sP0(k2_wellord1(sK5,X1)) ) ),
    inference(resolution,[],[f80,f45])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:49:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (11628)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.46  % (11612)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.48  % (11628)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f202,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(resolution,[],[f201,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ~v4_relat_2(k2_wellord1(sK5,sK4))),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ~v4_relat_2(k2_wellord1(sK5,sK4)) & v4_relat_2(sK5) & v1_relat_1(sK5)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f8,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ? [X0,X1] : (~v4_relat_2(k2_wellord1(X1,X0)) & v4_relat_2(X1) & v1_relat_1(X1)) => (~v4_relat_2(k2_wellord1(sK5,sK4)) & v4_relat_2(sK5) & v1_relat_1(sK5))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0,X1] : (~v4_relat_2(k2_wellord1(X1,X0)) & v4_relat_2(X1) & v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0,X1] : ((~v4_relat_2(k2_wellord1(X1,X0)) & v4_relat_2(X1)) & v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : (v1_relat_1(X1) => (v4_relat_2(X1) => v4_relat_2(k2_wellord1(X1,X0))))),
% 0.21/0.48    inference(negated_conjecture,[],[f5])).
% 0.21/0.48  fof(f5,conjecture,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_2(X1) => v4_relat_2(k2_wellord1(X1,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_wellord1)).
% 0.21/0.48  fof(f201,plain,(
% 0.21/0.48    ( ! [X0] : (v4_relat_2(k2_wellord1(sK5,X0))) )),
% 0.21/0.48    inference(resolution,[],[f200,f131])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    ( ! [X0] : (~sP0(k2_wellord1(sK5,X0)) | v4_relat_2(k2_wellord1(sK5,X0))) )),
% 0.21/0.48    inference(resolution,[],[f130,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0] : (~sP1(X0) | ~sP0(X0) | v4_relat_2(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (((v4_relat_2(X0) | ~sP0(X0)) & (sP0(X0) | ~v4_relat_2(X0))) | ~sP1(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : ((v4_relat_2(X0) <=> sP0(X0)) | ~sP1(X0))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    ( ! [X2] : (sP1(k2_wellord1(sK5,X2))) )),
% 0.21/0.48    inference(resolution,[],[f128,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | sP1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (sP1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(definition_folding,[],[f10,f14,f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (sP0(X0) <=> ! [X1,X2] : (X1 = X2 | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : ((v4_relat_2(X0) <=> ! [X1,X2] : (X1 = X2 | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0] : ((v4_relat_2(X0) <=> ! [X1,X2] : (X1 = X2 | (~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => (v4_relat_2(X0) <=> ! [X1,X2] : ((r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => X1 = X2)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_wellord1)).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    ( ! [X11] : (v1_relat_1(k2_wellord1(sK5,X11))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f127,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK8(X0) | v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK8(X0) & r2_hidden(sK8(X0),X0))) & (! [X4] : (k4_tarski(sK9(X4),sK10(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f27,f29,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK8(X0) & r2_hidden(sK8(X0),X0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK9(X4),sK10(X4)) = X4)),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(rectify,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    ( ! [X11] : (sK8(k2_wellord1(sK5,X11)) = k4_tarski(sK9(sK8(k2_wellord1(sK5,X11))),sK10(sK8(k2_wellord1(sK5,X11)))) | v1_relat_1(k2_wellord1(sK5,X11))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f123,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    v1_relat_1(sK5)),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    ( ! [X11] : (sK8(k2_wellord1(sK5,X11)) = k4_tarski(sK9(sK8(k2_wellord1(sK5,X11))),sK10(sK8(k2_wellord1(sK5,X11)))) | ~v1_relat_1(sK5) | v1_relat_1(k2_wellord1(sK5,X11))) )),
% 0.21/0.49    inference(resolution,[],[f50,f81])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK8(k2_wellord1(sK5,X0)),sK5) | v1_relat_1(k2_wellord1(sK5,X0))) )),
% 0.21/0.49    inference(resolution,[],[f80,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK8(X0),X0) | v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~r2_hidden(X2,k2_wellord1(sK5,X3)) | r2_hidden(X2,sK5)) )),
% 0.21/0.49    inference(resolution,[],[f74,f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | r2_hidden(X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP2(X0,X1,X2)))),
% 0.21/0.49    inference(rectify,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X1,X3,X0] : ((sP2(X1,X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP2(X1,X3,X0)))),
% 0.21/0.49    inference(flattening,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X1,X3,X0] : ((sP2(X1,X3,X0) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP2(X1,X3,X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X1,X3,X0] : (sP2(X1,X3,X0) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X4,X3] : (sP2(k2_zfmisc_1(X4,X4),X3,sK5) | ~r2_hidden(X3,k2_wellord1(sK5,X4))) )),
% 0.21/0.49    inference(resolution,[],[f53,f71])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ( ! [X0] : (sP3(sK5,k2_zfmisc_1(X0,X0),k2_wellord1(sK5,X0))) )),
% 0.21/0.49    inference(superposition,[],[f62,f70])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X0] : (k2_wellord1(sK5,X0) = k3_xboole_0(sK5,k2_zfmisc_1(X0,X0))) )),
% 0.21/0.49    inference(resolution,[],[f49,f39])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_wellord1)).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X0,X1] : (sP3(X0,X1,k3_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(equality_resolution,[],[f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (sP3(X0,X1,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP3(X0,X1,X2)) & (sP3(X0,X1,X2) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.49    inference(nnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP3(X0,X1,X2))),
% 0.21/0.49    inference(definition_folding,[],[f1,f17,f16])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (sP3(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP2(X1,X3,X0)))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X1] : (~sP3(X0,X1,X2) | ~r2_hidden(X4,X2) | sP2(X1,X4,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ((~sP2(X1,sK11(X0,X1,X2),X0) | ~r2_hidden(sK11(X0,X1,X2),X2)) & (sP2(X1,sK11(X0,X1,X2),X0) | r2_hidden(sK11(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP2(X1,X4,X0)) & (sP2(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP3(X0,X1,X2)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f32,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X3] : ((~sP2(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP2(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP2(X1,sK11(X0,X1,X2),X0) | ~r2_hidden(sK11(X0,X1,X2),X2)) & (sP2(X1,sK11(X0,X1,X2),X0) | r2_hidden(sK11(X0,X1,X2),X2))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : ((~sP2(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP2(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP2(X1,X4,X0)) & (sP2(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP3(X0,X1,X2)))),
% 0.21/0.49    inference(rectify,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : ((~sP2(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP2(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP2(X1,X3,X0)) & (sP2(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP3(X0,X1,X2)))),
% 0.21/0.49    inference(nnf_transformation,[],[f17])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X4,X0] : (~r2_hidden(X4,X0) | k4_tarski(sK9(X4),sK10(X4)) = X4 | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f200,plain,(
% 0.21/0.49    ( ! [X0] : (sP0(k2_wellord1(sK5,X0))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f199,f83])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ( ! [X2] : (r2_hidden(k4_tarski(sK7(k2_wellord1(sK5,X2)),sK6(k2_wellord1(sK5,X2))),sK5) | sP0(k2_wellord1(sK5,X2))) )),
% 0.21/0.49    inference(resolution,[],[f80,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(k4_tarski(sK7(X0),sK6(X0)),X0) | sP0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : ((sP0(X0) | (sK6(X0) != sK7(X0) & r2_hidden(k4_tarski(sK7(X0),sK6(X0)),X0) & r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0))) & (! [X3,X4] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~sP0(X0)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f23,f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : (? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => (sK6(X0) != sK7(X0) & r2_hidden(k4_tarski(sK7(X0),sK6(X0)),X0) & r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X3,X4] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~sP0(X0)))),
% 0.21/0.49    inference(rectify,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X1,X2] : (X1 = X2 | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)) | ~sP0(X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f13])).
% 0.21/0.49  fof(f199,plain,(
% 0.21/0.49    ( ! [X0] : (sP0(k2_wellord1(sK5,X0)) | ~r2_hidden(k4_tarski(sK7(k2_wellord1(sK5,X0)),sK6(k2_wellord1(sK5,X0))),sK5)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f198,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0] : (sK6(X0) != sK7(X0) | sP0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f198,plain,(
% 0.21/0.49    ( ! [X0] : (sP0(k2_wellord1(sK5,X0)) | sK6(k2_wellord1(sK5,X0)) = sK7(k2_wellord1(sK5,X0)) | ~r2_hidden(k4_tarski(sK7(k2_wellord1(sK5,X0)),sK6(k2_wellord1(sK5,X0))),sK5)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f196,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    sP0(sK5)),
% 0.21/0.49    inference(subsumption_resolution,[],[f64,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    v4_relat_2(sK5)),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ~v4_relat_2(sK5) | sP0(sK5)),
% 0.21/0.49    inference(resolution,[],[f42,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    sP1(sK5)),
% 0.21/0.49    inference(resolution,[],[f48,f39])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0] : (~sP1(X0) | ~v4_relat_2(X0) | sP0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    ( ! [X0] : (sP0(k2_wellord1(sK5,X0)) | sK6(k2_wellord1(sK5,X0)) = sK7(k2_wellord1(sK5,X0)) | ~r2_hidden(k4_tarski(sK7(k2_wellord1(sK5,X0)),sK6(k2_wellord1(sK5,X0))),sK5) | ~sP0(sK5)) )),
% 0.21/0.49    inference(resolution,[],[f82,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X4,X0,X3] : (~r2_hidden(k4_tarski(X4,X3),X0) | X3 = X4 | ~r2_hidden(k4_tarski(X3,X4),X0) | ~sP0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X1] : (r2_hidden(k4_tarski(sK6(k2_wellord1(sK5,X1)),sK7(k2_wellord1(sK5,X1))),sK5) | sP0(k2_wellord1(sK5,X1))) )),
% 0.21/0.49    inference(resolution,[],[f80,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) | sP0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (11628)------------------------------
% 0.21/0.49  % (11628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (11628)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (11628)Memory used [KB]: 10746
% 0.21/0.49  % (11628)Time elapsed: 0.078 s
% 0.21/0.49  % (11628)------------------------------
% 0.21/0.49  % (11628)------------------------------
% 0.21/0.49  % (11606)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.49  % (11602)Success in time 0.133 s
%------------------------------------------------------------------------------
