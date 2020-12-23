%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:01 EST 2020

% Result     : Theorem 2.00s
% Output     : Refutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 303 expanded)
%              Number of leaves         :   13 (  87 expanded)
%              Depth                    :   20
%              Number of atoms          :  252 (1246 expanded)
%              Number of equality atoms :   84 ( 475 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f972,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f52,f951,f54])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f37,f36])).

fof(f36,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f10,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f951,plain,(
    ! [X0] : ~ r2_hidden(X0,sK3) ),
    inference(subsumption_resolution,[],[f950,f945])).

fof(f945,plain,(
    r2_hidden(sK5(sK2,sK3),sK2) ),
    inference(subsumption_resolution,[],[f944,f35])).

fof(f35,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK2 != sK3
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK3,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f9,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) )
   => ( sK2 != sK3
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
       => ( X0 = X1
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
     => ( X0 = X1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

fof(f944,plain,
    ( r2_hidden(sK5(sK2,sK3),sK2)
    | sK2 = sK3 ),
    inference(factoring,[],[f263])).

fof(f263,plain,(
    ! [X1] :
      ( r2_hidden(sK5(X1,sK3),sK2)
      | sK3 = X1
      | r2_hidden(sK5(X1,sK3),X1) ) ),
    inference(resolution,[],[f253,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK5(X0,X1),X1)
          | ~ r2_hidden(sK5(X0,X1),X0) )
        & ( r2_hidden(sK5(X0,X1),X1)
          | r2_hidden(sK5(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1),X1)
          | ~ r2_hidden(sK5(X0,X1),X0) )
        & ( r2_hidden(sK5(X0,X1),X1)
          | r2_hidden(sK5(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f253,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | r2_hidden(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f249,f53])).

fof(f53,plain,(
    o_0_0_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f33,f36])).

fof(f33,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f17])).

fof(f249,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | r2_hidden(X0,sK2)
      | o_0_0_xboole_0 = sK2 ) ),
    inference(resolution,[],[f233,f54])).

fof(f233,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,sK2)
      | ~ r2_hidden(X2,sK3)
      | r2_hidden(X2,sK2) ) ),
    inference(resolution,[],[f105,f147])).

fof(f147,plain,(
    ! [X12,X10,X13,X11] :
      ( ~ sP0(k4_tarski(X10,X11),X12,X13)
      | r2_hidden(X11,X12) ) ),
    inference(duplicate_literal_removal,[],[f146])).

fof(f146,plain,(
    ! [X12,X10,X13,X11] :
      ( r2_hidden(X11,X12)
      | ~ sP0(k4_tarski(X10,X11),X12,X13)
      | ~ sP0(k4_tarski(X10,X11),X12,X13) ) ),
    inference(superposition,[],[f45,f117])).

fof(f117,plain,(
    ! [X2,X0,X3,X1] :
      ( sK8(k4_tarski(X0,X1),X2,X3) = X1
      | ~ sP0(k4_tarski(X0,X1),X2,X3) ) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( k4_tarski(X8,X9) != X5
      | sK8(X5,X6,X7) = X9
      | ~ sP0(X5,X6,X7) ) ),
    inference(superposition,[],[f51,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)) = X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3,X4] :
            ( k4_tarski(X3,X4) != X0
            | ~ r2_hidden(X4,X1)
            | ~ r2_hidden(X3,X2) ) )
      & ( ( k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)) = X0
          & r2_hidden(sK8(X0,X1,X2),X1)
          & r2_hidden(sK7(X0,X1,X2),X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X5,X6] :
          ( k4_tarski(X5,X6) = X0
          & r2_hidden(X6,X1)
          & r2_hidden(X5,X2) )
     => ( k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)) = X0
        & r2_hidden(sK8(X0,X1,X2),X1)
        & r2_hidden(sK7(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3,X4] :
            ( k4_tarski(X3,X4) != X0
            | ~ r2_hidden(X4,X1)
            | ~ r2_hidden(X3,X2) ) )
      & ( ? [X5,X6] :
            ( k4_tarski(X5,X6) = X0
            & r2_hidden(X6,X1)
            & r2_hidden(X5,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X3,X1,X0] :
      ( ( sP0(X3,X1,X0)
        | ! [X4,X5] :
            ( k4_tarski(X4,X5) != X3
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X0) ) )
      & ( ? [X4,X5] :
            ( k4_tarski(X4,X5) = X3
            & r2_hidden(X5,X1)
            & r2_hidden(X4,X0) )
        | ~ sP0(X3,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X3,X1,X0] :
      ( sP0(X3,X1,X0)
    <=> ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X4,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X0,X1) = k4_tarski(X2,X3)
     => ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_zfmisc_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f105,plain,(
    ! [X0,X1] :
      ( sP0(k4_tarski(X0,X1),sK2,sK3)
      | ~ r2_hidden(X1,sK3)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f93,f55])).

fof(f55,plain,(
    ! [X4,X2,X3,X1] :
      ( sP0(k4_tarski(X3,X4),X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X3,X2) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | k4_tarski(X3,X4) != X0
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X3,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f93,plain,(
    ! [X0] :
      ( ~ sP0(X0,sK3,sK2)
      | sP0(X0,sK2,sK3) ) ),
    inference(resolution,[],[f75,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k2_zfmisc_1(X2,X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f41,f56])).

fof(f56,plain,(
    ! [X0,X1] : sP1(X0,X1,k2_zfmisc_1(X0,X1)) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f4,f14,f13])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X3,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X4,X1,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(sK6(X0,X1,X2),X1,X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sP0(sK6(X0,X1,X2),X1,X0)
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X4,X1,X0) )
            & ( sP0(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X3,X1,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X3,X1,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(sK6(X0,X1,X2),X1,X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sP0(sK6(X0,X1,X2),X1,X0)
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X4,X1,X0) )
            & ( sP0(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X3,X1,X0) )
            & ( sP0(X3,X1,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f75,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(sK2,sK3))
      | sP0(X3,sK2,sK3) ) ),
    inference(resolution,[],[f40,f57])).

fof(f57,plain,(
    sP1(sK3,sK2,k2_zfmisc_1(sK2,sK3)) ),
    inference(superposition,[],[f56,f32])).

fof(f32,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP0(X4,X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f950,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(sK5(sK2,sK3),sK2) ) ),
    inference(subsumption_resolution,[],[f948,f35])).

fof(f948,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | sK2 = sK3
      | ~ r2_hidden(sK5(sK2,sK3),sK2) ) ),
    inference(resolution,[],[f947,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | X0 = X1
      | ~ r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f947,plain,(
    ! [X1] :
      ( r2_hidden(sK5(sK2,sK3),sK3)
      | ~ r2_hidden(X1,sK3) ) ),
    inference(resolution,[],[f945,f232])).

fof(f232,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(X0,sK3)
      | r2_hidden(X1,sK3) ) ),
    inference(resolution,[],[f105,f155])).

fof(f155,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ sP0(k4_tarski(X4,X5),X6,X7)
      | r2_hidden(X4,X7) ) ),
    inference(duplicate_literal_removal,[],[f154])).

fof(f154,plain,(
    ! [X6,X4,X7,X5] :
      ( r2_hidden(X4,X7)
      | ~ sP0(k4_tarski(X4,X5),X6,X7)
      | ~ sP0(k4_tarski(X4,X5),X6,X7) ) ),
    inference(superposition,[],[f44,f121])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( sK7(k4_tarski(X0,X1),X2,X3) = X0
      | ~ sP0(k4_tarski(X0,X1),X2,X3) ) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X19,X17,X15,X18,X16] :
      ( k4_tarski(X18,X19) != X15
      | sK7(X15,X16,X17) = X18
      | ~ sP0(X15,X16,X17) ) ),
    inference(superposition,[],[f50,f46])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f52,plain,(
    o_0_0_xboole_0 != sK3 ),
    inference(definition_unfolding,[],[f34,f36])).

fof(f34,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:55:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.51  % (8068)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.51  % (8066)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.52  % (8060)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.52  % (8082)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.53  % (8074)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.53  % (8074)Refutation not found, incomplete strategy% (8074)------------------------------
% 0.19/0.53  % (8074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (8074)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (8074)Memory used [KB]: 1663
% 0.19/0.53  % (8074)Time elapsed: 0.127 s
% 0.19/0.53  % (8074)------------------------------
% 0.19/0.53  % (8074)------------------------------
% 0.19/0.53  % (8065)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.54  % (8067)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.55  % (8053)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.55  % (8063)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.55  % (8054)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.56  % (8079)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.56  % (8056)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.56  % (8075)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.56  % (8058)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.56  % (8064)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.56  % (8055)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.56  % (8059)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.57  % (8076)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.57  % (8071)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.57  % (8081)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.58  % (8073)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.58  % (8073)Refutation not found, incomplete strategy% (8073)------------------------------
% 0.19/0.58  % (8073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.58  % (8073)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.58  
% 0.19/0.58  % (8073)Memory used [KB]: 10746
% 0.19/0.58  % (8073)Time elapsed: 0.191 s
% 0.19/0.58  % (8073)------------------------------
% 0.19/0.58  % (8073)------------------------------
% 0.19/0.58  % (8075)Refutation not found, incomplete strategy% (8075)------------------------------
% 0.19/0.58  % (8075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.58  % (8075)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.58  
% 0.19/0.58  % (8075)Memory used [KB]: 10746
% 0.19/0.58  % (8075)Time elapsed: 0.096 s
% 0.19/0.58  % (8075)------------------------------
% 0.19/0.58  % (8075)------------------------------
% 0.19/0.58  % (8057)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.58  % (8078)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.59  % (8069)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.73/0.59  % (8061)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.73/0.59  % (8070)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.73/0.60  % (8072)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.73/0.60  % (8080)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.73/0.60  % (8062)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.73/0.61  % (8077)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 2.00/0.62  % (8082)Refutation found. Thanks to Tanya!
% 2.00/0.62  % SZS status Theorem for theBenchmark
% 2.00/0.62  % SZS output start Proof for theBenchmark
% 2.00/0.62  fof(f972,plain,(
% 2.00/0.62    $false),
% 2.00/0.62    inference(unit_resulting_resolution,[],[f52,f951,f54])).
% 2.00/0.62  fof(f54,plain,(
% 2.00/0.62    ( ! [X0] : (r2_hidden(sK4(X0),X0) | o_0_0_xboole_0 = X0) )),
% 2.00/0.62    inference(definition_unfolding,[],[f37,f36])).
% 2.00/0.62  fof(f36,plain,(
% 2.00/0.62    k1_xboole_0 = o_0_0_xboole_0),
% 2.00/0.62    inference(cnf_transformation,[],[f1])).
% 2.00/0.62  fof(f1,axiom,(
% 2.00/0.62    k1_xboole_0 = o_0_0_xboole_0),
% 2.00/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).
% 2.00/0.62  fof(f37,plain,(
% 2.00/0.62    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 2.00/0.62    inference(cnf_transformation,[],[f19])).
% 2.00/0.62  fof(f19,plain,(
% 2.00/0.62    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 2.00/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f10,f18])).
% 2.00/0.62  fof(f18,plain,(
% 2.00/0.62    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 2.00/0.62    introduced(choice_axiom,[])).
% 2.00/0.62  fof(f10,plain,(
% 2.00/0.62    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.00/0.62    inference(ennf_transformation,[],[f3])).
% 2.00/0.62  fof(f3,axiom,(
% 2.00/0.62    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.00/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.00/0.62  fof(f951,plain,(
% 2.00/0.62    ( ! [X0] : (~r2_hidden(X0,sK3)) )),
% 2.00/0.62    inference(subsumption_resolution,[],[f950,f945])).
% 2.00/0.62  fof(f945,plain,(
% 2.00/0.62    r2_hidden(sK5(sK2,sK3),sK2)),
% 2.00/0.62    inference(subsumption_resolution,[],[f944,f35])).
% 2.00/0.62  fof(f35,plain,(
% 2.00/0.62    sK2 != sK3),
% 2.00/0.62    inference(cnf_transformation,[],[f17])).
% 2.00/0.62  fof(f17,plain,(
% 2.00/0.62    sK2 != sK3 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK3,sK2)),
% 2.00/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f9,f16])).
% 2.00/0.62  fof(f16,plain,(
% 2.00/0.62    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)) => (sK2 != sK3 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK3,sK2))),
% 2.00/0.62    introduced(choice_axiom,[])).
% 2.00/0.62  fof(f9,plain,(
% 2.00/0.62    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 2.00/0.62    inference(flattening,[],[f8])).
% 2.00/0.62  fof(f8,plain,(
% 2.00/0.62    ? [X0,X1] : ((X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 2.00/0.62    inference(ennf_transformation,[],[f7])).
% 2.00/0.62  fof(f7,negated_conjecture,(
% 2.00/0.62    ~! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.00/0.62    inference(negated_conjecture,[],[f6])).
% 2.00/0.62  fof(f6,conjecture,(
% 2.00/0.62    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.00/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).
% 2.00/0.62  fof(f944,plain,(
% 2.00/0.62    r2_hidden(sK5(sK2,sK3),sK2) | sK2 = sK3),
% 2.00/0.62    inference(factoring,[],[f263])).
% 2.00/0.62  fof(f263,plain,(
% 2.00/0.62    ( ! [X1] : (r2_hidden(sK5(X1,sK3),sK2) | sK3 = X1 | r2_hidden(sK5(X1,sK3),X1)) )),
% 2.00/0.62    inference(resolution,[],[f253,f38])).
% 2.00/0.62  fof(f38,plain,(
% 2.00/0.62    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | X0 = X1 | r2_hidden(sK5(X0,X1),X0)) )),
% 2.00/0.62    inference(cnf_transformation,[],[f22])).
% 2.00/0.62  fof(f22,plain,(
% 2.00/0.62    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK5(X0,X1),X1) | ~r2_hidden(sK5(X0,X1),X0)) & (r2_hidden(sK5(X0,X1),X1) | r2_hidden(sK5(X0,X1),X0))))),
% 2.00/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f21])).
% 2.00/0.62  fof(f21,plain,(
% 2.00/0.62    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK5(X0,X1),X1) | ~r2_hidden(sK5(X0,X1),X0)) & (r2_hidden(sK5(X0,X1),X1) | r2_hidden(sK5(X0,X1),X0))))),
% 2.00/0.62    introduced(choice_axiom,[])).
% 2.00/0.62  fof(f20,plain,(
% 2.00/0.62    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 2.00/0.62    inference(nnf_transformation,[],[f11])).
% 2.00/0.62  fof(f11,plain,(
% 2.00/0.62    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 2.00/0.62    inference(ennf_transformation,[],[f2])).
% 2.00/0.62  fof(f2,axiom,(
% 2.00/0.62    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 2.00/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 2.00/0.62  fof(f253,plain,(
% 2.00/0.62    ( ! [X0] : (~r2_hidden(X0,sK3) | r2_hidden(X0,sK2)) )),
% 2.00/0.62    inference(subsumption_resolution,[],[f249,f53])).
% 2.00/0.62  fof(f53,plain,(
% 2.00/0.62    o_0_0_xboole_0 != sK2),
% 2.00/0.62    inference(definition_unfolding,[],[f33,f36])).
% 2.00/0.62  fof(f33,plain,(
% 2.00/0.62    k1_xboole_0 != sK2),
% 2.00/0.62    inference(cnf_transformation,[],[f17])).
% 2.00/0.62  fof(f249,plain,(
% 2.00/0.62    ( ! [X0] : (~r2_hidden(X0,sK3) | r2_hidden(X0,sK2) | o_0_0_xboole_0 = sK2) )),
% 2.00/0.62    inference(resolution,[],[f233,f54])).
% 2.00/0.62  fof(f233,plain,(
% 2.00/0.62    ( ! [X2,X3] : (~r2_hidden(X3,sK2) | ~r2_hidden(X2,sK3) | r2_hidden(X2,sK2)) )),
% 2.00/0.62    inference(resolution,[],[f105,f147])).
% 2.00/0.62  fof(f147,plain,(
% 2.00/0.62    ( ! [X12,X10,X13,X11] : (~sP0(k4_tarski(X10,X11),X12,X13) | r2_hidden(X11,X12)) )),
% 2.00/0.62    inference(duplicate_literal_removal,[],[f146])).
% 2.00/0.62  fof(f146,plain,(
% 2.00/0.62    ( ! [X12,X10,X13,X11] : (r2_hidden(X11,X12) | ~sP0(k4_tarski(X10,X11),X12,X13) | ~sP0(k4_tarski(X10,X11),X12,X13)) )),
% 2.00/0.62    inference(superposition,[],[f45,f117])).
% 2.00/0.62  fof(f117,plain,(
% 2.00/0.62    ( ! [X2,X0,X3,X1] : (sK8(k4_tarski(X0,X1),X2,X3) = X1 | ~sP0(k4_tarski(X0,X1),X2,X3)) )),
% 2.00/0.62    inference(equality_resolution,[],[f101])).
% 2.00/0.62  fof(f101,plain,(
% 2.00/0.62    ( ! [X6,X8,X7,X5,X9] : (k4_tarski(X8,X9) != X5 | sK8(X5,X6,X7) = X9 | ~sP0(X5,X6,X7)) )),
% 2.00/0.62    inference(superposition,[],[f51,f46])).
% 2.00/0.62  fof(f46,plain,(
% 2.00/0.62    ( ! [X2,X0,X1] : (k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)) = X0 | ~sP0(X0,X1,X2)) )),
% 2.00/0.62    inference(cnf_transformation,[],[f30])).
% 2.00/0.62  fof(f30,plain,(
% 2.00/0.62    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3,X4] : (k4_tarski(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2))) & ((k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)) = X0 & r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X2)) | ~sP0(X0,X1,X2)))),
% 2.00/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f28,f29])).
% 2.00/0.62  fof(f29,plain,(
% 2.00/0.62    ! [X2,X1,X0] : (? [X5,X6] : (k4_tarski(X5,X6) = X0 & r2_hidden(X6,X1) & r2_hidden(X5,X2)) => (k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)) = X0 & r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X2)))),
% 2.00/0.62    introduced(choice_axiom,[])).
% 2.00/0.62  fof(f28,plain,(
% 2.00/0.62    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3,X4] : (k4_tarski(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2))) & (? [X5,X6] : (k4_tarski(X5,X6) = X0 & r2_hidden(X6,X1) & r2_hidden(X5,X2)) | ~sP0(X0,X1,X2)))),
% 2.00/0.62    inference(rectify,[],[f27])).
% 2.00/0.62  fof(f27,plain,(
% 2.00/0.62    ! [X3,X1,X0] : ((sP0(X3,X1,X0) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~sP0(X3,X1,X0)))),
% 2.00/0.62    inference(nnf_transformation,[],[f13])).
% 2.00/0.62  fof(f13,plain,(
% 2.00/0.62    ! [X3,X1,X0] : (sP0(X3,X1,X0) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)))),
% 2.00/0.62    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.00/0.62  fof(f51,plain,(
% 2.00/0.62    ( ! [X2,X0,X3,X1] : (k4_tarski(X0,X1) != k4_tarski(X2,X3) | X1 = X3) )),
% 2.00/0.62    inference(cnf_transformation,[],[f12])).
% 2.00/0.62  fof(f12,plain,(
% 2.00/0.62    ! [X0,X1,X2,X3] : ((X1 = X3 & X0 = X2) | k4_tarski(X0,X1) != k4_tarski(X2,X3))),
% 2.00/0.62    inference(ennf_transformation,[],[f5])).
% 2.00/0.62  fof(f5,axiom,(
% 2.00/0.62    ! [X0,X1,X2,X3] : (k4_tarski(X0,X1) = k4_tarski(X2,X3) => (X1 = X3 & X0 = X2))),
% 2.00/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_zfmisc_1)).
% 2.00/0.62  fof(f45,plain,(
% 2.00/0.62    ( ! [X2,X0,X1] : (r2_hidden(sK8(X0,X1,X2),X1) | ~sP0(X0,X1,X2)) )),
% 2.00/0.62    inference(cnf_transformation,[],[f30])).
% 2.00/0.62  fof(f105,plain,(
% 2.00/0.62    ( ! [X0,X1] : (sP0(k4_tarski(X0,X1),sK2,sK3) | ~r2_hidden(X1,sK3) | ~r2_hidden(X0,sK2)) )),
% 2.00/0.62    inference(resolution,[],[f93,f55])).
% 2.00/0.62  fof(f55,plain,(
% 2.00/0.62    ( ! [X4,X2,X3,X1] : (sP0(k4_tarski(X3,X4),X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2)) )),
% 2.00/0.62    inference(equality_resolution,[],[f47])).
% 2.00/0.62  fof(f47,plain,(
% 2.00/0.62    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2) | k4_tarski(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2)) )),
% 2.00/0.62    inference(cnf_transformation,[],[f30])).
% 2.00/0.62  fof(f93,plain,(
% 2.00/0.62    ( ! [X0] : (~sP0(X0,sK3,sK2) | sP0(X0,sK2,sK3)) )),
% 2.00/0.62    inference(resolution,[],[f75,f76])).
% 2.00/0.62  fof(f76,plain,(
% 2.00/0.62    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_zfmisc_1(X2,X1)) | ~sP0(X0,X1,X2)) )),
% 2.00/0.62    inference(resolution,[],[f41,f56])).
% 2.00/0.62  fof(f56,plain,(
% 2.00/0.62    ( ! [X0,X1] : (sP1(X0,X1,k2_zfmisc_1(X0,X1))) )),
% 2.00/0.62    inference(equality_resolution,[],[f48])).
% 2.00/0.62  fof(f48,plain,(
% 2.00/0.62    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.00/0.62    inference(cnf_transformation,[],[f31])).
% 2.00/0.62  fof(f31,plain,(
% 2.00/0.62    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k2_zfmisc_1(X0,X1) != X2))),
% 2.00/0.62    inference(nnf_transformation,[],[f15])).
% 2.00/0.62  fof(f15,plain,(
% 2.00/0.62    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 2.00/0.62    inference(definition_folding,[],[f4,f14,f13])).
% 2.00/0.62  fof(f14,plain,(
% 2.00/0.62    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X3,X1,X0)))),
% 2.00/0.62    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.00/0.62  fof(f4,axiom,(
% 2.00/0.62    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 2.00/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 2.00/0.62  fof(f41,plain,(
% 2.00/0.62    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X4,X1,X0) | r2_hidden(X4,X2)) )),
% 2.00/0.62    inference(cnf_transformation,[],[f26])).
% 2.00/0.62  fof(f26,plain,(
% 2.00/0.62    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(sK6(X0,X1,X2),X1,X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sP0(sK6(X0,X1,X2),X1,X0) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X4,X1,X0)) & (sP0(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 2.00/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f25])).
% 2.00/0.62  fof(f25,plain,(
% 2.00/0.62    ! [X2,X1,X0] : (? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2))) => ((~sP0(sK6(X0,X1,X2),X1,X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sP0(sK6(X0,X1,X2),X1,X0) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 2.00/0.62    introduced(choice_axiom,[])).
% 2.00/0.62  fof(f24,plain,(
% 2.00/0.62    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X4,X1,X0)) & (sP0(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 2.00/0.62    inference(rectify,[],[f23])).
% 2.00/0.62  fof(f23,plain,(
% 2.00/0.62    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X3,X1,X0)) & (sP0(X3,X1,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 2.00/0.62    inference(nnf_transformation,[],[f14])).
% 2.00/0.62  fof(f75,plain,(
% 2.00/0.62    ( ! [X3] : (~r2_hidden(X3,k2_zfmisc_1(sK2,sK3)) | sP0(X3,sK2,sK3)) )),
% 2.00/0.62    inference(resolution,[],[f40,f57])).
% 2.00/0.62  fof(f57,plain,(
% 2.00/0.62    sP1(sK3,sK2,k2_zfmisc_1(sK2,sK3))),
% 2.00/0.62    inference(superposition,[],[f56,f32])).
% 2.00/0.62  fof(f32,plain,(
% 2.00/0.62    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK3,sK2)),
% 2.00/0.62    inference(cnf_transformation,[],[f17])).
% 2.00/0.62  fof(f40,plain,(
% 2.00/0.62    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | sP0(X4,X1,X0)) )),
% 2.00/0.62    inference(cnf_transformation,[],[f26])).
% 2.00/0.62  fof(f950,plain,(
% 2.00/0.62    ( ! [X0] : (~r2_hidden(X0,sK3) | ~r2_hidden(sK5(sK2,sK3),sK2)) )),
% 2.00/0.62    inference(subsumption_resolution,[],[f948,f35])).
% 2.00/0.62  fof(f948,plain,(
% 2.00/0.62    ( ! [X0] : (~r2_hidden(X0,sK3) | sK2 = sK3 | ~r2_hidden(sK5(sK2,sK3),sK2)) )),
% 2.00/0.62    inference(resolution,[],[f947,f39])).
% 2.00/0.62  fof(f39,plain,(
% 2.00/0.62    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | X0 = X1 | ~r2_hidden(sK5(X0,X1),X0)) )),
% 2.00/0.62    inference(cnf_transformation,[],[f22])).
% 2.00/0.62  fof(f947,plain,(
% 2.00/0.62    ( ! [X1] : (r2_hidden(sK5(sK2,sK3),sK3) | ~r2_hidden(X1,sK3)) )),
% 2.00/0.62    inference(resolution,[],[f945,f232])).
% 2.00/0.62  fof(f232,plain,(
% 2.00/0.62    ( ! [X0,X1] : (~r2_hidden(X1,sK2) | ~r2_hidden(X0,sK3) | r2_hidden(X1,sK3)) )),
% 2.00/0.62    inference(resolution,[],[f105,f155])).
% 2.00/0.62  fof(f155,plain,(
% 2.00/0.62    ( ! [X6,X4,X7,X5] : (~sP0(k4_tarski(X4,X5),X6,X7) | r2_hidden(X4,X7)) )),
% 2.00/0.62    inference(duplicate_literal_removal,[],[f154])).
% 2.00/0.62  fof(f154,plain,(
% 2.00/0.62    ( ! [X6,X4,X7,X5] : (r2_hidden(X4,X7) | ~sP0(k4_tarski(X4,X5),X6,X7) | ~sP0(k4_tarski(X4,X5),X6,X7)) )),
% 2.00/0.62    inference(superposition,[],[f44,f121])).
% 2.00/0.62  fof(f121,plain,(
% 2.00/0.62    ( ! [X2,X0,X3,X1] : (sK7(k4_tarski(X0,X1),X2,X3) = X0 | ~sP0(k4_tarski(X0,X1),X2,X3)) )),
% 2.00/0.62    inference(equality_resolution,[],[f103])).
% 2.00/0.62  fof(f103,plain,(
% 2.00/0.62    ( ! [X19,X17,X15,X18,X16] : (k4_tarski(X18,X19) != X15 | sK7(X15,X16,X17) = X18 | ~sP0(X15,X16,X17)) )),
% 2.00/0.62    inference(superposition,[],[f50,f46])).
% 2.00/0.62  fof(f50,plain,(
% 2.00/0.62    ( ! [X2,X0,X3,X1] : (k4_tarski(X0,X1) != k4_tarski(X2,X3) | X0 = X2) )),
% 2.00/0.62    inference(cnf_transformation,[],[f12])).
% 2.00/0.62  fof(f44,plain,(
% 2.00/0.62    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X2) | ~sP0(X0,X1,X2)) )),
% 2.00/0.62    inference(cnf_transformation,[],[f30])).
% 2.00/0.62  fof(f52,plain,(
% 2.00/0.62    o_0_0_xboole_0 != sK3),
% 2.00/0.62    inference(definition_unfolding,[],[f34,f36])).
% 2.00/0.62  fof(f34,plain,(
% 2.00/0.62    k1_xboole_0 != sK3),
% 2.00/0.62    inference(cnf_transformation,[],[f17])).
% 2.00/0.62  % SZS output end Proof for theBenchmark
% 2.00/0.62  % (8082)------------------------------
% 2.00/0.62  % (8082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.62  % (8082)Termination reason: Refutation
% 2.00/0.62  
% 2.00/0.62  % (8082)Memory used [KB]: 2174
% 2.00/0.62  % (8082)Time elapsed: 0.216 s
% 2.00/0.62  % (8082)------------------------------
% 2.00/0.62  % (8082)------------------------------
% 2.00/0.63  % (8052)Success in time 0.279 s
%------------------------------------------------------------------------------
