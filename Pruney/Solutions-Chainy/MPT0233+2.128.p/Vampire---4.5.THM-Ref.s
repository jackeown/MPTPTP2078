%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 470 expanded)
%              Number of leaves         :   22 ( 139 expanded)
%              Depth                    :   16
%              Number of atoms          :  361 (1706 expanded)
%              Number of equality atoms :  192 ( 999 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f541,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f293,f298,f452,f513,f540])).

fof(f540,plain,(
    ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f539])).

fof(f539,plain,
    ( $false
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f531,f146])).

fof(f146,plain,(
    ! [X0,X1] : r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(resolution,[],[f97,f96])).

fof(f96,plain,(
    ! [X4,X2,X0] :
      ( ~ sP0(X0,X4,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( sK6(X0,X1,X2) != X0
              & sK6(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sK6(X0,X1,X2) = X0
            | sK6(X0,X1,X2) = X1
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK6(X0,X1,X2) != X0
            & sK6(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sK6(X0,X1,X2) = X0
          | sK6(X0,X1,X2) = X1
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

% (16318)Refutation not found, incomplete strategy% (16318)------------------------------
% (16318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (16318)Termination reason: Refutation not found, incomplete strategy

% (16318)Memory used [KB]: 1663
% (16318)Time elapsed: 0.130 s
% (16318)------------------------------
% (16318)------------------------------
fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( X0 != X3
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X0 = X3
              | X1 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

% (16298)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
fof(f97,plain,(
    ! [X0,X1] : sP0(X1,X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f65,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f21])).

% (16316)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f7,f20])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f531,plain,
    ( ~ r2_hidden(sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl7_9 ),
    inference(backward_demodulation,[],[f152,f233])).

fof(f233,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl7_9
  <=> k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f152,plain,(
    ~ r2_hidden(sK1,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(extensionality_resolution,[],[f94,f41])).

fof(f41,plain,(
    sK1 != sK4 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( sK1 != sK4
    & sK1 != sK3
    & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f16,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK1 != sK4
      & sK1 != sK3
      & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f94,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f52,f43])).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_enumset1)).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).

% (16310)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f513,plain,(
    ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f512])).

fof(f512,plain,
    ( $false
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f506,f146])).

fof(f506,plain,
    ( ~ r2_hidden(sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl7_8 ),
    inference(backward_demodulation,[],[f150,f229])).

fof(f229,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl7_8
  <=> k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f150,plain,(
    ~ r2_hidden(sK1,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
    inference(extensionality_resolution,[],[f94,f40])).

fof(f40,plain,(
    sK1 != sK3 ),
    inference(cnf_transformation,[],[f23])).

fof(f452,plain,(
    ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f451])).

fof(f451,plain,
    ( $false
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f389,f305])).

fof(f305,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl7_7 ),
    inference(superposition,[],[f146,f225])).

fof(f225,plain,
    ( k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl7_7
  <=> k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f389,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f335,f354])).

fof(f354,plain,
    ( ! [X1] : sK1 = X1
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f338,f141])).

fof(f141,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2) ),
    inference(resolution,[],[f138,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f138,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(trivial_inequality_removal,[],[f137])).

fof(f137,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f82,f74])).

fof(f74,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(definition_unfolding,[],[f42,f46])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f46])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f338,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
        | sK1 = X1 )
    | ~ spl7_7 ),
    inference(superposition,[],[f76,f323])).

fof(f323,plain,
    ( k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl7_7 ),
    inference(resolution,[],[f301,f140])).

fof(f140,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f138,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f301,plain,
    ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0)
    | ~ spl7_7 ),
    inference(superposition,[],[f75,f225])).

fof(f75,plain,(
    ! [X0,X1] : r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f43,f72])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f48,f43,f43,f43])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(f335,plain,
    ( ~ r2_hidden(sK4,k1_xboole_0)
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f151,f323])).

fof(f151,plain,(
    ~ r2_hidden(sK4,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(extensionality_resolution,[],[f94,f41])).

fof(f298,plain,
    ( spl7_6
    | spl7_7
    | spl7_8
    | spl7_9 ),
    inference(avatar_split_clause,[],[f294,f231,f227,f223,f174])).

fof(f174,plain,
    ( spl7_6
  <=> k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f294,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
    inference(resolution,[],[f73,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
      | k5_enumset1(X2,X2,X2,X2,X2,X2,X2) = X0
      | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = X0 ) ),
    inference(definition_unfolding,[],[f67,f72,f43,f43,f72])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f73,plain,(
    r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f39,f72,f72])).

fof(f39,plain,(
    r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f23])).

fof(f293,plain,(
    ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f292])).

fof(f292,plain,
    ( $false
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f274,f146])).

fof(f274,plain,
    ( ~ r2_hidden(sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f251,f272])).

fof(f272,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f252,f267])).

fof(f267,plain,
    ( sK2 = sK4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f266,f41])).

fof(f266,plain,
    ( sK1 = sK4
    | sK2 = sK4
    | ~ spl7_6 ),
    inference(resolution,[],[f243,f148])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X2))
      | X0 = X1
      | X1 = X2 ) ),
    inference(resolution,[],[f59,f97])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | X1 = X4
      | ~ r2_hidden(X4,X2)
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f243,plain,
    ( r2_hidden(sK4,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl7_6 ),
    inference(superposition,[],[f147,f176])).

fof(f176,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f174])).

fof(f147,plain,(
    ! [X2,X3] : r2_hidden(X2,k5_enumset1(X3,X3,X3,X3,X3,X3,X2)) ),
    inference(resolution,[],[f97,f95])).

fof(f95,plain,(
    ! [X4,X2,X1] :
      ( ~ sP0(X4,X1,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f252,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK4)
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f176,f248])).

fof(f248,plain,
    ( sK2 = sK3
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f247,f40])).

fof(f247,plain,
    ( sK1 = sK3
    | sK2 = sK3
    | ~ spl7_6 ),
    inference(resolution,[],[f242,f148])).

fof(f242,plain,
    ( r2_hidden(sK3,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl7_6 ),
    inference(superposition,[],[f146,f176])).

fof(f251,plain,
    ( ~ r2_hidden(sK1,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f150,f248])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:04:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.45  % (16288)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.49  % (16304)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.50  % (16295)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.50  % (16311)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.51  % (16303)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.51  % (16312)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.51  % (16291)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.51  % (16292)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (16289)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.51  % (16289)Refutation not found, incomplete strategy% (16289)------------------------------
% 0.22/0.51  % (16289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (16289)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (16289)Memory used [KB]: 1663
% 0.22/0.51  % (16289)Time elapsed: 0.097 s
% 0.22/0.51  % (16289)------------------------------
% 0.22/0.51  % (16289)------------------------------
% 0.22/0.51  % (16294)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (16300)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  % (16296)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.53  % (16290)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (16317)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.53  % (16293)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (16313)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (16314)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (16305)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (16306)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  % (16294)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (16318)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f541,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f293,f298,f452,f513,f540])).
% 0.22/0.54  fof(f540,plain,(
% 0.22/0.54    ~spl7_9),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f539])).
% 0.22/0.54  fof(f539,plain,(
% 0.22/0.54    $false | ~spl7_9),
% 0.22/0.54    inference(subsumption_resolution,[],[f531,f146])).
% 0.22/0.54  fof(f146,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 0.22/0.54    inference(resolution,[],[f97,f96])).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    ( ! [X4,X2,X0] : (~sP0(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 0.22/0.54    inference(equality_resolution,[],[f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP0(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((sK6(X0,X1,X2) != X0 & sK6(X0,X1,X2) != X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sK6(X0,X1,X2) = X0 | sK6(X0,X1,X2) = X1 | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f33,f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK6(X0,X1,X2) != X0 & sK6(X0,X1,X2) != X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sK6(X0,X1,X2) = X0 | sK6(X0,X1,X2) = X1 | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  % (16318)Refutation not found, incomplete strategy% (16318)------------------------------
% 0.22/0.54  % (16318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (16318)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (16318)Memory used [KB]: 1663
% 0.22/0.54  % (16318)Time elapsed: 0.130 s
% 0.22/0.54  % (16318)------------------------------
% 0.22/0.54  % (16318)------------------------------
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.54    inference(rectify,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.22/0.54    inference(flattening,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.22/0.54    inference(nnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.54  % (16298)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    ( ! [X0,X1] : (sP0(X1,X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 0.22/0.54    inference(equality_resolution,[],[f84])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 0.22/0.54    inference(definition_unfolding,[],[f65,f72])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f45,f58])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_enumset1)).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 0.22/0.54    inference(nnf_transformation,[],[f21])).
% 0.22/0.54  % (16316)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.22/0.54    inference(definition_folding,[],[f7,f20])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.22/0.54  fof(f531,plain,(
% 0.22/0.54    ~r2_hidden(sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | ~spl7_9),
% 0.22/0.54    inference(backward_demodulation,[],[f152,f233])).
% 0.22/0.54  fof(f233,plain,(
% 0.22/0.54    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) | ~spl7_9),
% 0.22/0.54    inference(avatar_component_clause,[],[f231])).
% 0.22/0.54  fof(f231,plain,(
% 0.22/0.54    spl7_9 <=> k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.54  fof(f152,plain,(
% 0.22/0.54    ~r2_hidden(sK1,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))),
% 0.22/0.54    inference(extensionality_resolution,[],[f94,f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    sK1 != sK4),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    sK1 != sK4 & sK1 != sK3 & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f16,f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK1 != sK4 & sK1 != sK3 & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.22/0.54    inference(ennf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.22/0.54    inference(negated_conjecture,[],[f14])).
% 0.22/0.54  fof(f14,conjecture,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    ( ! [X0,X3] : (~r2_hidden(X3,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) | X0 = X3) )),
% 0.22/0.54    inference(equality_resolution,[],[f80])).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 0.22/0.54    inference(definition_unfolding,[],[f52,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_enumset1)).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).
% 0.22/0.54  % (16310)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.54    inference(rectify,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.54  fof(f513,plain,(
% 0.22/0.54    ~spl7_8),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f512])).
% 0.22/0.54  fof(f512,plain,(
% 0.22/0.54    $false | ~spl7_8),
% 0.22/0.54    inference(subsumption_resolution,[],[f506,f146])).
% 0.22/0.54  fof(f506,plain,(
% 0.22/0.54    ~r2_hidden(sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | ~spl7_8),
% 0.22/0.54    inference(backward_demodulation,[],[f150,f229])).
% 0.22/0.54  fof(f229,plain,(
% 0.22/0.54    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) | ~spl7_8),
% 0.22/0.54    inference(avatar_component_clause,[],[f227])).
% 0.22/0.54  fof(f227,plain,(
% 0.22/0.54    spl7_8 <=> k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.54  fof(f150,plain,(
% 0.22/0.54    ~r2_hidden(sK1,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))),
% 0.22/0.54    inference(extensionality_resolution,[],[f94,f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    sK1 != sK3),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f452,plain,(
% 0.22/0.54    ~spl7_7),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f451])).
% 0.22/0.54  fof(f451,plain,(
% 0.22/0.54    $false | ~spl7_7),
% 0.22/0.54    inference(subsumption_resolution,[],[f389,f305])).
% 0.22/0.54  fof(f305,plain,(
% 0.22/0.54    r2_hidden(sK1,k1_xboole_0) | ~spl7_7),
% 0.22/0.54    inference(superposition,[],[f146,f225])).
% 0.22/0.54  fof(f225,plain,(
% 0.22/0.54    k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) | ~spl7_7),
% 0.22/0.54    inference(avatar_component_clause,[],[f223])).
% 0.22/0.54  fof(f223,plain,(
% 0.22/0.54    spl7_7 <=> k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.54  fof(f389,plain,(
% 0.22/0.54    ~r2_hidden(sK1,k1_xboole_0) | ~spl7_7),
% 0.22/0.54    inference(backward_demodulation,[],[f335,f354])).
% 0.22/0.54  fof(f354,plain,(
% 0.22/0.54    ( ! [X1] : (sK1 = X1) ) | ~spl7_7),
% 0.22/0.54    inference(subsumption_resolution,[],[f338,f141])).
% 0.22/0.54  fof(f141,plain,(
% 0.22/0.54    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)) )),
% 0.22/0.54    inference(resolution,[],[f138,f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.54  fof(f138,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f137])).
% 0.22/0.54  fof(f137,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.54    inference(superposition,[],[f82,f74])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f42,f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f56,f46])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.54    inference(nnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.54  fof(f338,plain,(
% 0.22/0.54    ( ! [X1] : (k1_xboole_0 != k3_xboole_0(k1_xboole_0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) | sK1 = X1) ) | ~spl7_7),
% 0.22/0.54    inference(superposition,[],[f76,f323])).
% 0.22/0.54  fof(f323,plain,(
% 0.22/0.54    k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl7_7),
% 0.22/0.54    inference(resolution,[],[f301,f140])).
% 0.22/0.54  fof(f140,plain,(
% 0.22/0.54    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 0.22/0.54    inference(resolution,[],[f138,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(flattening,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.54  fof(f301,plain,(
% 0.22/0.54    r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) | ~spl7_7),
% 0.22/0.54    inference(superposition,[],[f75,f225])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f44,f43,f72])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) | X0 = X1) )),
% 0.22/0.54    inference(definition_unfolding,[],[f48,f43,f43,f43])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X0,X1] : (X0 = X1 | k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 | k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).
% 0.22/0.54  fof(f335,plain,(
% 0.22/0.54    ~r2_hidden(sK4,k1_xboole_0) | ~spl7_7),
% 0.22/0.54    inference(backward_demodulation,[],[f151,f323])).
% 0.22/0.54  fof(f151,plain,(
% 0.22/0.54    ~r2_hidden(sK4,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.22/0.54    inference(extensionality_resolution,[],[f94,f41])).
% 0.22/0.54  fof(f298,plain,(
% 0.22/0.54    spl7_6 | spl7_7 | spl7_8 | spl7_9),
% 0.22/0.54    inference(avatar_split_clause,[],[f294,f231,f227,f223,f174])).
% 0.22/0.54  fof(f174,plain,(
% 0.22/0.54    spl7_6 <=> k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.54  fof(f294,plain,(
% 0.22/0.54    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) | k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)),
% 0.22/0.54    inference(resolution,[],[f73,f89])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) | k5_enumset1(X2,X2,X2,X2,X2,X2,X2) = X0 | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = X0) )),
% 0.22/0.54    inference(definition_unfolding,[],[f67,f72,f43,f43,f72])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.22/0.54    inference(flattening,[],[f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.22/0.54    inference(nnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 0.22/0.54    inference(definition_unfolding,[],[f39,f72,f72])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f293,plain,(
% 0.22/0.54    ~spl7_6),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f292])).
% 0.22/0.54  fof(f292,plain,(
% 0.22/0.54    $false | ~spl7_6),
% 0.22/0.54    inference(subsumption_resolution,[],[f274,f146])).
% 0.22/0.54  fof(f274,plain,(
% 0.22/0.54    ~r2_hidden(sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | ~spl7_6),
% 0.22/0.54    inference(backward_demodulation,[],[f251,f272])).
% 0.22/0.54  fof(f272,plain,(
% 0.22/0.54    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) | ~spl7_6),
% 0.22/0.54    inference(backward_demodulation,[],[f252,f267])).
% 0.22/0.54  fof(f267,plain,(
% 0.22/0.54    sK2 = sK4 | ~spl7_6),
% 0.22/0.54    inference(subsumption_resolution,[],[f266,f41])).
% 0.22/0.54  fof(f266,plain,(
% 0.22/0.54    sK1 = sK4 | sK2 = sK4 | ~spl7_6),
% 0.22/0.54    inference(resolution,[],[f243,f148])).
% 0.22/0.54  fof(f148,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X2)) | X0 = X1 | X1 = X2) )),
% 0.22/0.54    inference(resolution,[],[f59,f97])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | X1 = X4 | ~r2_hidden(X4,X2) | X0 = X4) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  fof(f243,plain,(
% 0.22/0.54    r2_hidden(sK4,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | ~spl7_6),
% 0.22/0.54    inference(superposition,[],[f147,f176])).
% 0.22/0.54  fof(f176,plain,(
% 0.22/0.54    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) | ~spl7_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f174])).
% 0.22/0.54  fof(f147,plain,(
% 0.22/0.54    ( ! [X2,X3] : (r2_hidden(X2,k5_enumset1(X3,X3,X3,X3,X3,X3,X2))) )),
% 0.22/0.54    inference(resolution,[],[f97,f95])).
% 0.22/0.55  fof(f95,plain,(
% 0.22/0.55    ( ! [X4,X2,X1] : (~sP0(X4,X1,X2) | r2_hidden(X4,X2)) )),
% 0.22/0.55    inference(equality_resolution,[],[f61])).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | ~sP0(X0,X1,X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f35])).
% 0.22/0.55  fof(f252,plain,(
% 0.22/0.55    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK4) | ~spl7_6),
% 0.22/0.55    inference(backward_demodulation,[],[f176,f248])).
% 0.22/0.55  fof(f248,plain,(
% 0.22/0.55    sK2 = sK3 | ~spl7_6),
% 0.22/0.55    inference(subsumption_resolution,[],[f247,f40])).
% 0.22/0.55  fof(f247,plain,(
% 0.22/0.55    sK1 = sK3 | sK2 = sK3 | ~spl7_6),
% 0.22/0.55    inference(resolution,[],[f242,f148])).
% 0.22/0.55  fof(f242,plain,(
% 0.22/0.55    r2_hidden(sK3,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | ~spl7_6),
% 0.22/0.55    inference(superposition,[],[f146,f176])).
% 0.22/0.55  fof(f251,plain,(
% 0.22/0.55    ~r2_hidden(sK1,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl7_6),
% 0.22/0.55    inference(backward_demodulation,[],[f150,f248])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (16294)------------------------------
% 0.22/0.55  % (16294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (16294)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (16294)Memory used [KB]: 10874
% 0.22/0.55  % (16294)Time elapsed: 0.087 s
% 0.22/0.55  % (16294)------------------------------
% 0.22/0.55  % (16294)------------------------------
% 0.22/0.55  % (16297)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (16305)Refutation not found, incomplete strategy% (16305)------------------------------
% 0.22/0.55  % (16305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (16305)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (16305)Memory used [KB]: 10618
% 0.22/0.55  % (16305)Time elapsed: 0.140 s
% 0.22/0.55  % (16305)------------------------------
% 0.22/0.55  % (16305)------------------------------
% 0.22/0.55  % (16308)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (16286)Success in time 0.187 s
%------------------------------------------------------------------------------
