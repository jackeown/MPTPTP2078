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
% DateTime   : Thu Dec  3 12:38:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   85 (1149 expanded)
%              Number of leaves         :   12 ( 296 expanded)
%              Depth                    :   27
%              Number of atoms          :  310 (5944 expanded)
%              Number of equality atoms :  165 (4280 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f668,plain,(
    $false ),
    inference(subsumption_resolution,[],[f598,f547])).

% (21416)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
fof(f547,plain,(
    r2_hidden(sK0,k1_xboole_0) ),
    inference(resolution,[],[f544,f452])).

fof(f452,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f96,f436])).

fof(f436,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f435,f117])).

fof(f117,plain,
    ( sK1 != sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f105])).

fof(f105,plain,
    ( sK1 != sK1
    | sK1 != sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f71,f76])).

fof(f76,plain,
    ( sK1 = k1_tarski(sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f72,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f72,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f58,f37])).

fof(f37,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f16])).

% (21421)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f71,plain,
    ( sK1 != k1_tarski(sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f70])).

fof(f70,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f38])).

fof(f38,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f435,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f398])).

fof(f398,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f372,f76])).

fof(f372,plain,
    ( sK2 = k1_tarski(sK0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f320,f37])).

fof(f320,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f318,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f318,plain,
    ( r1_tarski(sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f309,f118])).

fof(f118,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f104])).

fof(f104,plain,
    ( sK1 != sK1
    | k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f40,f76])).

fof(f40,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f309,plain,
    ( r1_tarski(sK1,sK2)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f112,f146])).

fof(f146,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f44,f89])).

fof(f89,plain,
    ( sK0 = sK3(sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f88,f44])).

fof(f88,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK2)
      | sK0 = X4 ) ),
    inference(resolution,[],[f75,f69])).

fof(f69,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).

fof(f34,plain,(
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

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f75,plain,(
    ! [X2] :
      ( r2_hidden(X2,k1_tarski(sK0))
      | ~ r2_hidden(X2,sK2) ) ),
    inference(superposition,[],[f64,f37])).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & ~ r2_hidden(sK4(X0,X1,X2),X0) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & ~ r2_hidden(sK4(X0,X1,X2),X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f112,plain,(
    ! [X5] :
      ( ~ r2_hidden(sK0,X5)
      | r1_tarski(sK1,X5)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f60,f76])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f96,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f73,f68])).

fof(f68,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f73,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | r2_hidden(X0,sK1)
      | r2_hidden(X0,sK2) ) ),
    inference(superposition,[],[f66,f37])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f544,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(subsumption_resolution,[],[f543,f489])).

fof(f489,plain,(
    sK2 != k1_tarski(sK0) ),
    inference(trivial_inequality_removal,[],[f438])).

fof(f438,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK2 != k1_tarski(sK0) ),
    inference(backward_demodulation,[],[f39,f436])).

fof(f39,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f543,plain,
    ( sK2 = k1_tarski(sK0)
    | ~ r2_hidden(sK0,sK2) ),
    inference(trivial_inequality_removal,[],[f542])).

fof(f542,plain,
    ( sK0 != sK0
    | sK2 = k1_tarski(sK0)
    | ~ r2_hidden(sK0,sK2) ),
    inference(superposition,[],[f54,f537])).

fof(f537,plain,(
    sK0 = sK5(sK0,sK2) ),
    inference(subsumption_resolution,[],[f536,f489])).

fof(f536,plain,
    ( sK0 = sK5(sK0,sK2)
    | sK2 = k1_tarski(sK0) ),
    inference(equality_resolution,[],[f366])).

fof(f366,plain,(
    ! [X0] :
      ( sK0 != X0
      | sK0 = sK5(X0,sK2)
      | k1_tarski(X0) = sK2 ) ),
    inference(equality_factoring,[],[f93])).

fof(f93,plain,(
    ! [X6] :
      ( sK5(X6,sK2) = X6
      | sK0 = sK5(X6,sK2)
      | sK2 = k1_tarski(X6) ) ),
    inference(resolution,[],[f88,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | sK5(X0,X1) = X0
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != X0
      | k1_tarski(X0) = X1
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f598,plain,(
    ~ r2_hidden(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f544,f548])).

fof(f548,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f544,f146])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:12:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (21419)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (21418)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (21427)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (21417)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (21427)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (21435)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (21434)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (21413)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.34/0.53  % (21426)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.34/0.53  % (21436)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.34/0.53  % (21415)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.34/0.53  % SZS output start Proof for theBenchmark
% 1.34/0.53  fof(f668,plain,(
% 1.34/0.53    $false),
% 1.34/0.53    inference(subsumption_resolution,[],[f598,f547])).
% 1.34/0.53  % (21416)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.34/0.53  fof(f547,plain,(
% 1.34/0.53    r2_hidden(sK0,k1_xboole_0)),
% 1.34/0.53    inference(resolution,[],[f544,f452])).
% 1.34/0.53  fof(f452,plain,(
% 1.34/0.53    r2_hidden(sK0,sK2) | r2_hidden(sK0,k1_xboole_0)),
% 1.34/0.53    inference(backward_demodulation,[],[f96,f436])).
% 1.34/0.53  fof(f436,plain,(
% 1.34/0.53    k1_xboole_0 = sK1),
% 1.34/0.53    inference(subsumption_resolution,[],[f435,f117])).
% 1.34/0.53  fof(f117,plain,(
% 1.34/0.53    sK1 != sK2 | k1_xboole_0 = sK1),
% 1.34/0.53    inference(trivial_inequality_removal,[],[f105])).
% 1.34/0.53  fof(f105,plain,(
% 1.34/0.53    sK1 != sK1 | sK1 != sK2 | k1_xboole_0 = sK1),
% 1.34/0.53    inference(superposition,[],[f71,f76])).
% 1.34/0.53  fof(f76,plain,(
% 1.34/0.53    sK1 = k1_tarski(sK0) | k1_xboole_0 = sK1),
% 1.34/0.53    inference(resolution,[],[f72,f41])).
% 1.34/0.53  fof(f41,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.34/0.53    inference(cnf_transformation,[],[f24])).
% 1.34/0.53  fof(f24,plain,(
% 1.34/0.53    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.34/0.53    inference(flattening,[],[f23])).
% 1.34/0.53  fof(f23,plain,(
% 1.34/0.53    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.34/0.53    inference(nnf_transformation,[],[f14])).
% 1.34/0.53  fof(f14,axiom,(
% 1.34/0.53    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.34/0.53  fof(f72,plain,(
% 1.34/0.53    r1_tarski(sK1,k1_tarski(sK0))),
% 1.34/0.53    inference(superposition,[],[f58,f37])).
% 1.34/0.53  fof(f37,plain,(
% 1.34/0.53    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.34/0.53    inference(cnf_transformation,[],[f22])).
% 1.34/0.53  fof(f22,plain,(
% 1.34/0.53    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.34/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21])).
% 1.34/0.53  fof(f21,plain,(
% 1.34/0.53    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.34/0.53    introduced(choice_axiom,[])).
% 1.34/0.53  fof(f18,plain,(
% 1.34/0.53    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.34/0.53    inference(ennf_transformation,[],[f17])).
% 1.34/0.53  fof(f17,negated_conjecture,(
% 1.34/0.53    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.34/0.53    inference(negated_conjecture,[],[f16])).
% 1.34/0.54  % (21421)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.34/0.54  fof(f16,conjecture,(
% 1.34/0.54    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.34/0.54  fof(f58,plain,(
% 1.34/0.54    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f4])).
% 1.34/0.54  fof(f4,axiom,(
% 1.34/0.54    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.34/0.54  fof(f71,plain,(
% 1.34/0.54    sK1 != k1_tarski(sK0) | sK1 != sK2),
% 1.34/0.54    inference(inner_rewriting,[],[f70])).
% 1.34/0.54  fof(f70,plain,(
% 1.34/0.54    sK2 != k1_tarski(sK0) | sK1 != sK2),
% 1.34/0.54    inference(inner_rewriting,[],[f38])).
% 1.34/0.54  fof(f38,plain,(
% 1.34/0.54    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 1.34/0.54    inference(cnf_transformation,[],[f22])).
% 1.34/0.54  fof(f435,plain,(
% 1.34/0.54    sK1 = sK2 | k1_xboole_0 = sK1),
% 1.34/0.54    inference(duplicate_literal_removal,[],[f398])).
% 1.34/0.54  fof(f398,plain,(
% 1.34/0.54    sK1 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 1.34/0.54    inference(superposition,[],[f372,f76])).
% 1.34/0.54  fof(f372,plain,(
% 1.34/0.54    sK2 = k1_tarski(sK0) | k1_xboole_0 = sK1),
% 1.34/0.54    inference(superposition,[],[f320,f37])).
% 1.34/0.54  fof(f320,plain,(
% 1.34/0.54    sK2 = k2_xboole_0(sK1,sK2) | k1_xboole_0 = sK1),
% 1.34/0.54    inference(resolution,[],[f318,f55])).
% 1.34/0.54  fof(f55,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.34/0.54    inference(cnf_transformation,[],[f20])).
% 1.34/0.54  fof(f20,plain,(
% 1.34/0.54    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.34/0.54    inference(ennf_transformation,[],[f3])).
% 1.34/0.54  fof(f3,axiom,(
% 1.34/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.34/0.54  fof(f318,plain,(
% 1.34/0.54    r1_tarski(sK1,sK2) | k1_xboole_0 = sK1),
% 1.34/0.54    inference(subsumption_resolution,[],[f309,f118])).
% 1.34/0.54  fof(f118,plain,(
% 1.34/0.54    k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 1.34/0.54    inference(trivial_inequality_removal,[],[f104])).
% 1.34/0.54  fof(f104,plain,(
% 1.34/0.54    sK1 != sK1 | k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 1.34/0.54    inference(superposition,[],[f40,f76])).
% 1.34/0.54  fof(f40,plain,(
% 1.34/0.54    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 1.34/0.54    inference(cnf_transformation,[],[f22])).
% 1.34/0.54  fof(f309,plain,(
% 1.34/0.54    r1_tarski(sK1,sK2) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2),
% 1.34/0.54    inference(resolution,[],[f112,f146])).
% 1.34/0.54  fof(f146,plain,(
% 1.34/0.54    r2_hidden(sK0,sK2) | k1_xboole_0 = sK2),
% 1.34/0.54    inference(duplicate_literal_removal,[],[f145])).
% 1.34/0.54  fof(f145,plain,(
% 1.34/0.54    r2_hidden(sK0,sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 1.34/0.54    inference(superposition,[],[f44,f89])).
% 1.34/0.54  fof(f89,plain,(
% 1.34/0.54    sK0 = sK3(sK2) | k1_xboole_0 = sK2),
% 1.34/0.54    inference(resolution,[],[f88,f44])).
% 1.34/0.54  fof(f88,plain,(
% 1.34/0.54    ( ! [X4] : (~r2_hidden(X4,sK2) | sK0 = X4) )),
% 1.34/0.54    inference(resolution,[],[f75,f69])).
% 1.34/0.54  fof(f69,plain,(
% 1.34/0.54    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.34/0.54    inference(equality_resolution,[],[f51])).
% 1.34/0.54  fof(f51,plain,(
% 1.34/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.34/0.54    inference(cnf_transformation,[],[f35])).
% 1.34/0.54  fof(f35,plain,(
% 1.34/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.34/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).
% 1.34/0.54  fof(f34,plain,(
% 1.34/0.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 1.34/0.54    introduced(choice_axiom,[])).
% 1.34/0.54  fof(f33,plain,(
% 1.34/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.34/0.54    inference(rectify,[],[f32])).
% 1.34/0.54  fof(f32,plain,(
% 1.34/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.34/0.54    inference(nnf_transformation,[],[f5])).
% 1.34/0.54  fof(f5,axiom,(
% 1.34/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.34/0.54  fof(f75,plain,(
% 1.34/0.54    ( ! [X2] : (r2_hidden(X2,k1_tarski(sK0)) | ~r2_hidden(X2,sK2)) )),
% 1.34/0.54    inference(superposition,[],[f64,f37])).
% 1.34/0.54  fof(f64,plain,(
% 1.34/0.54    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.34/0.54    inference(equality_resolution,[],[f47])).
% 1.34/0.54  fof(f47,plain,(
% 1.34/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 1.34/0.54    inference(cnf_transformation,[],[f31])).
% 1.34/0.54  fof(f31,plain,(
% 1.34/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.34/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).
% 1.34/0.54  fof(f30,plain,(
% 1.34/0.54    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.34/0.54    introduced(choice_axiom,[])).
% 1.34/0.54  fof(f29,plain,(
% 1.34/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.34/0.54    inference(rectify,[],[f28])).
% 1.34/0.54  fof(f28,plain,(
% 1.34/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.34/0.54    inference(flattening,[],[f27])).
% 1.34/0.54  fof(f27,plain,(
% 1.34/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.34/0.54    inference(nnf_transformation,[],[f1])).
% 1.34/0.54  fof(f1,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.34/0.54  fof(f44,plain,(
% 1.34/0.54    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.34/0.54    inference(cnf_transformation,[],[f26])).
% 1.34/0.54  fof(f26,plain,(
% 1.34/0.54    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 1.34/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f25])).
% 1.34/0.54  fof(f25,plain,(
% 1.34/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.34/0.54    introduced(choice_axiom,[])).
% 1.34/0.54  fof(f19,plain,(
% 1.34/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.34/0.54    inference(ennf_transformation,[],[f2])).
% 1.34/0.54  fof(f2,axiom,(
% 1.34/0.54    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.34/0.54  fof(f112,plain,(
% 1.34/0.54    ( ! [X5] : (~r2_hidden(sK0,X5) | r1_tarski(sK1,X5) | k1_xboole_0 = sK1) )),
% 1.34/0.54    inference(superposition,[],[f60,f76])).
% 1.34/0.54  fof(f60,plain,(
% 1.34/0.54    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f36])).
% 1.34/0.54  fof(f36,plain,(
% 1.34/0.54    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.34/0.54    inference(nnf_transformation,[],[f13])).
% 1.34/0.54  fof(f13,axiom,(
% 1.34/0.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.34/0.54  fof(f96,plain,(
% 1.34/0.54    r2_hidden(sK0,sK2) | r2_hidden(sK0,sK1)),
% 1.34/0.54    inference(resolution,[],[f73,f68])).
% 1.34/0.54  fof(f68,plain,(
% 1.34/0.54    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 1.34/0.54    inference(equality_resolution,[],[f67])).
% 1.34/0.54  fof(f67,plain,(
% 1.34/0.54    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 1.34/0.54    inference(equality_resolution,[],[f52])).
% 1.34/0.54  fof(f52,plain,(
% 1.34/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.34/0.54    inference(cnf_transformation,[],[f35])).
% 1.34/0.54  fof(f73,plain,(
% 1.34/0.54    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(X0,sK1) | r2_hidden(X0,sK2)) )),
% 1.34/0.54    inference(superposition,[],[f66,f37])).
% 1.34/0.54  fof(f66,plain,(
% 1.34/0.54    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_xboole_0(X0,X1)) | r2_hidden(X4,X0) | r2_hidden(X4,X1)) )),
% 1.34/0.54    inference(equality_resolution,[],[f45])).
% 1.34/0.54  fof(f45,plain,(
% 1.34/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.34/0.54    inference(cnf_transformation,[],[f31])).
% 1.34/0.54  fof(f544,plain,(
% 1.34/0.54    ~r2_hidden(sK0,sK2)),
% 1.34/0.54    inference(subsumption_resolution,[],[f543,f489])).
% 1.34/0.54  fof(f489,plain,(
% 1.34/0.54    sK2 != k1_tarski(sK0)),
% 1.34/0.54    inference(trivial_inequality_removal,[],[f438])).
% 1.34/0.54  fof(f438,plain,(
% 1.34/0.54    k1_xboole_0 != k1_xboole_0 | sK2 != k1_tarski(sK0)),
% 1.34/0.54    inference(backward_demodulation,[],[f39,f436])).
% 1.34/0.54  fof(f39,plain,(
% 1.34/0.54    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 1.34/0.54    inference(cnf_transformation,[],[f22])).
% 1.34/0.54  fof(f543,plain,(
% 1.34/0.54    sK2 = k1_tarski(sK0) | ~r2_hidden(sK0,sK2)),
% 1.34/0.54    inference(trivial_inequality_removal,[],[f542])).
% 1.34/0.54  fof(f542,plain,(
% 1.34/0.54    sK0 != sK0 | sK2 = k1_tarski(sK0) | ~r2_hidden(sK0,sK2)),
% 1.34/0.54    inference(superposition,[],[f54,f537])).
% 1.34/0.54  fof(f537,plain,(
% 1.34/0.54    sK0 = sK5(sK0,sK2)),
% 1.34/0.54    inference(subsumption_resolution,[],[f536,f489])).
% 1.34/0.54  fof(f536,plain,(
% 1.34/0.54    sK0 = sK5(sK0,sK2) | sK2 = k1_tarski(sK0)),
% 1.34/0.54    inference(equality_resolution,[],[f366])).
% 1.34/0.54  fof(f366,plain,(
% 1.34/0.54    ( ! [X0] : (sK0 != X0 | sK0 = sK5(X0,sK2) | k1_tarski(X0) = sK2) )),
% 1.34/0.54    inference(equality_factoring,[],[f93])).
% 1.34/0.54  fof(f93,plain,(
% 1.34/0.54    ( ! [X6] : (sK5(X6,sK2) = X6 | sK0 = sK5(X6,sK2) | sK2 = k1_tarski(X6)) )),
% 1.34/0.54    inference(resolution,[],[f88,f53])).
% 1.34/0.54  fof(f53,plain,(
% 1.34/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | sK5(X0,X1) = X0 | k1_tarski(X0) = X1) )),
% 1.34/0.54    inference(cnf_transformation,[],[f35])).
% 1.34/0.54  fof(f54,plain,(
% 1.34/0.54    ( ! [X0,X1] : (sK5(X0,X1) != X0 | k1_tarski(X0) = X1 | ~r2_hidden(sK5(X0,X1),X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f35])).
% 1.34/0.54  fof(f598,plain,(
% 1.34/0.54    ~r2_hidden(sK0,k1_xboole_0)),
% 1.34/0.54    inference(backward_demodulation,[],[f544,f548])).
% 1.34/0.54  fof(f548,plain,(
% 1.34/0.54    k1_xboole_0 = sK2),
% 1.34/0.54    inference(resolution,[],[f544,f146])).
% 1.34/0.54  % SZS output end Proof for theBenchmark
% 1.34/0.54  % (21427)------------------------------
% 1.34/0.54  % (21427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (21427)Termination reason: Refutation
% 1.34/0.54  
% 1.34/0.54  % (21427)Memory used [KB]: 1918
% 1.34/0.54  % (21427)Time elapsed: 0.122 s
% 1.34/0.54  % (21427)------------------------------
% 1.34/0.54  % (21427)------------------------------
% 1.34/0.54  % (21428)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.34/0.54  % (21438)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.34/0.54  % (21442)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.34/0.54  % (21412)Success in time 0.178 s
%------------------------------------------------------------------------------
