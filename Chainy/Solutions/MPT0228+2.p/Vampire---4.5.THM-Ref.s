%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0228+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:18 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :   32 (  46 expanded)
%              Number of leaves         :    6 (  14 expanded)
%              Depth                    :   10
%              Number of atoms          :  106 ( 167 expanded)
%              Number of equality atoms :   56 (  96 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1314,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1313,f1059])).

fof(f1059,plain,(
    ~ sQ30_eqProxy(sK4,sK5) ),
    inference(equality_proxy_replacement,[],[f565,f1042])).

fof(f1042,plain,(
    ! [X1,X0] :
      ( sQ30_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ30_eqProxy])])).

fof(f565,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f457])).

fof(f457,plain,
    ( k1_tarski(sK4) != k4_xboole_0(k2_tarski(sK4,sK5),k1_tarski(sK5))
    & sK4 != sK5 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f324,f456])).

fof(f456,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1))
        & X0 != X1 )
   => ( k1_tarski(sK4) != k4_xboole_0(k2_tarski(sK4,sK5),k1_tarski(sK5))
      & sK4 != sK5 ) ),
    introduced(choice_axiom,[])).

fof(f324,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f313])).

fof(f313,negated_conjecture,(
    ~ ! [X0,X1] :
        ( X0 != X1
       => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f312])).

fof(f312,conjecture,(
    ! [X0,X1] :
      ( X0 != X1
     => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_zfmisc_1)).

fof(f1313,plain,(
    sQ30_eqProxy(sK4,sK5) ),
    inference(resolution,[],[f1309,f1295])).

fof(f1295,plain,(
    ! [X0,X1] :
      ( ~ sQ30_eqProxy(X0,X1)
      | sQ30_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f1042])).

fof(f1309,plain,(
    sQ30_eqProxy(sK5,sK4) ),
    inference(resolution,[],[f1299,f1139])).

fof(f1139,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | sQ30_eqProxy(X0,X3) ) ),
    inference(equality_proxy_replacement,[],[f993,f1042])).

fof(f993,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f704])).

fof(f704,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f496])).

fof(f496,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK16(X0,X1) != X0
            | ~ r2_hidden(sK16(X0,X1),X1) )
          & ( sK16(X0,X1) = X0
            | r2_hidden(sK16(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f494,f495])).

% (25328)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_88 on theBenchmark
fof(f495,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK16(X0,X1) != X0
          | ~ r2_hidden(sK16(X0,X1),X1) )
        & ( sK16(X0,X1) = X0
          | r2_hidden(sK16(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f494,plain,(
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
    inference(rectify,[],[f493])).

fof(f493,plain,(
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
    inference(nnf_transformation,[],[f175])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f1299,plain,(
    r2_hidden(sK4,k1_tarski(sK5)) ),
    inference(subsumption_resolution,[],[f1297,f992])).

fof(f992,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f991])).

fof(f991,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f705])).

fof(f705,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f496])).

fof(f1297,plain,
    ( ~ r2_hidden(sK5,k1_tarski(sK5))
    | r2_hidden(sK4,k1_tarski(sK5)) ),
    inference(resolution,[],[f1058,f1217])).

fof(f1217,plain,(
    ! [X2,X0,X1] :
      ( sQ30_eqProxy(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X1),X2))
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(equality_proxy_replacement,[],[f853,f1042])).

fof(f853,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f539])).

fof(f539,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f538])).

fof(f538,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f298])).

fof(f298,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(f1058,plain,(
    ~ sQ30_eqProxy(k1_tarski(sK4),k4_xboole_0(k2_tarski(sK4,sK5),k1_tarski(sK5))) ),
    inference(equality_proxy_replacement,[],[f566,f1042])).

fof(f566,plain,(
    k1_tarski(sK4) != k4_xboole_0(k2_tarski(sK4,sK5),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f457])).
%------------------------------------------------------------------------------
