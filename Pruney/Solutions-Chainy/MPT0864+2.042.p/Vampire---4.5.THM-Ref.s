%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 205 expanded)
%              Number of leaves         :   11 (  57 expanded)
%              Depth                    :   24
%              Number of atoms          :  253 (1068 expanded)
%              Number of equality atoms :  164 ( 717 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f527,plain,(
    $false ),
    inference(resolution,[],[f500,f58])).

fof(f58,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f500,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[],[f77,f479])).

fof(f479,plain,(
    k1_xboole_0 = k2_tarski(sK0,sK0) ),
    inference(resolution,[],[f439,f69])).

fof(f69,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
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
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
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
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f439,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK0))
    | k1_xboole_0 = k2_tarski(sK0,sK0) ),
    inference(trivial_inequality_removal,[],[f437])).

fof(f437,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK0))
    | k1_xboole_0 = k2_tarski(sK0,sK0) ),
    inference(backward_demodulation,[],[f308,f414])).

fof(f414,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f385,f58])).

fof(f385,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | sK0 = sK1 ),
    inference(superposition,[],[f77,f365])).

fof(f365,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK0)
    | sK0 = sK1 ),
    inference(resolution,[],[f345,f69])).

fof(f345,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK0))
    | k1_xboole_0 = k2_tarski(sK0,sK0)
    | sK0 = sK1 ),
    inference(trivial_inequality_removal,[],[f344])).

fof(f344,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK0))
    | k1_xboole_0 = k2_tarski(sK0,sK0)
    | sK0 = sK1 ),
    inference(superposition,[],[f342,f84])).

fof(f84,plain,
    ( sK0 = sK2
    | sK0 = sK1 ),
    inference(superposition,[],[f83,f82])).

fof(f82,plain,(
    k2_mcart_1(sK0) = sK2 ),
    inference(superposition,[],[f38,f35])).

fof(f35,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( sK0 = k2_mcart_1(sK0)
      | sK0 = k1_mcart_1(sK0) )
    & sK0 = k4_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( sK0 = k2_mcart_1(sK0)
        | sK0 = k1_mcart_1(sK0) )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK0 ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2,X1] : k4_tarski(X1,X2) = sK0
   => sK0 = k4_tarski(sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f38,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f83,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f36,f81])).

fof(f81,plain,(
    k1_mcart_1(sK0) = sK1 ),
    inference(superposition,[],[f37,f35])).

fof(f37,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f36,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f342,plain,
    ( sK0 != sK2
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK0))
    | k1_xboole_0 = k2_tarski(sK0,sK0) ),
    inference(inner_rewriting,[],[f339])).

fof(f339,plain,
    ( sK0 != sK2
    | ~ r2_hidden(sK2,k2_tarski(sK2,sK0))
    | k1_xboole_0 = k2_tarski(sK2,sK0) ),
    inference(duplicate_literal_removal,[],[f330])).

fof(f330,plain,
    ( sK0 != sK2
    | ~ r2_hidden(sK2,k2_tarski(sK2,sK0))
    | k1_xboole_0 = k2_tarski(sK2,sK0)
    | k1_xboole_0 = k2_tarski(sK2,sK0) ),
    inference(superposition,[],[f108,f323])).

fof(f323,plain,
    ( sK2 = sK3(k2_tarski(sK2,sK0))
    | k1_xboole_0 = k2_tarski(sK2,sK0) ),
    inference(resolution,[],[f292,f71])).

fof(f71,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f292,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,k2_tarski(X0,sK0))
      | k1_xboole_0 = k2_tarski(X0,sK0)
      | sK3(k2_tarski(X0,sK0)) = X0 ) ),
    inference(equality_resolution,[],[f208])).

fof(f208,plain,(
    ! [X2,X3] :
      ( sK0 != X3
      | ~ r2_hidden(sK2,k2_tarski(X2,X3))
      | k1_xboole_0 = k2_tarski(X2,X3)
      | sK3(k2_tarski(X2,X3)) = X2 ) ),
    inference(duplicate_literal_removal,[],[f197])).

fof(f197,plain,(
    ! [X2,X3] :
      ( sK0 != X3
      | ~ r2_hidden(sK2,k2_tarski(X2,X3))
      | k1_xboole_0 = k2_tarski(X2,X3)
      | sK3(k2_tarski(X2,X3)) = X2
      | k1_xboole_0 = k2_tarski(X2,X3) ) ),
    inference(superposition,[],[f108,f104])).

fof(f104,plain,(
    ! [X6,X7] :
      ( sK3(k2_tarski(X6,X7)) = X6
      | sK3(k2_tarski(X6,X7)) = X7
      | k1_xboole_0 = k2_tarski(X6,X7) ) ),
    inference(resolution,[],[f72,f44])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f72,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f108,plain,(
    ! [X0] :
      ( sK0 != sK3(X0)
      | ~ r2_hidden(sK2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f46,f35])).

fof(f46,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK3(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f308,plain,
    ( sK0 != sK1
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK0))
    | k1_xboole_0 = k2_tarski(sK0,sK0) ),
    inference(inner_rewriting,[],[f303])).

fof(f303,plain,
    ( sK0 != sK1
    | ~ r2_hidden(sK1,k2_tarski(sK1,sK0))
    | k1_xboole_0 = k2_tarski(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f298])).

fof(f298,plain,
    ( sK0 != sK1
    | ~ r2_hidden(sK1,k2_tarski(sK1,sK0))
    | k1_xboole_0 = k2_tarski(sK1,sK0)
    | k1_xboole_0 = k2_tarski(sK1,sK0) ),
    inference(superposition,[],[f106,f291])).

fof(f291,plain,
    ( sK1 = sK3(k2_tarski(sK1,sK0))
    | k1_xboole_0 = k2_tarski(sK1,sK0) ),
    inference(resolution,[],[f290,f71])).

fof(f290,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,k2_tarski(X0,sK0))
      | k1_xboole_0 = k2_tarski(X0,sK0)
      | sK3(k2_tarski(X0,sK0)) = X0 ) ),
    inference(equality_resolution,[],[f206])).

fof(f206,plain,(
    ! [X8,X9] :
      ( sK0 != X9
      | ~ r2_hidden(sK1,k2_tarski(X8,X9))
      | k1_xboole_0 = k2_tarski(X8,X9)
      | sK3(k2_tarski(X8,X9)) = X8 ) ),
    inference(duplicate_literal_removal,[],[f199])).

fof(f199,plain,(
    ! [X8,X9] :
      ( sK0 != X9
      | ~ r2_hidden(sK1,k2_tarski(X8,X9))
      | k1_xboole_0 = k2_tarski(X8,X9)
      | sK3(k2_tarski(X8,X9)) = X8
      | k1_xboole_0 = k2_tarski(X8,X9) ) ),
    inference(superposition,[],[f106,f104])).

fof(f106,plain,(
    ! [X0] :
      ( sK0 != sK3(X0)
      | ~ r2_hidden(sK1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f45,f35])).

fof(f45,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK3(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f77,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(resolution,[],[f69,f59])).

fof(f59,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:52:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (7207)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.50  % (7215)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.50  % (7197)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (7207)Refutation not found, incomplete strategy% (7207)------------------------------
% 0.21/0.51  % (7207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (7207)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (7207)Memory used [KB]: 10618
% 0.21/0.51  % (7207)Time elapsed: 0.088 s
% 0.21/0.51  % (7207)------------------------------
% 0.21/0.51  % (7207)------------------------------
% 0.21/0.52  % (7195)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (7199)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (7222)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.52  % (7222)Refutation not found, incomplete strategy% (7222)------------------------------
% 0.21/0.52  % (7222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (7222)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (7222)Memory used [KB]: 6140
% 0.21/0.52  % (7222)Time elapsed: 0.107 s
% 0.21/0.52  % (7222)------------------------------
% 0.21/0.52  % (7222)------------------------------
% 0.21/0.52  % (7204)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (7198)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (7205)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (7203)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (7206)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (7217)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (7220)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.53  % (7220)Refutation not found, incomplete strategy% (7220)------------------------------
% 0.21/0.53  % (7220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (7220)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (7220)Memory used [KB]: 6140
% 0.21/0.53  % (7220)Time elapsed: 0.125 s
% 0.21/0.53  % (7220)------------------------------
% 0.21/0.53  % (7220)------------------------------
% 0.21/0.53  % (7209)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (7212)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (7214)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (7213)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (7208)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (7223)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (7200)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (7196)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (7224)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (7224)Refutation not found, incomplete strategy% (7224)------------------------------
% 0.21/0.54  % (7224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7224)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (7224)Memory used [KB]: 1663
% 0.21/0.54  % (7224)Time elapsed: 0.001 s
% 0.21/0.54  % (7224)------------------------------
% 0.21/0.54  % (7224)------------------------------
% 0.21/0.54  % (7196)Refutation not found, incomplete strategy% (7196)------------------------------
% 0.21/0.54  % (7196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7196)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (7196)Memory used [KB]: 1663
% 0.21/0.54  % (7196)Time elapsed: 0.138 s
% 0.21/0.54  % (7196)------------------------------
% 0.21/0.54  % (7196)------------------------------
% 0.21/0.54  % (7201)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (7205)Refutation not found, incomplete strategy% (7205)------------------------------
% 0.21/0.55  % (7205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (7205)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (7205)Memory used [KB]: 10746
% 0.21/0.55  % (7205)Time elapsed: 0.121 s
% 0.21/0.55  % (7205)------------------------------
% 0.21/0.55  % (7205)------------------------------
% 0.21/0.55  % (7218)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (7221)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (7216)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (7221)Refutation not found, incomplete strategy% (7221)------------------------------
% 0.21/0.55  % (7221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (7221)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (7221)Memory used [KB]: 6140
% 0.21/0.55  % (7221)Time elapsed: 0.142 s
% 0.21/0.55  % (7221)------------------------------
% 0.21/0.55  % (7221)------------------------------
% 0.21/0.55  % (7213)Refutation not found, incomplete strategy% (7213)------------------------------
% 0.21/0.55  % (7213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (7213)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (7213)Memory used [KB]: 1663
% 0.21/0.55  % (7213)Time elapsed: 0.143 s
% 0.21/0.55  % (7213)------------------------------
% 0.21/0.55  % (7213)------------------------------
% 0.21/0.55  % (7219)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (7219)Refutation not found, incomplete strategy% (7219)------------------------------
% 0.21/0.55  % (7219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (7219)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (7219)Memory used [KB]: 10746
% 0.21/0.55  % (7219)Time elapsed: 0.151 s
% 0.21/0.55  % (7219)------------------------------
% 0.21/0.55  % (7219)------------------------------
% 0.21/0.55  % (7200)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f527,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(resolution,[],[f500,f58])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    v1_xboole_0(k1_xboole_0)),
% 0.21/0.55    inference(cnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    v1_xboole_0(k1_xboole_0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.55  fof(f500,plain,(
% 0.21/0.55    ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.55    inference(superposition,[],[f77,f479])).
% 0.21/0.55  fof(f479,plain,(
% 0.21/0.55    k1_xboole_0 = k2_tarski(sK0,sK0)),
% 0.21/0.55    inference(resolution,[],[f439,f69])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 0.21/0.55    inference(equality_resolution,[],[f68])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 0.21/0.55    inference(equality_resolution,[],[f49])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.55    inference(rectify,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.55    inference(flattening,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.55    inference(nnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.21/0.55  fof(f439,plain,(
% 0.21/0.55    ~r2_hidden(sK0,k2_tarski(sK0,sK0)) | k1_xboole_0 = k2_tarski(sK0,sK0)),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f437])).
% 0.21/0.55  fof(f437,plain,(
% 0.21/0.55    sK0 != sK0 | ~r2_hidden(sK0,k2_tarski(sK0,sK0)) | k1_xboole_0 = k2_tarski(sK0,sK0)),
% 0.21/0.55    inference(backward_demodulation,[],[f308,f414])).
% 0.21/0.55  fof(f414,plain,(
% 0.21/0.55    sK0 = sK1),
% 0.21/0.55    inference(resolution,[],[f385,f58])).
% 0.21/0.55  fof(f385,plain,(
% 0.21/0.55    ~v1_xboole_0(k1_xboole_0) | sK0 = sK1),
% 0.21/0.55    inference(superposition,[],[f77,f365])).
% 0.21/0.55  fof(f365,plain,(
% 0.21/0.55    k1_xboole_0 = k2_tarski(sK0,sK0) | sK0 = sK1),
% 0.21/0.55    inference(resolution,[],[f345,f69])).
% 0.21/0.55  fof(f345,plain,(
% 0.21/0.55    ~r2_hidden(sK0,k2_tarski(sK0,sK0)) | k1_xboole_0 = k2_tarski(sK0,sK0) | sK0 = sK1),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f344])).
% 0.21/0.55  fof(f344,plain,(
% 0.21/0.55    sK0 != sK0 | ~r2_hidden(sK0,k2_tarski(sK0,sK0)) | k1_xboole_0 = k2_tarski(sK0,sK0) | sK0 = sK1),
% 0.21/0.55    inference(superposition,[],[f342,f84])).
% 0.21/0.55  fof(f84,plain,(
% 0.21/0.55    sK0 = sK2 | sK0 = sK1),
% 0.21/0.55    inference(superposition,[],[f83,f82])).
% 0.21/0.55  fof(f82,plain,(
% 0.21/0.55    k2_mcart_1(sK0) = sK2),
% 0.21/0.55    inference(superposition,[],[f38,f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    (sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18,f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & ? [X2,X1] : k4_tarski(X1,X2) = sK0)),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ? [X2,X1] : k4_tarski(X1,X2) = sK0 => sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 0.21/0.55    inference(ennf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,negated_conjecture,(
% 0.21/0.55    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.55    inference(negated_conjecture,[],[f13])).
% 0.21/0.55  fof(f13,conjecture,(
% 0.21/0.55    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.55  fof(f83,plain,(
% 0.21/0.55    sK0 = k2_mcart_1(sK0) | sK0 = sK1),
% 0.21/0.55    inference(backward_demodulation,[],[f36,f81])).
% 0.21/0.55  fof(f81,plain,(
% 0.21/0.55    k1_mcart_1(sK0) = sK1),
% 0.21/0.55    inference(superposition,[],[f37,f35])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f11])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f342,plain,(
% 0.21/0.55    sK0 != sK2 | ~r2_hidden(sK0,k2_tarski(sK0,sK0)) | k1_xboole_0 = k2_tarski(sK0,sK0)),
% 0.21/0.55    inference(inner_rewriting,[],[f339])).
% 0.21/0.55  fof(f339,plain,(
% 0.21/0.55    sK0 != sK2 | ~r2_hidden(sK2,k2_tarski(sK2,sK0)) | k1_xboole_0 = k2_tarski(sK2,sK0)),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f330])).
% 0.21/0.55  fof(f330,plain,(
% 0.21/0.55    sK0 != sK2 | ~r2_hidden(sK2,k2_tarski(sK2,sK0)) | k1_xboole_0 = k2_tarski(sK2,sK0) | k1_xboole_0 = k2_tarski(sK2,sK0)),
% 0.21/0.55    inference(superposition,[],[f108,f323])).
% 0.21/0.55  fof(f323,plain,(
% 0.21/0.55    sK2 = sK3(k2_tarski(sK2,sK0)) | k1_xboole_0 = k2_tarski(sK2,sK0)),
% 0.21/0.55    inference(resolution,[],[f292,f71])).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 0.21/0.55    inference(equality_resolution,[],[f70])).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 0.21/0.55    inference(equality_resolution,[],[f48])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  fof(f292,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(sK2,k2_tarski(X0,sK0)) | k1_xboole_0 = k2_tarski(X0,sK0) | sK3(k2_tarski(X0,sK0)) = X0) )),
% 0.21/0.55    inference(equality_resolution,[],[f208])).
% 0.21/0.55  fof(f208,plain,(
% 0.21/0.55    ( ! [X2,X3] : (sK0 != X3 | ~r2_hidden(sK2,k2_tarski(X2,X3)) | k1_xboole_0 = k2_tarski(X2,X3) | sK3(k2_tarski(X2,X3)) = X2) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f197])).
% 0.21/0.55  fof(f197,plain,(
% 0.21/0.55    ( ! [X2,X3] : (sK0 != X3 | ~r2_hidden(sK2,k2_tarski(X2,X3)) | k1_xboole_0 = k2_tarski(X2,X3) | sK3(k2_tarski(X2,X3)) = X2 | k1_xboole_0 = k2_tarski(X2,X3)) )),
% 0.21/0.55    inference(superposition,[],[f108,f104])).
% 0.21/0.55  fof(f104,plain,(
% 0.21/0.55    ( ! [X6,X7] : (sK3(k2_tarski(X6,X7)) = X6 | sK3(k2_tarski(X6,X7)) = X7 | k1_xboole_0 = k2_tarski(X6,X7)) )),
% 0.21/0.55    inference(resolution,[],[f72,f44])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.55    inference(ennf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,axiom,(
% 0.21/0.55    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 0.21/0.55    inference(equality_resolution,[],[f47])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  fof(f108,plain,(
% 0.21/0.55    ( ! [X0] : (sK0 != sK3(X0) | ~r2_hidden(sK2,X0) | k1_xboole_0 = X0) )),
% 0.21/0.55    inference(superposition,[],[f46,f35])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK3(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f308,plain,(
% 0.21/0.55    sK0 != sK1 | ~r2_hidden(sK0,k2_tarski(sK0,sK0)) | k1_xboole_0 = k2_tarski(sK0,sK0)),
% 0.21/0.55    inference(inner_rewriting,[],[f303])).
% 0.21/0.55  fof(f303,plain,(
% 0.21/0.55    sK0 != sK1 | ~r2_hidden(sK1,k2_tarski(sK1,sK0)) | k1_xboole_0 = k2_tarski(sK1,sK0)),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f298])).
% 0.21/0.55  fof(f298,plain,(
% 0.21/0.55    sK0 != sK1 | ~r2_hidden(sK1,k2_tarski(sK1,sK0)) | k1_xboole_0 = k2_tarski(sK1,sK0) | k1_xboole_0 = k2_tarski(sK1,sK0)),
% 0.21/0.55    inference(superposition,[],[f106,f291])).
% 0.21/0.55  fof(f291,plain,(
% 0.21/0.55    sK1 = sK3(k2_tarski(sK1,sK0)) | k1_xboole_0 = k2_tarski(sK1,sK0)),
% 0.21/0.55    inference(resolution,[],[f290,f71])).
% 0.21/0.55  fof(f290,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(sK1,k2_tarski(X0,sK0)) | k1_xboole_0 = k2_tarski(X0,sK0) | sK3(k2_tarski(X0,sK0)) = X0) )),
% 0.21/0.55    inference(equality_resolution,[],[f206])).
% 0.21/0.55  fof(f206,plain,(
% 0.21/0.55    ( ! [X8,X9] : (sK0 != X9 | ~r2_hidden(sK1,k2_tarski(X8,X9)) | k1_xboole_0 = k2_tarski(X8,X9) | sK3(k2_tarski(X8,X9)) = X8) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f199])).
% 0.21/0.55  fof(f199,plain,(
% 0.21/0.55    ( ! [X8,X9] : (sK0 != X9 | ~r2_hidden(sK1,k2_tarski(X8,X9)) | k1_xboole_0 = k2_tarski(X8,X9) | sK3(k2_tarski(X8,X9)) = X8 | k1_xboole_0 = k2_tarski(X8,X9)) )),
% 0.21/0.55    inference(superposition,[],[f106,f104])).
% 0.21/0.55  fof(f106,plain,(
% 0.21/0.55    ( ! [X0] : (sK0 != sK3(X0) | ~r2_hidden(sK1,X0) | k1_xboole_0 = X0) )),
% 0.21/0.55    inference(superposition,[],[f45,f35])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK3(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f77,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v1_xboole_0(k2_tarski(X0,X1))) )),
% 0.21/0.55    inference(resolution,[],[f69,f59])).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.55    inference(rectify,[],[f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.55    inference(nnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (7200)------------------------------
% 0.21/0.55  % (7200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (7200)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (7200)Memory used [KB]: 1918
% 0.21/0.55  % (7200)Time elapsed: 0.147 s
% 0.21/0.55  % (7200)------------------------------
% 0.21/0.55  % (7200)------------------------------
% 0.21/0.55  % (7210)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (7194)Success in time 0.183 s
%------------------------------------------------------------------------------
