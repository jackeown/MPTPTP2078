%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:15 EST 2020

% Result     : Theorem 6.55s
% Output     : Refutation 6.55s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 187 expanded)
%              Number of leaves         :   12 (  48 expanded)
%              Depth                    :   20
%              Number of atoms          :  225 ( 726 expanded)
%              Number of equality atoms :   69 ( 190 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4951,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4946,f41])).

fof(f41,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k1_tarski(sK3) != k3_xboole_0(sK0,sK2)
    & r2_hidden(sK3,sK0)
    & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_tarski(X3) != k3_xboole_0(X0,X2)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k1_tarski(sK3) != k3_xboole_0(sK0,sK2)
      & r2_hidden(sK3,sK0)
      & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(f4946,plain,(
    ~ r2_hidden(sK3,sK0) ),
    inference(backward_demodulation,[],[f4930,f4939])).

fof(f4939,plain,(
    sK3 = sK4(k1_tarski(sK3),sK0) ),
    inference(resolution,[],[f4929,f72])).

fof(f72,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).

fof(f32,plain,(
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

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f4929,plain,(
    r2_hidden(sK4(k1_tarski(sK3),sK0),k1_tarski(sK3)) ),
    inference(resolution,[],[f4927,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f4927,plain,(
    ~ r1_tarski(k1_tarski(sK3),sK0) ),
    inference(subsumption_resolution,[],[f4901,f42])).

fof(f42,plain,(
    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f4901,plain,
    ( k1_tarski(sK3) = k3_xboole_0(sK0,sK2)
    | ~ r1_tarski(k1_tarski(sK3),sK0) ),
    inference(superposition,[],[f4845,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f4845,plain,(
    k3_xboole_0(sK0,sK2) = k3_xboole_0(k1_tarski(sK3),sK0) ),
    inference(superposition,[],[f4731,f393])).

fof(f393,plain,(
    ! [X1] : k3_xboole_0(k1_tarski(sK3),X1) = k3_xboole_0(sK1,k3_xboole_0(X1,sK2)) ),
    inference(superposition,[],[f93,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f93,plain,(
    ! [X0] : k3_xboole_0(sK1,k3_xboole_0(sK2,X0)) = k3_xboole_0(k1_tarski(sK3),X0) ),
    inference(superposition,[],[f60,f40])).

fof(f40,plain,(
    k1_tarski(sK3) = k3_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f4731,plain,(
    ! [X3] : k3_xboole_0(sK0,X3) = k3_xboole_0(sK1,k3_xboole_0(sK0,X3)) ),
    inference(superposition,[],[f4401,f45])).

fof(f4401,plain,(
    ! [X4] : k3_xboole_0(sK0,X4) = k3_xboole_0(k3_xboole_0(sK0,X4),sK1) ),
    inference(resolution,[],[f4393,f48])).

fof(f4393,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK0,X0),sK1) ),
    inference(superposition,[],[f4388,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f4388,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK0,X0),sK1) ),
    inference(duplicate_literal_removal,[],[f4378])).

fof(f4378,plain,(
    ! [X0] :
      ( r1_tarski(k4_xboole_0(sK0,X0),sK1)
      | r1_tarski(k4_xboole_0(sK0,X0),sK1) ) ),
    inference(resolution,[],[f462,f53])).

fof(f462,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,sK1),k4_xboole_0(sK0,X1))
      | r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f100,f75])).

fof(f75,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
              & r2_hidden(sK6(X0,X1,X2),X0) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(sK6(X0,X1,X2),X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f100,plain,(
    ! [X8] :
      ( ~ r2_hidden(sK4(X8,sK1),sK0)
      | r1_tarski(X8,sK1) ) ),
    inference(resolution,[],[f76,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f39,f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f39,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f4930,plain,(
    ~ r2_hidden(sK4(k1_tarski(sK3),sK0),sK0) ),
    inference(resolution,[],[f4927,f54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:52:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (15391)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.48  % (15407)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.49  % (15380)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.49  % (15387)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (15385)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (15386)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (15382)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (15405)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (15381)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (15383)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (15397)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (15400)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (15392)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (15378)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (15398)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (15390)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (15389)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (15401)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (15379)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (15402)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (15406)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (15399)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (15384)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (15393)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (15394)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (15404)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (15388)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (15396)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.57/0.56  % (15395)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.57/0.57  % (15395)Refutation not found, incomplete strategy% (15395)------------------------------
% 1.57/0.57  % (15395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (15395)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.57  
% 1.57/0.57  % (15395)Memory used [KB]: 10618
% 1.57/0.57  % (15395)Time elapsed: 0.163 s
% 1.57/0.57  % (15395)------------------------------
% 1.57/0.57  % (15395)------------------------------
% 1.57/0.57  % (15403)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 2.59/0.71  % (15467)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.02/0.81  % (15383)Time limit reached!
% 3.02/0.81  % (15383)------------------------------
% 3.02/0.81  % (15383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.02/0.81  % (15383)Termination reason: Time limit
% 3.02/0.81  % (15383)Termination phase: Saturation
% 3.02/0.81  
% 3.02/0.81  % (15383)Memory used [KB]: 8571
% 3.02/0.81  % (15383)Time elapsed: 0.400 s
% 3.02/0.81  % (15383)------------------------------
% 3.02/0.81  % (15383)------------------------------
% 4.03/0.91  % (15378)Time limit reached!
% 4.03/0.91  % (15378)------------------------------
% 4.03/0.91  % (15378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/0.91  % (15378)Termination reason: Time limit
% 4.03/0.91  % (15378)Termination phase: Saturation
% 4.03/0.91  
% 4.03/0.91  % (15378)Memory used [KB]: 3582
% 4.03/0.91  % (15378)Time elapsed: 0.500 s
% 4.03/0.91  % (15378)------------------------------
% 4.03/0.91  % (15378)------------------------------
% 4.03/0.91  % (15379)Time limit reached!
% 4.03/0.91  % (15379)------------------------------
% 4.03/0.91  % (15379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/0.91  % (15379)Termination reason: Time limit
% 4.03/0.91  % (15379)Termination phase: Saturation
% 4.03/0.91  
% 4.03/0.91  % (15379)Memory used [KB]: 8699
% 4.03/0.91  % (15379)Time elapsed: 0.500 s
% 4.03/0.91  % (15379)------------------------------
% 4.03/0.91  % (15379)------------------------------
% 4.03/0.92  % (15388)Time limit reached!
% 4.03/0.92  % (15388)------------------------------
% 4.03/0.92  % (15388)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/0.92  % (15388)Termination reason: Time limit
% 4.03/0.92  
% 4.03/0.92  % (15388)Memory used [KB]: 13816
% 4.03/0.92  % (15388)Time elapsed: 0.511 s
% 4.03/0.92  % (15388)------------------------------
% 4.03/0.92  % (15388)------------------------------
% 4.03/0.92  % (15390)Time limit reached!
% 4.03/0.92  % (15390)------------------------------
% 4.03/0.92  % (15390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/0.92  % (15390)Termination reason: Time limit
% 4.03/0.92  % (15390)Termination phase: Saturation
% 4.03/0.92  
% 4.03/0.92  % (15390)Memory used [KB]: 10106
% 4.03/0.92  % (15390)Time elapsed: 0.500 s
% 4.03/0.92  % (15390)------------------------------
% 4.03/0.92  % (15390)------------------------------
% 4.41/0.95  % (15573)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 4.81/1.02  % (15406)Time limit reached!
% 4.81/1.02  % (15406)------------------------------
% 4.81/1.02  % (15406)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.81/1.02  % (15406)Termination reason: Time limit
% 4.81/1.02  
% 4.81/1.02  % (15406)Memory used [KB]: 9722
% 4.81/1.02  % (15406)Time elapsed: 0.611 s
% 4.81/1.02  % (15406)------------------------------
% 4.81/1.02  % (15406)------------------------------
% 4.81/1.02  % (15385)Time limit reached!
% 4.81/1.02  % (15385)------------------------------
% 4.81/1.02  % (15385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.81/1.02  % (15385)Termination reason: Time limit
% 4.81/1.02  
% 4.81/1.02  % (15385)Memory used [KB]: 11385
% 4.81/1.02  % (15385)Time elapsed: 0.608 s
% 4.81/1.02  % (15385)------------------------------
% 4.81/1.02  % (15385)------------------------------
% 4.81/1.02  % (15394)Time limit reached!
% 4.81/1.02  % (15394)------------------------------
% 4.81/1.02  % (15394)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.81/1.02  % (15394)Termination reason: Time limit
% 4.81/1.02  % (15394)Termination phase: Saturation
% 4.81/1.02  
% 4.81/1.02  % (15394)Memory used [KB]: 17910
% 4.81/1.02  % (15394)Time elapsed: 0.600 s
% 4.81/1.02  % (15394)------------------------------
% 4.81/1.02  % (15394)------------------------------
% 4.81/1.03  % (15607)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.81/1.04  % (15606)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.81/1.04  % (15598)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.81/1.05  % (15602)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.53/1.14  % (15643)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 5.53/1.15  % (15641)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.53/1.15  % (15642)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.55/1.21  % (15401)Refutation found. Thanks to Tanya!
% 6.55/1.21  % SZS status Theorem for theBenchmark
% 6.55/1.21  % SZS output start Proof for theBenchmark
% 6.55/1.21  fof(f4951,plain,(
% 6.55/1.21    $false),
% 6.55/1.21    inference(subsumption_resolution,[],[f4946,f41])).
% 6.55/1.21  fof(f41,plain,(
% 6.55/1.21    r2_hidden(sK3,sK0)),
% 6.55/1.21    inference(cnf_transformation,[],[f23])).
% 6.55/1.21  fof(f23,plain,(
% 6.55/1.21    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 6.55/1.21    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f22])).
% 6.55/1.21  fof(f22,plain,(
% 6.55/1.21    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k1_tarski(sK3) != k3_xboole_0(sK0,sK2) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 6.55/1.21    introduced(choice_axiom,[])).
% 6.55/1.21  fof(f18,plain,(
% 6.55/1.21    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 6.55/1.21    inference(flattening,[],[f17])).
% 6.55/1.21  fof(f17,plain,(
% 6.55/1.21    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 6.55/1.21    inference(ennf_transformation,[],[f15])).
% 6.55/1.21  fof(f15,negated_conjecture,(
% 6.55/1.21    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 6.55/1.21    inference(negated_conjecture,[],[f14])).
% 6.55/1.21  fof(f14,conjecture,(
% 6.55/1.21    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 6.55/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).
% 6.55/1.21  fof(f4946,plain,(
% 6.55/1.21    ~r2_hidden(sK3,sK0)),
% 6.55/1.21    inference(backward_demodulation,[],[f4930,f4939])).
% 6.55/1.21  fof(f4939,plain,(
% 6.55/1.21    sK3 = sK4(k1_tarski(sK3),sK0)),
% 6.55/1.21    inference(resolution,[],[f4929,f72])).
% 6.55/1.21  fof(f72,plain,(
% 6.55/1.21    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 6.55/1.21    inference(equality_resolution,[],[f55])).
% 6.55/1.21  fof(f55,plain,(
% 6.55/1.21    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 6.55/1.21    inference(cnf_transformation,[],[f33])).
% 6.55/1.21  fof(f33,plain,(
% 6.55/1.21    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 6.55/1.21    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).
% 6.55/1.21  fof(f32,plain,(
% 6.55/1.21    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 6.55/1.21    introduced(choice_axiom,[])).
% 6.55/1.21  fof(f31,plain,(
% 6.55/1.21    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 6.55/1.21    inference(rectify,[],[f30])).
% 6.55/1.21  fof(f30,plain,(
% 6.55/1.21    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 6.55/1.21    inference(nnf_transformation,[],[f9])).
% 6.55/1.21  fof(f9,axiom,(
% 6.55/1.21    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 6.55/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 6.55/1.21  fof(f4929,plain,(
% 6.55/1.21    r2_hidden(sK4(k1_tarski(sK3),sK0),k1_tarski(sK3))),
% 6.55/1.21    inference(resolution,[],[f4927,f53])).
% 6.55/1.21  fof(f53,plain,(
% 6.55/1.21    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 6.55/1.21    inference(cnf_transformation,[],[f29])).
% 6.55/1.21  fof(f29,plain,(
% 6.55/1.21    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.55/1.21    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).
% 6.55/1.21  fof(f28,plain,(
% 6.55/1.21    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 6.55/1.21    introduced(choice_axiom,[])).
% 6.55/1.21  fof(f27,plain,(
% 6.55/1.21    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.55/1.21    inference(rectify,[],[f26])).
% 6.55/1.21  fof(f26,plain,(
% 6.55/1.21    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 6.55/1.21    inference(nnf_transformation,[],[f20])).
% 6.55/1.21  fof(f20,plain,(
% 6.55/1.21    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 6.55/1.21    inference(ennf_transformation,[],[f2])).
% 6.55/1.21  fof(f2,axiom,(
% 6.55/1.21    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 6.55/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 6.55/1.21  fof(f4927,plain,(
% 6.55/1.21    ~r1_tarski(k1_tarski(sK3),sK0)),
% 6.55/1.21    inference(subsumption_resolution,[],[f4901,f42])).
% 6.55/1.21  fof(f42,plain,(
% 6.55/1.21    k1_tarski(sK3) != k3_xboole_0(sK0,sK2)),
% 6.55/1.21    inference(cnf_transformation,[],[f23])).
% 6.55/1.21  fof(f4901,plain,(
% 6.55/1.21    k1_tarski(sK3) = k3_xboole_0(sK0,sK2) | ~r1_tarski(k1_tarski(sK3),sK0)),
% 6.55/1.21    inference(superposition,[],[f4845,f48])).
% 6.55/1.21  fof(f48,plain,(
% 6.55/1.21    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 6.55/1.21    inference(cnf_transformation,[],[f19])).
% 6.55/1.21  fof(f19,plain,(
% 6.55/1.21    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 6.55/1.21    inference(ennf_transformation,[],[f7])).
% 6.55/1.21  fof(f7,axiom,(
% 6.55/1.21    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 6.55/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 6.55/1.21  fof(f4845,plain,(
% 6.55/1.21    k3_xboole_0(sK0,sK2) = k3_xboole_0(k1_tarski(sK3),sK0)),
% 6.55/1.21    inference(superposition,[],[f4731,f393])).
% 6.55/1.21  fof(f393,plain,(
% 6.55/1.21    ( ! [X1] : (k3_xboole_0(k1_tarski(sK3),X1) = k3_xboole_0(sK1,k3_xboole_0(X1,sK2))) )),
% 6.55/1.21    inference(superposition,[],[f93,f45])).
% 6.55/1.21  fof(f45,plain,(
% 6.55/1.21    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 6.55/1.21    inference(cnf_transformation,[],[f1])).
% 6.55/1.21  fof(f1,axiom,(
% 6.55/1.21    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 6.55/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 6.55/1.21  fof(f93,plain,(
% 6.55/1.21    ( ! [X0] : (k3_xboole_0(sK1,k3_xboole_0(sK2,X0)) = k3_xboole_0(k1_tarski(sK3),X0)) )),
% 6.55/1.21    inference(superposition,[],[f60,f40])).
% 6.55/1.21  fof(f40,plain,(
% 6.55/1.21    k1_tarski(sK3) = k3_xboole_0(sK1,sK2)),
% 6.55/1.21    inference(cnf_transformation,[],[f23])).
% 6.55/1.21  fof(f60,plain,(
% 6.55/1.21    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 6.55/1.21    inference(cnf_transformation,[],[f6])).
% 6.55/1.21  fof(f6,axiom,(
% 6.55/1.21    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 6.55/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 6.55/1.21  fof(f4731,plain,(
% 6.55/1.21    ( ! [X3] : (k3_xboole_0(sK0,X3) = k3_xboole_0(sK1,k3_xboole_0(sK0,X3))) )),
% 6.55/1.21    inference(superposition,[],[f4401,f45])).
% 6.55/1.21  fof(f4401,plain,(
% 6.55/1.21    ( ! [X4] : (k3_xboole_0(sK0,X4) = k3_xboole_0(k3_xboole_0(sK0,X4),sK1)) )),
% 6.55/1.21    inference(resolution,[],[f4393,f48])).
% 6.55/1.21  fof(f4393,plain,(
% 6.55/1.21    ( ! [X0] : (r1_tarski(k3_xboole_0(sK0,X0),sK1)) )),
% 6.55/1.21    inference(superposition,[],[f4388,f47])).
% 6.55/1.21  fof(f47,plain,(
% 6.55/1.21    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 6.55/1.21    inference(cnf_transformation,[],[f8])).
% 6.55/1.21  fof(f8,axiom,(
% 6.55/1.21    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 6.55/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 6.55/1.21  fof(f4388,plain,(
% 6.55/1.21    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,X0),sK1)) )),
% 6.55/1.21    inference(duplicate_literal_removal,[],[f4378])).
% 6.55/1.21  fof(f4378,plain,(
% 6.55/1.21    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,X0),sK1) | r1_tarski(k4_xboole_0(sK0,X0),sK1)) )),
% 6.55/1.21    inference(resolution,[],[f462,f53])).
% 6.55/1.21  fof(f462,plain,(
% 6.55/1.21    ( ! [X0,X1] : (~r2_hidden(sK4(X0,sK1),k4_xboole_0(sK0,X1)) | r1_tarski(X0,sK1)) )),
% 6.55/1.21    inference(resolution,[],[f100,f75])).
% 6.55/1.21  fof(f75,plain,(
% 6.55/1.21    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 6.55/1.21    inference(equality_resolution,[],[f62])).
% 6.55/1.21  fof(f62,plain,(
% 6.55/1.21    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 6.55/1.21    inference(cnf_transformation,[],[f38])).
% 6.55/1.21  fof(f38,plain,(
% 6.55/1.21    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 6.55/1.21    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).
% 6.55/1.21  fof(f37,plain,(
% 6.55/1.21    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 6.55/1.21    introduced(choice_axiom,[])).
% 6.55/1.21  fof(f36,plain,(
% 6.55/1.21    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 6.55/1.21    inference(rectify,[],[f35])).
% 6.55/1.21  fof(f35,plain,(
% 6.55/1.21    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 6.55/1.21    inference(flattening,[],[f34])).
% 6.55/1.21  fof(f34,plain,(
% 6.55/1.21    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 6.55/1.21    inference(nnf_transformation,[],[f3])).
% 6.55/1.21  fof(f3,axiom,(
% 6.55/1.21    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 6.55/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 6.55/1.21  fof(f100,plain,(
% 6.55/1.21    ( ! [X8] : (~r2_hidden(sK4(X8,sK1),sK0) | r1_tarski(X8,sK1)) )),
% 6.55/1.21    inference(resolution,[],[f76,f54])).
% 6.55/1.21  fof(f54,plain,(
% 6.55/1.21    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK4(X0,X1),X1)) )),
% 6.55/1.21    inference(cnf_transformation,[],[f29])).
% 6.55/1.21  fof(f76,plain,(
% 6.55/1.21    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 6.55/1.21    inference(resolution,[],[f39,f52])).
% 6.55/1.21  fof(f52,plain,(
% 6.55/1.21    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 6.55/1.21    inference(cnf_transformation,[],[f29])).
% 6.55/1.21  fof(f39,plain,(
% 6.55/1.21    r1_tarski(sK0,sK1)),
% 6.55/1.21    inference(cnf_transformation,[],[f23])).
% 6.55/1.21  fof(f4930,plain,(
% 6.55/1.21    ~r2_hidden(sK4(k1_tarski(sK3),sK0),sK0)),
% 6.55/1.21    inference(resolution,[],[f4927,f54])).
% 6.55/1.21  % SZS output end Proof for theBenchmark
% 6.55/1.21  % (15401)------------------------------
% 6.55/1.21  % (15401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.55/1.21  % (15401)Termination reason: Refutation
% 6.55/1.21  
% 6.55/1.21  % (15401)Memory used [KB]: 4861
% 6.55/1.21  % (15401)Time elapsed: 0.781 s
% 6.55/1.21  % (15401)------------------------------
% 6.55/1.21  % (15401)------------------------------
% 6.55/1.22  % (15377)Success in time 0.849 s
%------------------------------------------------------------------------------
