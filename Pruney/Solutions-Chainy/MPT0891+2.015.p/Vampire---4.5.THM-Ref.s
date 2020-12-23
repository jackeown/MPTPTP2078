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
% DateTime   : Thu Dec  3 12:59:08 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 290 expanded)
%              Number of leaves         :   14 (  87 expanded)
%              Depth                    :   29
%              Number of atoms          :  387 (1762 expanded)
%              Number of equality atoms :  230 (1053 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f670,plain,(
    $false ),
    inference(resolution,[],[f660,f61])).

fof(f61,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

% (13475)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).

fof(f23,plain,(
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

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f660,plain,(
    ! [X0] : ~ r2_hidden(sK3,k1_tarski(X0)) ),
    inference(subsumption_resolution,[],[f659,f62])).

fof(f62,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f659,plain,(
    ! [X0] :
      ( sK3 != X0
      | ~ r2_hidden(sK3,k1_tarski(X0)) ) ),
    inference(subsumption_resolution,[],[f658,f130])).

fof(f130,plain,(
    ! [X9] : k1_xboole_0 != k1_tarski(X9) ),
    inference(subsumption_resolution,[],[f128,f61])).

fof(f128,plain,(
    ! [X9] :
      ( k1_xboole_0 != k1_tarski(X9)
      | ~ r2_hidden(X9,k1_tarski(X9)) ) ),
    inference(superposition,[],[f47,f116])).

fof(f116,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,(
    ! [X0] :
      ( k1_xboole_0 = k4_xboole_0(X0,X0)
      | k1_xboole_0 = k4_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f71,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(k4_xboole_0(X0,X1)),X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f64,f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f29])).

% (13486)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
fof(f29,plain,(
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

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(k4_xboole_0(X0,X1)),X0)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f65,f38])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f658,plain,(
    ! [X0] :
      ( sK3 != X0
      | k1_tarski(X0) = k1_xboole_0
      | ~ r2_hidden(sK3,k1_tarski(X0)) ) ),
    inference(duplicate_literal_removal,[],[f655])).

fof(f655,plain,(
    ! [X0] :
      ( sK3 != X0
      | k1_tarski(X0) = k1_xboole_0
      | ~ r2_hidden(sK3,k1_tarski(X0))
      | k1_tarski(X0) = k1_xboole_0 ) ),
    inference(superposition,[],[f639,f69])).

fof(f69,plain,(
    ! [X1] :
      ( sK4(k1_tarski(X1)) = X1
      | k1_tarski(X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f62,f38])).

fof(f639,plain,(
    ! [X0] :
      ( sK3 != sK4(X0)
      | k1_xboole_0 = X0
      | ~ r2_hidden(sK3,X0) ) ),
    inference(resolution,[],[f626,f61])).

fof(f626,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3,k1_tarski(X1))
      | sK3 != sK4(X0)
      | k1_xboole_0 = X0
      | ~ r2_hidden(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f625,f31])).

fof(f31,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
      | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
      | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) )
    & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f17,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( k7_mcart_1(X0,X1,X2,X3) = X3
              | k6_mcart_1(X0,X1,X2,X3) = X3
              | k5_mcart_1(X0,X1,X2,X3) = X3 )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X3] :
          ( ( k7_mcart_1(sK0,sK1,sK2,X3) = X3
            | k6_mcart_1(sK0,sK1,sK2,X3) = X3
            | k5_mcart_1(sK0,sK1,sK2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2)) )
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X3] :
        ( ( k7_mcart_1(sK0,sK1,sK2,X3) = X3
          | k6_mcart_1(sK0,sK1,sK2,X3) = X3
          | k5_mcart_1(sK0,sK1,sK2,X3) = X3 )
        & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2)) )
   => ( ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
        | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
        | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) )
      & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) != X3
                  & k6_mcart_1(X0,X1,X2,X3) != X3
                  & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) != X3
                & k6_mcart_1(X0,X1,X2,X3) != X3
                & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).

fof(f625,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3,X0)
      | sK3 != sK4(X0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = sK0
      | ~ r2_hidden(sK3,k1_tarski(X1)) ) ),
    inference(subsumption_resolution,[],[f624,f32])).

fof(f32,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f624,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3,X0)
      | sK3 != sK4(X0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | ~ r2_hidden(sK3,k1_tarski(X1)) ) ),
    inference(subsumption_resolution,[],[f623,f33])).

fof(f33,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f18])).

fof(f623,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3,X0)
      | sK3 != sK4(X0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | ~ r2_hidden(sK3,k1_tarski(X1)) ) ),
    inference(subsumption_resolution,[],[f621,f34])).

fof(f34,plain,(
    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f621,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3,X0)
      | sK3 != sK4(X0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | ~ r2_hidden(sK3,k1_tarski(X1)) ) ),
    inference(superposition,[],[f136,f613])).

fof(f613,plain,(
    ! [X5] :
      ( sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)
      | ~ r2_hidden(sK3,k1_tarski(X5)) ) ),
    inference(subsumption_resolution,[],[f612,f62])).

fof(f612,plain,(
    ! [X5] :
      ( sK3 != X5
      | ~ r2_hidden(sK3,k1_tarski(X5))
      | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ) ),
    inference(subsumption_resolution,[],[f607,f130])).

fof(f607,plain,(
    ! [X5] :
      ( sK3 != X5
      | ~ r2_hidden(sK3,k1_tarski(X5))
      | k1_xboole_0 = k1_tarski(X5)
      | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ) ),
    inference(superposition,[],[f89,f154])).

fof(f154,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f153,f31])).

fof(f153,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f152,f32])).

fof(f152,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f151,f33])).

fof(f151,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f150,f34])).

fof(f150,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))
    | ~ m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(superposition,[],[f57,f142])).

fof(f142,plain,
    ( sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f141,f31])).

fof(f141,plain,
    ( k1_xboole_0 = sK0
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f140,f32])).

fof(f140,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f139,f33])).

fof(f139,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f138,f34])).

fof(f138,plain,
    ( ~ m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f131,f82])).

fof(f82,plain,(
    ! [X10,X11,X9] : k3_mcart_1(X9,X10,X11) != X11 ),
    inference(superposition,[],[f66,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f66,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != X2 ),
    inference(backward_demodulation,[],[f58,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f58,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f131,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK3)
    | ~ m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(superposition,[],[f57,f35])).

fof(f35,plain,
    ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

% (13486)Refutation not found, incomplete strategy% (13486)------------------------------
% (13486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (13486)Termination reason: Refutation not found, incomplete strategy

% (13486)Memory used [KB]: 6268
% (13486)Time elapsed: 0.147 s
% (13488)Refutation not found, incomplete strategy% (13488)------------------------------
% (13488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (13488)Termination reason: Refutation not found, incomplete strategy

% (13488)Memory used [KB]: 10874
% (13488)Time elapsed: 0.131 s
% (13488)------------------------------
% (13488)------------------------------
% (13486)------------------------------
% (13486)------------------------------
fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(X1,X2,X3) != X0
      | ~ r2_hidden(X2,k1_tarski(X0))
      | k1_tarski(X0) = k1_xboole_0 ) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(X1,X2,X3) != X0
      | ~ r2_hidden(X2,k1_tarski(X0))
      | k1_tarski(X0) = k1_xboole_0
      | k1_tarski(X0) = k1_xboole_0 ) ),
    inference(superposition,[],[f40,f69])).

fof(f40,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK4(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f136,plain,(
    ! [X21,X19,X17,X20,X18] :
      ( ~ r2_hidden(k5_mcart_1(X17,X18,X19,X20),X21)
      | sK4(X21) != X20
      | k1_xboole_0 = X21
      | ~ m1_subset_1(X20,k3_zfmisc_1(X17,X18,X19))
      | k1_xboole_0 = X19
      | k1_xboole_0 = X18
      | k1_xboole_0 = X17 ) ),
    inference(superposition,[],[f39,f57])).

fof(f39,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK4(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:50:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (13464)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (13471)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.20/0.52  % (13469)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.20/0.52  % (13470)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.20/0.52  % (13480)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.33/0.53  % (13478)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.33/0.53  % (13478)Refutation not found, incomplete strategy% (13478)------------------------------
% 1.33/0.53  % (13478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  % (13478)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.53  
% 1.33/0.53  % (13478)Memory used [KB]: 1791
% 1.33/0.53  % (13478)Time elapsed: 0.121 s
% 1.33/0.53  % (13478)------------------------------
% 1.33/0.53  % (13478)------------------------------
% 1.33/0.54  % (13479)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.33/0.54  % (13461)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.33/0.54  % (13474)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.33/0.54  % (13461)Refutation not found, incomplete strategy% (13461)------------------------------
% 1.33/0.54  % (13461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (13461)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (13461)Memory used [KB]: 1663
% 1.33/0.54  % (13461)Time elapsed: 0.126 s
% 1.33/0.54  % (13461)------------------------------
% 1.33/0.54  % (13461)------------------------------
% 1.33/0.54  % (13488)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.33/0.54  % (13462)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.33/0.54  % (13463)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.33/0.54  % (13472)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.33/0.54  % (13470)Refutation not found, incomplete strategy% (13470)------------------------------
% 1.33/0.54  % (13470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (13481)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.33/0.55  % (13487)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.33/0.55  % (13483)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.33/0.55  % (13472)Refutation not found, incomplete strategy% (13472)------------------------------
% 1.33/0.55  % (13472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (13472)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.55  
% 1.33/0.55  % (13472)Memory used [KB]: 10618
% 1.33/0.55  % (13472)Time elapsed: 0.118 s
% 1.33/0.55  % (13472)------------------------------
% 1.33/0.55  % (13472)------------------------------
% 1.33/0.55  % (13473)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.33/0.55  % (13470)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.55  
% 1.33/0.55  % (13470)Memory used [KB]: 10874
% 1.33/0.55  % (13470)Time elapsed: 0.113 s
% 1.33/0.55  % (13470)------------------------------
% 1.33/0.55  % (13470)------------------------------
% 1.33/0.55  % (13460)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.33/0.55  % (13466)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.33/0.55  % (13482)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.33/0.55  % (13489)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.33/0.55  % (13489)Refutation not found, incomplete strategy% (13489)------------------------------
% 1.33/0.55  % (13489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (13489)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.55  
% 1.33/0.55  % (13489)Memory used [KB]: 1663
% 1.33/0.55  % (13489)Time elapsed: 0.003 s
% 1.33/0.55  % (13489)------------------------------
% 1.33/0.55  % (13489)------------------------------
% 1.33/0.55  % (13484)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.33/0.56  % (13465)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.33/0.56  % (13474)Refutation not found, incomplete strategy% (13474)------------------------------
% 1.33/0.56  % (13474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.56  % (13474)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.56  
% 1.33/0.56  % (13474)Memory used [KB]: 1791
% 1.33/0.56  % (13474)Time elapsed: 0.153 s
% 1.33/0.56  % (13474)------------------------------
% 1.33/0.56  % (13474)------------------------------
% 1.33/0.56  % (13484)Refutation not found, incomplete strategy% (13484)------------------------------
% 1.33/0.56  % (13484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.56  % (13484)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.56  
% 1.33/0.56  % (13484)Memory used [KB]: 10746
% 1.33/0.56  % (13484)Time elapsed: 0.151 s
% 1.33/0.56  % (13484)------------------------------
% 1.33/0.56  % (13484)------------------------------
% 1.33/0.56  % (13487)Refutation not found, incomplete strategy% (13487)------------------------------
% 1.33/0.56  % (13487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.56  % (13487)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.56  
% 1.33/0.56  % (13487)Memory used [KB]: 6268
% 1.33/0.56  % (13487)Time elapsed: 0.129 s
% 1.33/0.56  % (13487)------------------------------
% 1.33/0.56  % (13487)------------------------------
% 1.33/0.56  % (13468)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.33/0.56  % (13477)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.33/0.56  % (13469)Refutation found. Thanks to Tanya!
% 1.33/0.56  % SZS status Theorem for theBenchmark
% 1.33/0.56  % SZS output start Proof for theBenchmark
% 1.33/0.56  fof(f670,plain,(
% 1.33/0.56    $false),
% 1.33/0.56    inference(resolution,[],[f660,f61])).
% 1.33/0.56  fof(f61,plain,(
% 1.33/0.56    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 1.33/0.56    inference(equality_resolution,[],[f60])).
% 1.33/0.56  fof(f60,plain,(
% 1.33/0.56    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 1.33/0.56    inference(equality_resolution,[],[f44])).
% 1.33/0.56  fof(f44,plain,(
% 1.33/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.33/0.56    inference(cnf_transformation,[],[f24])).
% 1.33/0.56  % (13475)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.33/0.56  fof(f24,plain,(
% 1.33/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.33/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).
% 1.33/0.56  fof(f23,plain,(
% 1.33/0.56    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 1.33/0.56    introduced(choice_axiom,[])).
% 1.33/0.56  fof(f22,plain,(
% 1.33/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.33/0.56    inference(rectify,[],[f21])).
% 1.33/0.57  fof(f21,plain,(
% 1.33/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.33/0.57    inference(nnf_transformation,[],[f2])).
% 1.33/0.57  fof(f2,axiom,(
% 1.33/0.57    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.33/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.33/0.57  fof(f660,plain,(
% 1.33/0.57    ( ! [X0] : (~r2_hidden(sK3,k1_tarski(X0))) )),
% 1.33/0.57    inference(subsumption_resolution,[],[f659,f62])).
% 1.33/0.57  fof(f62,plain,(
% 1.33/0.57    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.33/0.57    inference(equality_resolution,[],[f43])).
% 1.33/0.57  fof(f43,plain,(
% 1.33/0.57    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.33/0.57    inference(cnf_transformation,[],[f24])).
% 1.33/0.57  fof(f659,plain,(
% 1.33/0.57    ( ! [X0] : (sK3 != X0 | ~r2_hidden(sK3,k1_tarski(X0))) )),
% 1.33/0.57    inference(subsumption_resolution,[],[f658,f130])).
% 1.33/0.57  fof(f130,plain,(
% 1.33/0.57    ( ! [X9] : (k1_xboole_0 != k1_tarski(X9)) )),
% 1.33/0.57    inference(subsumption_resolution,[],[f128,f61])).
% 1.33/0.57  fof(f128,plain,(
% 1.33/0.57    ( ! [X9] : (k1_xboole_0 != k1_tarski(X9) | ~r2_hidden(X9,k1_tarski(X9))) )),
% 1.33/0.57    inference(superposition,[],[f47,f116])).
% 1.33/0.57  fof(f116,plain,(
% 1.33/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.33/0.57    inference(duplicate_literal_removal,[],[f110])).
% 1.33/0.57  fof(f110,plain,(
% 1.33/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0) | k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.33/0.57    inference(resolution,[],[f71,f70])).
% 1.33/0.57  fof(f70,plain,(
% 1.33/0.57    ( ! [X0,X1] : (~r2_hidden(sK4(k4_xboole_0(X0,X1)),X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.33/0.57    inference(resolution,[],[f64,f38])).
% 1.33/0.57  fof(f38,plain,(
% 1.33/0.57    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.33/0.57    inference(cnf_transformation,[],[f20])).
% 1.33/0.57  fof(f20,plain,(
% 1.33/0.57    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)) | k1_xboole_0 = X0)),
% 1.33/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f19])).
% 1.33/0.57  fof(f19,plain,(
% 1.33/0.57    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)))),
% 1.33/0.57    introduced(choice_axiom,[])).
% 1.33/0.57  fof(f14,plain,(
% 1.33/0.57    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.33/0.57    inference(ennf_transformation,[],[f7])).
% 1.33/0.57  fof(f7,axiom,(
% 1.33/0.57    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.33/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).
% 1.33/0.57  fof(f64,plain,(
% 1.33/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.33/0.57    inference(equality_resolution,[],[f52])).
% 1.33/0.57  fof(f52,plain,(
% 1.33/0.57    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.33/0.57    inference(cnf_transformation,[],[f30])).
% 1.33/0.57  fof(f30,plain,(
% 1.33/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.33/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f29])).
% 1.33/0.57  % (13486)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.33/0.57  fof(f29,plain,(
% 1.33/0.57    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.33/0.57    introduced(choice_axiom,[])).
% 1.33/0.57  fof(f28,plain,(
% 1.33/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.33/0.57    inference(rectify,[],[f27])).
% 1.33/0.57  fof(f27,plain,(
% 1.33/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.33/0.57    inference(flattening,[],[f26])).
% 1.33/0.57  fof(f26,plain,(
% 1.33/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.33/0.57    inference(nnf_transformation,[],[f1])).
% 1.33/0.57  fof(f1,axiom,(
% 1.33/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.33/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.33/0.57  fof(f71,plain,(
% 1.33/0.57    ( ! [X0,X1] : (r2_hidden(sK4(k4_xboole_0(X0,X1)),X0) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.33/0.57    inference(resolution,[],[f65,f38])).
% 1.33/0.57  fof(f65,plain,(
% 1.33/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 1.33/0.57    inference(equality_resolution,[],[f51])).
% 1.33/0.57  fof(f51,plain,(
% 1.33/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.33/0.57    inference(cnf_transformation,[],[f30])).
% 1.33/0.57  fof(f47,plain,(
% 1.33/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 1.33/0.57    inference(cnf_transformation,[],[f25])).
% 1.33/0.57  fof(f25,plain,(
% 1.33/0.57    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.33/0.57    inference(nnf_transformation,[],[f3])).
% 1.33/0.57  fof(f3,axiom,(
% 1.33/0.57    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.33/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.33/0.57  fof(f658,plain,(
% 1.33/0.57    ( ! [X0] : (sK3 != X0 | k1_tarski(X0) = k1_xboole_0 | ~r2_hidden(sK3,k1_tarski(X0))) )),
% 1.33/0.57    inference(duplicate_literal_removal,[],[f655])).
% 1.33/0.57  fof(f655,plain,(
% 1.33/0.57    ( ! [X0] : (sK3 != X0 | k1_tarski(X0) = k1_xboole_0 | ~r2_hidden(sK3,k1_tarski(X0)) | k1_tarski(X0) = k1_xboole_0) )),
% 1.33/0.57    inference(superposition,[],[f639,f69])).
% 1.33/0.57  fof(f69,plain,(
% 1.33/0.57    ( ! [X1] : (sK4(k1_tarski(X1)) = X1 | k1_tarski(X1) = k1_xboole_0) )),
% 1.33/0.57    inference(resolution,[],[f62,f38])).
% 1.33/0.57  fof(f639,plain,(
% 1.33/0.57    ( ! [X0] : (sK3 != sK4(X0) | k1_xboole_0 = X0 | ~r2_hidden(sK3,X0)) )),
% 1.33/0.57    inference(resolution,[],[f626,f61])).
% 1.33/0.57  fof(f626,plain,(
% 1.33/0.57    ( ! [X0,X1] : (~r2_hidden(sK3,k1_tarski(X1)) | sK3 != sK4(X0) | k1_xboole_0 = X0 | ~r2_hidden(sK3,X0)) )),
% 1.33/0.57    inference(subsumption_resolution,[],[f625,f31])).
% 1.33/0.57  fof(f31,plain,(
% 1.33/0.57    k1_xboole_0 != sK0),
% 1.33/0.57    inference(cnf_transformation,[],[f18])).
% 1.33/0.57  fof(f18,plain,(
% 1.33/0.57    ((sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)) & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 1.33/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f17,f16])).
% 1.33/0.57  fof(f16,plain,(
% 1.33/0.57    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK0,sK1,sK2,X3) = X3 | k6_mcart_1(sK0,sK1,sK2,X3) = X3 | k5_mcart_1(sK0,sK1,sK2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2))) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 1.33/0.57    introduced(choice_axiom,[])).
% 1.33/0.57  fof(f17,plain,(
% 1.33/0.57    ? [X3] : ((k7_mcart_1(sK0,sK1,sK2,X3) = X3 | k6_mcart_1(sK0,sK1,sK2,X3) = X3 | k5_mcart_1(sK0,sK1,sK2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2))) => ((sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)) & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)))),
% 1.33/0.57    introduced(choice_axiom,[])).
% 1.33/0.57  fof(f12,plain,(
% 1.33/0.57    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.33/0.57    inference(ennf_transformation,[],[f11])).
% 1.33/0.57  fof(f11,negated_conjecture,(
% 1.33/0.57    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.33/0.57    inference(negated_conjecture,[],[f10])).
% 1.33/0.57  fof(f10,conjecture,(
% 1.33/0.57    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.33/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).
% 1.33/0.57  fof(f625,plain,(
% 1.33/0.57    ( ! [X0,X1] : (~r2_hidden(sK3,X0) | sK3 != sK4(X0) | k1_xboole_0 = X0 | k1_xboole_0 = sK0 | ~r2_hidden(sK3,k1_tarski(X1))) )),
% 1.33/0.57    inference(subsumption_resolution,[],[f624,f32])).
% 1.33/0.57  fof(f32,plain,(
% 1.33/0.57    k1_xboole_0 != sK1),
% 1.33/0.57    inference(cnf_transformation,[],[f18])).
% 1.33/0.57  fof(f624,plain,(
% 1.33/0.57    ( ! [X0,X1] : (~r2_hidden(sK3,X0) | sK3 != sK4(X0) | k1_xboole_0 = X0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~r2_hidden(sK3,k1_tarski(X1))) )),
% 1.33/0.57    inference(subsumption_resolution,[],[f623,f33])).
% 1.33/0.57  fof(f33,plain,(
% 1.33/0.57    k1_xboole_0 != sK2),
% 1.33/0.57    inference(cnf_transformation,[],[f18])).
% 1.33/0.57  fof(f623,plain,(
% 1.33/0.57    ( ! [X0,X1] : (~r2_hidden(sK3,X0) | sK3 != sK4(X0) | k1_xboole_0 = X0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~r2_hidden(sK3,k1_tarski(X1))) )),
% 1.33/0.57    inference(subsumption_resolution,[],[f621,f34])).
% 1.33/0.57  fof(f34,plain,(
% 1.33/0.57    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.33/0.57    inference(cnf_transformation,[],[f18])).
% 1.33/0.57  fof(f621,plain,(
% 1.33/0.57    ( ! [X0,X1] : (~r2_hidden(sK3,X0) | sK3 != sK4(X0) | k1_xboole_0 = X0 | ~m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~r2_hidden(sK3,k1_tarski(X1))) )),
% 1.33/0.57    inference(superposition,[],[f136,f613])).
% 1.33/0.57  fof(f613,plain,(
% 1.33/0.57    ( ! [X5] : (sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) | ~r2_hidden(sK3,k1_tarski(X5))) )),
% 1.33/0.57    inference(subsumption_resolution,[],[f612,f62])).
% 1.33/0.57  fof(f612,plain,(
% 1.33/0.57    ( ! [X5] : (sK3 != X5 | ~r2_hidden(sK3,k1_tarski(X5)) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)) )),
% 1.33/0.57    inference(subsumption_resolution,[],[f607,f130])).
% 1.33/0.57  fof(f607,plain,(
% 1.33/0.57    ( ! [X5] : (sK3 != X5 | ~r2_hidden(sK3,k1_tarski(X5)) | k1_xboole_0 = k1_tarski(X5) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)) )),
% 1.33/0.57    inference(superposition,[],[f89,f154])).
% 1.33/0.57  fof(f154,plain,(
% 1.33/0.57    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 1.33/0.57    inference(subsumption_resolution,[],[f153,f31])).
% 1.33/0.57  fof(f153,plain,(
% 1.33/0.57    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0 | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 1.33/0.57    inference(subsumption_resolution,[],[f152,f32])).
% 1.33/0.57  fof(f152,plain,(
% 1.33/0.57    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 1.33/0.57    inference(subsumption_resolution,[],[f151,f33])).
% 1.33/0.57  fof(f151,plain,(
% 1.33/0.57    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 1.33/0.57    inference(subsumption_resolution,[],[f150,f34])).
% 1.33/0.57  fof(f150,plain,(
% 1.33/0.57    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) | ~m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 1.33/0.57    inference(superposition,[],[f57,f142])).
% 1.33/0.57  fof(f142,plain,(
% 1.33/0.57    sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 1.33/0.57    inference(subsumption_resolution,[],[f141,f31])).
% 1.33/0.57  fof(f141,plain,(
% 1.33/0.57    k1_xboole_0 = sK0 | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 1.33/0.57    inference(subsumption_resolution,[],[f140,f32])).
% 1.33/0.57  fof(f140,plain,(
% 1.33/0.57    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 1.33/0.57    inference(subsumption_resolution,[],[f139,f33])).
% 1.33/0.57  fof(f139,plain,(
% 1.33/0.57    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 1.33/0.57    inference(subsumption_resolution,[],[f138,f34])).
% 1.33/0.57  fof(f138,plain,(
% 1.33/0.57    ~m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 1.33/0.57    inference(subsumption_resolution,[],[f131,f82])).
% 1.33/0.57  fof(f82,plain,(
% 1.33/0.57    ( ! [X10,X11,X9] : (k3_mcart_1(X9,X10,X11) != X11) )),
% 1.33/0.57    inference(superposition,[],[f66,f50])).
% 1.33/0.57  fof(f50,plain,(
% 1.33/0.57    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.33/0.57    inference(cnf_transformation,[],[f4])).
% 1.33/0.57  fof(f4,axiom,(
% 1.33/0.57    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.33/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.33/0.57  fof(f66,plain,(
% 1.33/0.57    ( ! [X2,X1] : (k4_tarski(X1,X2) != X2) )),
% 1.33/0.57    inference(backward_demodulation,[],[f58,f42])).
% 1.33/0.57  fof(f42,plain,(
% 1.33/0.57    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.33/0.57    inference(cnf_transformation,[],[f9])).
% 1.33/0.57  fof(f9,axiom,(
% 1.33/0.57    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.33/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.33/0.57  fof(f58,plain,(
% 1.33/0.57    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 1.33/0.57    inference(equality_resolution,[],[f37])).
% 1.33/0.57  fof(f37,plain,(
% 1.33/0.57    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 1.33/0.57    inference(cnf_transformation,[],[f13])).
% 1.33/0.57  fof(f13,plain,(
% 1.33/0.57    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 1.33/0.57    inference(ennf_transformation,[],[f6])).
% 1.33/0.57  fof(f6,axiom,(
% 1.33/0.57    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.33/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 1.33/0.57  fof(f131,plain,(
% 1.33/0.57    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK3) | ~m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 1.33/0.57    inference(superposition,[],[f57,f35])).
% 1.33/0.57  fof(f35,plain,(
% 1.33/0.57    sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 1.33/0.57    inference(cnf_transformation,[],[f18])).
% 1.33/0.57  % (13486)Refutation not found, incomplete strategy% (13486)------------------------------
% 1.33/0.57  % (13486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.57  % (13486)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.57  
% 1.33/0.57  % (13486)Memory used [KB]: 6268
% 1.33/0.57  % (13486)Time elapsed: 0.147 s
% 1.33/0.57  % (13488)Refutation not found, incomplete strategy% (13488)------------------------------
% 1.33/0.57  % (13488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.57  % (13488)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.57  
% 1.33/0.57  % (13488)Memory used [KB]: 10874
% 1.33/0.57  % (13488)Time elapsed: 0.131 s
% 1.33/0.57  % (13488)------------------------------
% 1.33/0.57  % (13488)------------------------------
% 1.33/0.57  % (13486)------------------------------
% 1.33/0.57  % (13486)------------------------------
% 1.33/0.57  fof(f57,plain,(
% 1.33/0.57    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.33/0.57    inference(cnf_transformation,[],[f15])).
% 1.33/0.57  fof(f15,plain,(
% 1.33/0.57    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.33/0.57    inference(ennf_transformation,[],[f8])).
% 1.33/0.57  fof(f8,axiom,(
% 1.33/0.57    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.33/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).
% 1.33/0.57  fof(f89,plain,(
% 1.33/0.57    ( ! [X2,X0,X3,X1] : (k3_mcart_1(X1,X2,X3) != X0 | ~r2_hidden(X2,k1_tarski(X0)) | k1_tarski(X0) = k1_xboole_0) )),
% 1.33/0.57    inference(duplicate_literal_removal,[],[f88])).
% 1.33/0.57  fof(f88,plain,(
% 1.33/0.57    ( ! [X2,X0,X3,X1] : (k3_mcart_1(X1,X2,X3) != X0 | ~r2_hidden(X2,k1_tarski(X0)) | k1_tarski(X0) = k1_xboole_0 | k1_tarski(X0) = k1_xboole_0) )),
% 1.33/0.57    inference(superposition,[],[f40,f69])).
% 1.33/0.57  fof(f40,plain,(
% 1.33/0.57    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 1.33/0.57    inference(cnf_transformation,[],[f20])).
% 1.33/0.57  fof(f136,plain,(
% 1.33/0.57    ( ! [X21,X19,X17,X20,X18] : (~r2_hidden(k5_mcart_1(X17,X18,X19,X20),X21) | sK4(X21) != X20 | k1_xboole_0 = X21 | ~m1_subset_1(X20,k3_zfmisc_1(X17,X18,X19)) | k1_xboole_0 = X19 | k1_xboole_0 = X18 | k1_xboole_0 = X17) )),
% 1.33/0.57    inference(superposition,[],[f39,f57])).
% 1.33/0.57  fof(f39,plain,(
% 1.33/0.57    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 1.33/0.57    inference(cnf_transformation,[],[f20])).
% 1.33/0.57  % SZS output end Proof for theBenchmark
% 1.33/0.57  % (13469)------------------------------
% 1.33/0.57  % (13469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.57  % (13469)Termination reason: Refutation
% 1.33/0.57  
% 1.33/0.57  % (13469)Memory used [KB]: 2174
% 1.33/0.57  % (13469)Time elapsed: 0.155 s
% 1.33/0.57  % (13469)------------------------------
% 1.33/0.57  % (13469)------------------------------
% 1.33/0.57  % (13459)Success in time 0.199 s
%------------------------------------------------------------------------------
