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
% DateTime   : Thu Dec  3 12:41:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 281 expanded)
%              Number of leaves         :   11 (  84 expanded)
%              Depth                    :   25
%              Number of atoms          :  234 (1373 expanded)
%              Number of equality atoms :   37 ( 238 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f187,plain,(
    $false ),
    inference(subsumption_resolution,[],[f182,f45])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f182,plain,(
    ~ r1_tarski(sK0,sK0) ),
    inference(resolution,[],[f168,f45])).

fof(f168,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,X0)
      | ~ r1_tarski(X0,sK0) ) ),
    inference(resolution,[],[f167,f46])).

fof(f46,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

% (10599)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f167,plain,(
    ! [X9] :
      ( ~ r2_hidden(X9,k1_zfmisc_1(sK0))
      | ~ r1_tarski(sK0,X9) ) ),
    inference(subsumption_resolution,[],[f166,f143])).

fof(f143,plain,(
    r2_hidden(sK3(k1_zfmisc_1(sK0),sK0),sK0) ),
    inference(subsumption_resolution,[],[f142,f27])).

fof(f27,plain,(
    sK0 != k3_tarski(k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    sK0 != k3_tarski(k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f9])).

fof(f9,plain,
    ( ? [X0] : k3_tarski(k1_zfmisc_1(X0)) != X0
   => sK0 != k3_tarski(k1_zfmisc_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] : k3_tarski(k1_zfmisc_1(X0)) != X0 ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f142,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK0),sK0)
    | sK0 = k3_tarski(k1_zfmisc_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK0),sK0)
    | sK0 = k3_tarski(k1_zfmisc_1(sK0))
    | r2_hidden(sK3(k1_zfmisc_1(sK0),sK0),sK0) ),
    inference(resolution,[],[f118,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK3(X0,X1),sK4(X0,X1))
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK3(X0,X1),X3) )
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( ( r2_hidden(sK4(X0,X1),X0)
              & r2_hidden(sK3(X0,X1),sK4(X0,X1)) )
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK5(X0,X5),X0)
                & r2_hidden(X5,sK5(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f22,f25,f24,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK3(X0,X1),X3) )
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK3(X0,X1),X4) )
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK3(X0,X1),X4) )
     => ( r2_hidden(sK4(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK5(X0,X5),X0)
        & r2_hidden(X5,sK5(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f118,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK4(k1_zfmisc_1(sK0),sK0))
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f116,f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f116,plain,(
    r1_tarski(sK4(k1_zfmisc_1(sK0),sK0),sK0) ),
    inference(subsumption_resolution,[],[f111,f45])).

fof(f111,plain,
    ( r1_tarski(sK4(k1_zfmisc_1(sK0),sK0),sK0)
    | ~ r1_tarski(sK0,sK0) ),
    inference(resolution,[],[f98,f45])).

fof(f98,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,X0)
      | r1_tarski(sK4(k1_zfmisc_1(sK0),sK0),sK0)
      | ~ r1_tarski(X0,sK0) ) ),
    inference(resolution,[],[f97,f46])).

fof(f97,plain,(
    ! [X9] :
      ( ~ r2_hidden(X9,k1_zfmisc_1(sK0))
      | ~ r1_tarski(sK0,X9)
      | r1_tarski(sK4(k1_zfmisc_1(sK0),sK0),sK0) ) ),
    inference(subsumption_resolution,[],[f96,f69])).

fof(f69,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK0),sK0)
    | r1_tarski(sK4(k1_zfmisc_1(sK0),sK0),sK0) ),
    inference(resolution,[],[f68,f47])).

fof(f47,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,
    ( r2_hidden(sK4(k1_zfmisc_1(sK0),sK0),k1_zfmisc_1(sK0))
    | r2_hidden(sK3(k1_zfmisc_1(sK0),sK0),sK0) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X1] :
      ( sK0 != X1
      | r2_hidden(sK4(k1_zfmisc_1(sK0),X1),k1_zfmisc_1(sK0))
      | r2_hidden(sK3(k1_zfmisc_1(sK0),X1),X1) ) ),
    inference(superposition,[],[f27,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK4(X0,X1),X0)
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f96,plain,(
    ! [X9] :
      ( r1_tarski(sK4(k1_zfmisc_1(sK0),sK0),sK0)
      | ~ r1_tarski(sK0,X9)
      | ~ r2_hidden(X9,k1_zfmisc_1(sK0))
      | ~ r2_hidden(sK3(k1_zfmisc_1(sK0),sK0),sK0) ) ),
    inference(subsumption_resolution,[],[f90,f27])).

fof(f90,plain,(
    ! [X9] :
      ( r1_tarski(sK4(k1_zfmisc_1(sK0),sK0),sK0)
      | ~ r1_tarski(sK0,X9)
      | sK0 = k3_tarski(k1_zfmisc_1(sK0))
      | ~ r2_hidden(X9,k1_zfmisc_1(sK0))
      | ~ r2_hidden(sK3(k1_zfmisc_1(sK0),sK0),sK0) ) ),
    inference(resolution,[],[f80,f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( k3_tarski(X0) = X1
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(sK3(X0,X1),X3)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f80,plain,(
    ! [X4] :
      ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK0),X4)
      | r1_tarski(sK4(k1_zfmisc_1(sK0),sK0),sK0)
      | ~ r1_tarski(sK0,X4) ) ),
    inference(resolution,[],[f69,f31])).

fof(f166,plain,(
    ! [X9] :
      ( ~ r1_tarski(sK0,X9)
      | ~ r2_hidden(X9,k1_zfmisc_1(sK0))
      | ~ r2_hidden(sK3(k1_zfmisc_1(sK0),sK0),sK0) ) ),
    inference(subsumption_resolution,[],[f158,f27])).

fof(f158,plain,(
    ! [X9] :
      ( ~ r1_tarski(sK0,X9)
      | sK0 = k3_tarski(k1_zfmisc_1(sK0))
      | ~ r2_hidden(X9,k1_zfmisc_1(sK0))
      | ~ r2_hidden(sK3(k1_zfmisc_1(sK0),sK0),sK0) ) ),
    inference(resolution,[],[f148,f43])).

fof(f148,plain,(
    ! [X4] :
      ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK0),X4)
      | ~ r1_tarski(sK0,X4) ) ),
    inference(resolution,[],[f143,f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (10604)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (10597)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (10600)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (10615)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (10615)Refutation not found, incomplete strategy% (10615)------------------------------
% 0.21/0.52  % (10615)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10615)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (10615)Memory used [KB]: 1663
% 0.21/0.52  % (10615)Time elapsed: 0.097 s
% 0.21/0.52  % (10615)------------------------------
% 0.21/0.52  % (10615)------------------------------
% 0.21/0.52  % (10596)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (10605)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (10595)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (10596)Refutation not found, incomplete strategy% (10596)------------------------------
% 0.21/0.52  % (10596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10596)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (10596)Memory used [KB]: 10618
% 0.21/0.52  % (10596)Time elapsed: 0.098 s
% 0.21/0.52  % (10596)------------------------------
% 0.21/0.52  % (10596)------------------------------
% 0.21/0.52  % (10604)Refutation not found, incomplete strategy% (10604)------------------------------
% 0.21/0.52  % (10604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10604)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (10604)Memory used [KB]: 10618
% 0.21/0.52  % (10604)Time elapsed: 0.104 s
% 0.21/0.52  % (10604)------------------------------
% 0.21/0.52  % (10604)------------------------------
% 0.21/0.52  % (10594)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (10617)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (10608)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (10617)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f187,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f182,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(flattening,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f182,plain,(
% 0.21/0.53    ~r1_tarski(sK0,sK0)),
% 0.21/0.53    inference(resolution,[],[f168,f45])).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(sK0,X0) | ~r1_tarski(X0,sK0)) )),
% 0.21/0.53    inference(resolution,[],[f167,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.53    inference(rectify,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f3])).
% 0.21/0.53  % (10599)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.53  fof(f167,plain,(
% 0.21/0.53    ( ! [X9] : (~r2_hidden(X9,k1_zfmisc_1(sK0)) | ~r1_tarski(sK0,X9)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f166,f143])).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    r2_hidden(sK3(k1_zfmisc_1(sK0),sK0),sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f142,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    sK0 != k3_tarski(k1_zfmisc_1(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    sK0 != k3_tarski(k1_zfmisc_1(sK0))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f9])).
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    ? [X0] : k3_tarski(k1_zfmisc_1(X0)) != X0 => sK0 != k3_tarski(k1_zfmisc_1(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f7,plain,(
% 0.21/0.53    ? [X0] : k3_tarski(k1_zfmisc_1(X0)) != X0),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,negated_conjecture,(
% 0.21/0.53    ~! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.21/0.53    inference(negated_conjecture,[],[f5])).
% 0.21/0.53  fof(f5,conjecture,(
% 0.21/0.53    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    r2_hidden(sK3(k1_zfmisc_1(sK0),sK0),sK0) | sK0 = k3_tarski(k1_zfmisc_1(sK0))),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f134])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    r2_hidden(sK3(k1_zfmisc_1(sK0),sK0),sK0) | sK0 = k3_tarski(k1_zfmisc_1(sK0)) | r2_hidden(sK3(k1_zfmisc_1(sK0),sK0),sK0)),
% 0.21/0.53    inference(resolution,[],[f118,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK3(X0,X1),sK4(X0,X1)) | r2_hidden(sK3(X0,X1),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK3(X0,X1),X3)) | ~r2_hidden(sK3(X0,X1),X1)) & ((r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK3(X0,X1),sK4(X0,X1))) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK5(X0,X5),X0) & r2_hidden(X5,sK5(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f22,f25,f24,f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK3(X0,X1),X3)) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK3(X0,X1),X4)) | r2_hidden(sK3(X0,X1),X1))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK3(X0,X1),X4)) => (r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK3(X0,X1),sK4(X0,X1))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK5(X0,X5),X0) & r2_hidden(X5,sK5(X0,X5))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 0.21/0.53    inference(rectify,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,sK4(k1_zfmisc_1(sK0),sK0)) | r2_hidden(X0,sK0)) )),
% 0.21/0.53    inference(resolution,[],[f116,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(rectify,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    r1_tarski(sK4(k1_zfmisc_1(sK0),sK0),sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f111,f45])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    r1_tarski(sK4(k1_zfmisc_1(sK0),sK0),sK0) | ~r1_tarski(sK0,sK0)),
% 0.21/0.53    inference(resolution,[],[f98,f45])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(sK0,X0) | r1_tarski(sK4(k1_zfmisc_1(sK0),sK0),sK0) | ~r1_tarski(X0,sK0)) )),
% 0.21/0.53    inference(resolution,[],[f97,f46])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ( ! [X9] : (~r2_hidden(X9,k1_zfmisc_1(sK0)) | ~r1_tarski(sK0,X9) | r1_tarski(sK4(k1_zfmisc_1(sK0),sK0),sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f96,f69])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    r2_hidden(sK3(k1_zfmisc_1(sK0),sK0),sK0) | r1_tarski(sK4(k1_zfmisc_1(sK0),sK0),sK0)),
% 0.21/0.53    inference(resolution,[],[f68,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(equality_resolution,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    r2_hidden(sK4(k1_zfmisc_1(sK0),sK0),k1_zfmisc_1(sK0)) | r2_hidden(sK3(k1_zfmisc_1(sK0),sK0),sK0)),
% 0.21/0.53    inference(equality_resolution,[],[f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X1] : (sK0 != X1 | r2_hidden(sK4(k1_zfmisc_1(sK0),X1),k1_zfmisc_1(sK0)) | r2_hidden(sK3(k1_zfmisc_1(sK0),X1),X1)) )),
% 0.21/0.53    inference(superposition,[],[f27,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK4(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    ( ! [X9] : (r1_tarski(sK4(k1_zfmisc_1(sK0),sK0),sK0) | ~r1_tarski(sK0,X9) | ~r2_hidden(X9,k1_zfmisc_1(sK0)) | ~r2_hidden(sK3(k1_zfmisc_1(sK0),sK0),sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f90,f27])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    ( ! [X9] : (r1_tarski(sK4(k1_zfmisc_1(sK0),sK0),sK0) | ~r1_tarski(sK0,X9) | sK0 = k3_tarski(k1_zfmisc_1(sK0)) | ~r2_hidden(X9,k1_zfmisc_1(sK0)) | ~r2_hidden(sK3(k1_zfmisc_1(sK0),sK0),sK0)) )),
% 0.21/0.53    inference(resolution,[],[f80,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (k3_tarski(X0) = X1 | ~r2_hidden(X3,X0) | ~r2_hidden(sK3(X0,X1),X3) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X4] : (r2_hidden(sK3(k1_zfmisc_1(sK0),sK0),X4) | r1_tarski(sK4(k1_zfmisc_1(sK0),sK0),sK0) | ~r1_tarski(sK0,X4)) )),
% 0.21/0.53    inference(resolution,[],[f69,f31])).
% 0.21/0.53  fof(f166,plain,(
% 0.21/0.53    ( ! [X9] : (~r1_tarski(sK0,X9) | ~r2_hidden(X9,k1_zfmisc_1(sK0)) | ~r2_hidden(sK3(k1_zfmisc_1(sK0),sK0),sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f158,f27])).
% 0.21/0.53  fof(f158,plain,(
% 0.21/0.53    ( ! [X9] : (~r1_tarski(sK0,X9) | sK0 = k3_tarski(k1_zfmisc_1(sK0)) | ~r2_hidden(X9,k1_zfmisc_1(sK0)) | ~r2_hidden(sK3(k1_zfmisc_1(sK0),sK0),sK0)) )),
% 0.21/0.53    inference(resolution,[],[f148,f43])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    ( ! [X4] : (r2_hidden(sK3(k1_zfmisc_1(sK0),sK0),X4) | ~r1_tarski(sK0,X4)) )),
% 0.21/0.53    inference(resolution,[],[f143,f31])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (10617)------------------------------
% 0.21/0.53  % (10617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (10617)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (10617)Memory used [KB]: 1791
% 0.21/0.53  % (10617)Time elapsed: 0.080 s
% 0.21/0.53  % (10617)------------------------------
% 0.21/0.53  % (10617)------------------------------
% 0.21/0.53  % (10593)Success in time 0.167 s
%------------------------------------------------------------------------------
