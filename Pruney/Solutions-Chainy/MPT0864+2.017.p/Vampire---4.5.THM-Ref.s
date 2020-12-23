%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 217 expanded)
%              Number of leaves         :   10 (  65 expanded)
%              Depth                    :   16
%              Number of atoms          :  118 ( 557 expanded)
%              Number of equality atoms :   89 ( 400 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f265,plain,(
    $false ),
    inference(subsumption_resolution,[],[f253,f264])).

fof(f264,plain,(
    ! [X0,X1] : k4_tarski(X0,X1) != X1 ),
    inference(forward_demodulation,[],[f263,f181])).

fof(f181,plain,(
    ! [X0] : sK5(k1_tarski(X0)) = X0 ),
    inference(subsumption_resolution,[],[f178,f100])).

fof(f100,plain,(
    ! [X1] : k1_xboole_0 != k1_tarski(X1) ),
    inference(backward_demodulation,[],[f83,f98])).

fof(f98,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f53,f47])).

fof(f47,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f53,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f83,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f178,plain,(
    ! [X0] :
      ( sK5(k1_tarski(X0)) = X0
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(resolution,[],[f177,f49])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK5(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK5(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK5(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK5(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f177,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X0))
      | X0 = X1 ) ),
    inference(trivial_inequality_removal,[],[f172])).

fof(f172,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k1_tarski(X0)
      | ~ r2_hidden(X1,k1_tarski(X0))
      | X0 = X1 ) ),
    inference(superposition,[],[f60,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f263,plain,(
    ! [X0,X1] : k4_tarski(X0,sK5(k1_tarski(X1))) != X1 ),
    inference(subsumption_resolution,[],[f259,f100])).

fof(f259,plain,(
    ! [X0,X1] :
      ( k4_tarski(X0,sK5(k1_tarski(X1))) != X1
      | k1_xboole_0 = k1_tarski(X1) ) ),
    inference(resolution,[],[f238,f49])).

fof(f238,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | k4_tarski(X1,X2) != X0 ) ),
    inference(subsumption_resolution,[],[f237,f100])).

fof(f237,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X1,X2) != X0
      | ~ r2_hidden(X2,k1_tarski(X0))
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(superposition,[],[f51,f181])).

fof(f51,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK5(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f253,plain,(
    sK2 = k4_tarski(sK3,sK2) ),
    inference(backward_demodulation,[],[f45,f251])).

fof(f251,plain,(
    sK2 = sK4 ),
    inference(backward_demodulation,[],[f94,f250])).

fof(f250,plain,(
    sK2 = k2_mcart_1(sK2) ),
    inference(subsumption_resolution,[],[f93,f245])).

fof(f245,plain,(
    sK2 != sK3 ),
    inference(superposition,[],[f244,f45])).

fof(f244,plain,(
    ! [X0,X1] : k4_tarski(X0,X1) != X0 ),
    inference(forward_demodulation,[],[f243,f181])).

fof(f243,plain,(
    ! [X0,X1] : k4_tarski(sK5(k1_tarski(X0)),X1) != X0 ),
    inference(subsumption_resolution,[],[f239,f100])).

fof(f239,plain,(
    ! [X0,X1] :
      ( k4_tarski(sK5(k1_tarski(X0)),X1) != X0
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(resolution,[],[f234,f49])).

fof(f234,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X0))
      | k4_tarski(X1,X2) != X0 ) ),
    inference(subsumption_resolution,[],[f233,f100])).

fof(f233,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X1,X2) != X0
      | ~ r2_hidden(X1,k1_tarski(X0))
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(superposition,[],[f50,f181])).

fof(f50,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK5(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f93,plain,
    ( sK2 = k2_mcart_1(sK2)
    | sK2 = sK3 ),
    inference(backward_demodulation,[],[f46,f92])).

fof(f92,plain,(
    k1_mcart_1(sK2) = sK3 ),
    inference(superposition,[],[f58,f45])).

fof(f58,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f46,plain,
    ( sK2 = k2_mcart_1(sK2)
    | sK2 = k1_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( sK2 = k2_mcart_1(sK2)
      | sK2 = k1_mcart_1(sK2) )
    & sK2 = k4_tarski(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( sK2 = k2_mcart_1(sK2)
        | sK2 = k1_mcart_1(sK2) )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK2 ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2,X1] : k4_tarski(X1,X2) = sK2
   => sK2 = k4_tarski(sK3,sK4) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f94,plain,(
    k2_mcart_1(sK2) = sK4 ),
    inference(superposition,[],[f59,f45])).

fof(f59,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,(
    sK2 = k4_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:44:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (7910)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.46  % (7910)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % (7929)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.46  % (7929)Refutation not found, incomplete strategy% (7929)------------------------------
% 0.20/0.46  % (7929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f265,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(subsumption_resolution,[],[f253,f264])).
% 0.20/0.46  fof(f264,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k4_tarski(X0,X1) != X1) )),
% 0.20/0.46    inference(forward_demodulation,[],[f263,f181])).
% 0.20/0.46  fof(f181,plain,(
% 0.20/0.46    ( ! [X0] : (sK5(k1_tarski(X0)) = X0) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f178,f100])).
% 0.20/0.46  fof(f100,plain,(
% 0.20/0.46    ( ! [X1] : (k1_xboole_0 != k1_tarski(X1)) )),
% 0.20/0.46    inference(backward_demodulation,[],[f83,f98])).
% 0.20/0.46  fof(f98,plain,(
% 0.20/0.46    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.46    inference(superposition,[],[f53,f47])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.20/0.46  fof(f83,plain,(
% 0.20/0.46    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.20/0.46    inference(equality_resolution,[],[f62])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f32])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.20/0.46    inference(nnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,axiom,(
% 0.20/0.46    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.20/0.46  fof(f178,plain,(
% 0.20/0.46    ( ! [X0] : (sK5(k1_tarski(X0)) = X0 | k1_xboole_0 = k1_tarski(X0)) )),
% 0.20/0.46    inference(resolution,[],[f177,f49])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK5(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK5(X0),X0)) | k1_xboole_0 = X0)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f29])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK5(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK5(X0),X0)))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.20/0.46    inference(ennf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,axiom,(
% 0.20/0.47    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.20/0.47  fof(f177,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(X0)) | X0 = X1) )),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f172])).
% 0.20/0.47  fof(f172,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_tarski(X0) != k1_tarski(X0) | ~r2_hidden(X1,k1_tarski(X0)) | X0 = X1) )),
% 0.20/0.47    inference(superposition,[],[f60,f63])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f32])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,axiom,(
% 0.20/0.47    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.20/0.47  fof(f263,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_tarski(X0,sK5(k1_tarski(X1))) != X1) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f259,f100])).
% 0.20/0.47  fof(f259,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_tarski(X0,sK5(k1_tarski(X1))) != X1 | k1_xboole_0 = k1_tarski(X1)) )),
% 0.20/0.47    inference(resolution,[],[f238,f49])).
% 0.20/0.47  fof(f238,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_tarski(X0)) | k4_tarski(X1,X2) != X0) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f237,f100])).
% 0.20/0.47  fof(f237,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k4_tarski(X1,X2) != X0 | ~r2_hidden(X2,k1_tarski(X0)) | k1_xboole_0 = k1_tarski(X0)) )),
% 0.20/0.47    inference(superposition,[],[f51,f181])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK5(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f30])).
% 0.20/0.47  fof(f253,plain,(
% 0.20/0.47    sK2 = k4_tarski(sK3,sK2)),
% 0.20/0.47    inference(backward_demodulation,[],[f45,f251])).
% 0.20/0.47  fof(f251,plain,(
% 0.20/0.47    sK2 = sK4),
% 0.20/0.47    inference(backward_demodulation,[],[f94,f250])).
% 0.20/0.47  fof(f250,plain,(
% 0.20/0.47    sK2 = k2_mcart_1(sK2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f93,f245])).
% 0.20/0.47  fof(f245,plain,(
% 0.20/0.47    sK2 != sK3),
% 0.20/0.47    inference(superposition,[],[f244,f45])).
% 0.20/0.47  fof(f244,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_tarski(X0,X1) != X0) )),
% 0.20/0.47    inference(forward_demodulation,[],[f243,f181])).
% 0.20/0.47  fof(f243,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_tarski(sK5(k1_tarski(X0)),X1) != X0) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f239,f100])).
% 0.20/0.47  fof(f239,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_tarski(sK5(k1_tarski(X0)),X1) != X0 | k1_xboole_0 = k1_tarski(X0)) )),
% 0.20/0.47    inference(resolution,[],[f234,f49])).
% 0.20/0.47  fof(f234,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_tarski(X0)) | k4_tarski(X1,X2) != X0) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f233,f100])).
% 0.20/0.47  fof(f233,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k4_tarski(X1,X2) != X0 | ~r2_hidden(X1,k1_tarski(X0)) | k1_xboole_0 = k1_tarski(X0)) )),
% 0.20/0.47    inference(superposition,[],[f50,f181])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK5(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f30])).
% 0.20/0.47  fof(f93,plain,(
% 0.20/0.47    sK2 = k2_mcart_1(sK2) | sK2 = sK3),
% 0.20/0.47    inference(backward_demodulation,[],[f46,f92])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    k1_mcart_1(sK2) = sK3),
% 0.20/0.47    inference(superposition,[],[f58,f45])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,axiom,(
% 0.20/0.47    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    (sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)) & sK2 = k4_tarski(sK3,sK4)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f27,f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)) & ? [X2,X1] : k4_tarski(X1,X2) = sK2)),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ? [X2,X1] : k4_tarski(X1,X2) = sK2 => sK2 = k4_tarski(sK3,sK4)),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 0.20/0.47    inference(ennf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,negated_conjecture,(
% 0.20/0.47    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.20/0.47    inference(negated_conjecture,[],[f16])).
% 0.20/0.47  fof(f16,conjecture,(
% 0.20/0.47    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    k2_mcart_1(sK2) = sK4),
% 0.20/0.47    inference(superposition,[],[f59,f45])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    sK2 = k4_tarski(sK3,sK4)),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (7910)------------------------------
% 0.20/0.47  % (7910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (7910)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (7910)Memory used [KB]: 6396
% 0.20/0.47  % (7910)Time elapsed: 0.060 s
% 0.20/0.47  % (7910)------------------------------
% 0.20/0.47  % (7910)------------------------------
% 0.20/0.47  % (7902)Success in time 0.119 s
%------------------------------------------------------------------------------
