%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   37 (  96 expanded)
%              Number of leaves         :    7 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  129 ( 419 expanded)
%              Number of equality atoms :   45 ( 140 expanded)
%              Maximal formula depth    :    9 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f140,plain,(
    $false ),
    inference(subsumption_resolution,[],[f139,f21])).

fof(f21,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( ~ r1_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK3,k1_tarski(sK1)))
      | ~ r1_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK3)) )
    & sK0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1)))
          | ~ r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3)) )
        & X0 != X1 )
   => ( ( ~ r1_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK3,k1_tarski(sK1)))
        | ~ r1_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK3)) )
      & sK0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1)))
        | ~ r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3)) )
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( X0 != X1
       => ( r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1)))
          & r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( X0 != X1
     => ( r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1)))
        & r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_zfmisc_1)).

fof(f139,plain,(
    sK0 = sK1 ),
    inference(forward_demodulation,[],[f138,f124])).

fof(f124,plain,(
    sK0 = sK4(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f117,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,X1))
      | sK4(k1_tarski(X0),X1) = X0 ) ),
    inference(resolution,[],[f39,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | sK4(k1_tarski(X0),X1) = X0 ) ),
    inference(resolution,[],[f25,f37])).

fof(f37,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f18,f19])).

fof(f19,plain,(
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

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f17,plain,(
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

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f11,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f117,plain,
    ( sK0 = sK4(k1_tarski(sK0),k1_tarski(sK1))
    | ~ r1_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK3,k1_tarski(sK1))) ),
    inference(resolution,[],[f53,f22])).

fof(f22,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK3))
    | ~ r1_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK3,k1_tarski(sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,(
    ! [X6,X4,X7,X5] :
      ( r1_xboole_0(k2_zfmisc_1(k1_tarski(X4),X6),k2_zfmisc_1(X5,X7))
      | sK4(k1_tarski(X4),X5) = X4 ) ),
    inference(resolution,[],[f39,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f138,plain,(
    sK1 = sK4(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f131,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,k1_tarski(X1)))
      | sK4(X0,k1_tarski(X1)) = X1 ) ),
    inference(resolution,[],[f40,f34])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,k1_tarski(X1))
      | sK4(X0,k1_tarski(X1)) = X1 ) ),
    inference(resolution,[],[f26,f37])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f131,plain,
    ( sK1 = sK4(k1_tarski(sK0),k1_tarski(sK1))
    | ~ r1_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK3,k1_tarski(sK1))) ),
    inference(resolution,[],[f55,f22])).

fof(f55,plain,(
    ! [X6,X4,X7,X5] :
      ( r1_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(k1_tarski(X5),X7))
      | sK4(X4,k1_tarski(X5)) = X5 ) ),
    inference(resolution,[],[f40,f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:59:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.45  % (1699)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.45  % (1677)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.46  % (1677)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f140,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(subsumption_resolution,[],[f139,f21])).
% 0.22/0.46  fof(f21,plain,(
% 0.22/0.46    sK0 != sK1),
% 0.22/0.46    inference(cnf_transformation,[],[f14])).
% 0.22/0.46  fof(f14,plain,(
% 0.22/0.46    (~r1_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK3,k1_tarski(sK1))) | ~r1_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK3))) & sK0 != sK1),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f13])).
% 0.22/0.46  fof(f13,plain,(
% 0.22/0.46    ? [X0,X1,X2,X3] : ((~r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1))) | ~r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3))) & X0 != X1) => ((~r1_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK3,k1_tarski(sK1))) | ~r1_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK3))) & sK0 != sK1)),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f10,plain,(
% 0.22/0.46    ? [X0,X1,X2,X3] : ((~r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1))) | ~r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3))) & X0 != X1)),
% 0.22/0.46    inference(ennf_transformation,[],[f8])).
% 0.22/0.46  fof(f8,negated_conjecture,(
% 0.22/0.46    ~! [X0,X1,X2,X3] : (X0 != X1 => (r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1))) & r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3))))),
% 0.22/0.46    inference(negated_conjecture,[],[f7])).
% 0.22/0.46  fof(f7,conjecture,(
% 0.22/0.46    ! [X0,X1,X2,X3] : (X0 != X1 => (r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1))) & r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_zfmisc_1)).
% 0.22/0.46  fof(f139,plain,(
% 0.22/0.46    sK0 = sK1),
% 0.22/0.46    inference(forward_demodulation,[],[f138,f124])).
% 0.22/0.46  fof(f124,plain,(
% 0.22/0.46    sK0 = sK4(k1_tarski(sK0),k1_tarski(sK1))),
% 0.22/0.46    inference(subsumption_resolution,[],[f117,f52])).
% 0.22/0.46  fof(f52,plain,(
% 0.22/0.46    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,X1)) | sK4(k1_tarski(X0),X1) = X0) )),
% 0.22/0.46    inference(resolution,[],[f39,f34])).
% 0.22/0.46  fof(f34,plain,(
% 0.22/0.46    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f12])).
% 0.22/0.46  fof(f12,plain,(
% 0.22/0.46    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.46    inference(ennf_transformation,[],[f6])).
% 0.22/0.46  fof(f6,axiom,(
% 0.22/0.46    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 0.22/0.46  fof(f39,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | sK4(k1_tarski(X0),X1) = X0) )),
% 0.22/0.46    inference(resolution,[],[f25,f37])).
% 0.22/0.46  fof(f37,plain,(
% 0.22/0.46    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.22/0.46    inference(equality_resolution,[],[f28])).
% 0.22/0.46  fof(f28,plain,(
% 0.22/0.46    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.46    inference(cnf_transformation,[],[f20])).
% 0.22/0.46  fof(f20,plain,(
% 0.22/0.46    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f18,f19])).
% 0.22/0.46  fof(f19,plain,(
% 0.22/0.46    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f18,plain,(
% 0.22/0.46    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.46    inference(rectify,[],[f17])).
% 0.22/0.46  fof(f17,plain,(
% 0.22/0.46    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.46    inference(nnf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.46  fof(f25,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f16])).
% 0.22/0.46  fof(f16,plain,(
% 0.22/0.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f11,f15])).
% 0.22/0.46  fof(f15,plain,(
% 0.22/0.46    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f11,plain,(
% 0.22/0.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.46    inference(ennf_transformation,[],[f9])).
% 0.22/0.46  fof(f9,plain,(
% 0.22/0.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.46    inference(rectify,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.46  fof(f117,plain,(
% 0.22/0.46    sK0 = sK4(k1_tarski(sK0),k1_tarski(sK1)) | ~r1_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK3,k1_tarski(sK1)))),
% 0.22/0.46    inference(resolution,[],[f53,f22])).
% 0.22/0.46  fof(f22,plain,(
% 0.22/0.46    ~r1_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK3)) | ~r1_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK3,k1_tarski(sK1)))),
% 0.22/0.46    inference(cnf_transformation,[],[f14])).
% 0.22/0.46  fof(f53,plain,(
% 0.22/0.46    ( ! [X6,X4,X7,X5] : (r1_xboole_0(k2_zfmisc_1(k1_tarski(X4),X6),k2_zfmisc_1(X5,X7)) | sK4(k1_tarski(X4),X5) = X4) )),
% 0.22/0.46    inference(resolution,[],[f39,f33])).
% 0.22/0.46  fof(f33,plain,(
% 0.22/0.46    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f12])).
% 0.22/0.46  fof(f138,plain,(
% 0.22/0.46    sK1 = sK4(k1_tarski(sK0),k1_tarski(sK1))),
% 0.22/0.46    inference(subsumption_resolution,[],[f131,f54])).
% 0.22/0.46  fof(f54,plain,(
% 0.22/0.46    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,k1_tarski(X1))) | sK4(X0,k1_tarski(X1)) = X1) )),
% 0.22/0.46    inference(resolution,[],[f40,f34])).
% 0.22/0.46  fof(f40,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_xboole_0(X0,k1_tarski(X1)) | sK4(X0,k1_tarski(X1)) = X1) )),
% 0.22/0.46    inference(resolution,[],[f26,f37])).
% 0.22/0.46  fof(f26,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f16])).
% 0.22/0.46  fof(f131,plain,(
% 0.22/0.46    sK1 = sK4(k1_tarski(sK0),k1_tarski(sK1)) | ~r1_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK3,k1_tarski(sK1)))),
% 0.22/0.46    inference(resolution,[],[f55,f22])).
% 0.22/0.46  fof(f55,plain,(
% 0.22/0.46    ( ! [X6,X4,X7,X5] : (r1_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(k1_tarski(X5),X7)) | sK4(X4,k1_tarski(X5)) = X5) )),
% 0.22/0.46    inference(resolution,[],[f40,f33])).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (1677)------------------------------
% 0.22/0.46  % (1677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (1677)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (1677)Memory used [KB]: 1791
% 0.22/0.46  % (1677)Time elapsed: 0.053 s
% 0.22/0.46  % (1677)------------------------------
% 0.22/0.46  % (1677)------------------------------
% 0.22/0.46  % (1669)Success in time 0.1 s
%------------------------------------------------------------------------------
