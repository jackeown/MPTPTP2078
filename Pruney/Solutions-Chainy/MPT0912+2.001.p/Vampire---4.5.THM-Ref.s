%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:35 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   42 (  96 expanded)
%              Number of leaves         :    7 (  24 expanded)
%              Depth                    :   21
%              Number of atoms          :  161 ( 397 expanded)
%              Number of equality atoms :   39 ( 102 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f46,plain,(
    $false ),
    inference(subsumption_resolution,[],[f45,f26])).

fof(f26,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f15,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f15,plain,(
    r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ! [X4,X5,X6] :
        ( k3_mcart_1(X4,X5,X6) != sK0
        | ~ r2_hidden(X6,sK3)
        | ~ r2_hidden(X5,sK2)
        | ~ r2_hidden(X4,sK1) )
    & r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4,X5,X6] :
            ( k3_mcart_1(X4,X5,X6) != X0
            | ~ r2_hidden(X6,X3)
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X4,X1) )
        & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) )
   => ( ! [X6,X5,X4] :
          ( k3_mcart_1(X4,X5,X6) != sK0
          | ~ r2_hidden(X6,sK3)
          | ~ r2_hidden(X5,sK2)
          | ~ r2_hidden(X4,sK1) )
      & r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5,X6] :
          ( k3_mcart_1(X4,X5,X6) != X0
          | ~ r2_hidden(X6,X3)
          | ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1) )
      & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ! [X4,X5,X6] :
              ~ ( k3_mcart_1(X4,X5,X6) = X0
                & r2_hidden(X6,X3)
                & r2_hidden(X5,X2)
                & r2_hidden(X4,X1) )
          & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5,X6] :
            ~ ( k3_mcart_1(X4,X5,X6) = X0
              & r2_hidden(X6,X3)
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_mcart_1)).

fof(f45,plain,(
    ~ r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( sK0 != X0
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ) ),
    inference(duplicate_literal_removal,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( sK0 != X0
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ) ),
    inference(resolution,[],[f42,f27])).

fof(f27,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
      | sK0 != X0
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ) ),
    inference(duplicate_literal_removal,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
      | sK0 != X0
      | ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ) ),
    inference(resolution,[],[f40,f27])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
      | ~ r2_hidden(X0,X1)
      | sK0 != X0
      | ~ r2_hidden(X0,X2)
      | ~ r1_tarski(X2,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ) ),
    inference(resolution,[],[f39,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK4(X1,X2,X3),X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k4_tarski(sK4(X1,X2,X3),sK5(X1,X2,X3)) = X3
        & r2_hidden(sK5(X1,X2,X3),X2)
        & r2_hidden(sK4(X1,X2,X3),X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f8,f13])).

fof(f13,plain,(
    ! [X3,X2,X1] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
     => ( k4_tarski(sK4(X1,X2,X3),sK5(X1,X2,X3)) = X3
        & r2_hidden(sK5(X1,X2,X3),X2)
        & r2_hidden(sK4(X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5] :
            ~ ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,sK3,X1),k2_zfmisc_1(sK1,sK2))
      | sK0 != X1
      | ~ r2_hidden(X1,k2_zfmisc_1(X0,sK3))
      | ~ r2_hidden(X1,X2)
      | ~ r1_tarski(X2,k2_zfmisc_1(X0,sK3)) ) ),
    inference(resolution,[],[f38,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK5(X1,X2,X3),X2)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),sK3)
      | ~ r2_hidden(sK4(X0,X1,X2),k2_zfmisc_1(sK1,sK2))
      | sK0 != X2
      | ~ r2_hidden(X2,k2_zfmisc_1(X0,X1)) ) ),
    inference(superposition,[],[f37,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK4(X1,X2,X0),sK5(X1,X2,X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(resolution,[],[f24,f27])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(X3,X0)
      | k4_tarski(sK4(X1,X2,X3),sK5(X1,X2,X3)) = X3 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_tarski(X0,X1) != sK0
      | ~ r2_hidden(X0,k2_zfmisc_1(sK1,sK2))
      | ~ r2_hidden(X1,sK3) ) ),
    inference(duplicate_literal_removal,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(sK1,sK2))
      | k4_tarski(X0,X1) != sK0
      | ~ r2_hidden(X0,k2_zfmisc_1(sK1,sK2))
      | ~ r2_hidden(X1,sK3) ) ),
    inference(resolution,[],[f35,f27])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(sK1,sK2))
      | ~ r2_hidden(X1,k2_zfmisc_1(sK1,sK2))
      | sK0 != k4_tarski(X1,X0)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,sK3) ) ),
    inference(duplicate_literal_removal,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(X1,k2_zfmisc_1(sK1,sK2))
      | ~ r2_hidden(X1,k2_zfmisc_1(sK1,sK2))
      | sK0 != k4_tarski(X1,X0)
      | ~ r2_hidden(X1,X2)
      | ~ r1_tarski(X2,k2_zfmisc_1(sK1,sK2)) ) ),
    inference(resolution,[],[f33,f27])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(sK1,sK2))
      | ~ r2_hidden(X1,sK3)
      | ~ r2_hidden(X0,k2_zfmisc_1(sK1,sK2))
      | ~ r2_hidden(X0,X2)
      | k4_tarski(X0,X1) != sK0
      | ~ r2_hidden(X0,X3)
      | ~ r1_tarski(X3,k2_zfmisc_1(sK1,sK2)) ) ),
    inference(resolution,[],[f32,f22])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK4(X2,sK2,X1),sK1)
      | sK0 != k4_tarski(X1,X0)
      | ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(X1,k2_zfmisc_1(X2,sK2))
      | ~ r2_hidden(X1,X3)
      | ~ r1_tarski(X3,k2_zfmisc_1(X2,sK2)) ) ),
    inference(resolution,[],[f31,f23])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),sK2)
      | ~ r2_hidden(X3,sK3)
      | sK0 != k4_tarski(X2,X3)
      | ~ r2_hidden(sK4(X0,X1,X2),sK1)
      | ~ r2_hidden(X2,k2_zfmisc_1(X0,X1)) ) ),
    inference(superposition,[],[f25,f30])).

fof(f25,plain,(
    ! [X6,X4,X5] :
      ( sK0 != k4_tarski(k4_tarski(X4,X5),X6)
      | ~ r2_hidden(X6,sK3)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(definition_unfolding,[],[f16,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f16,plain,(
    ! [X6,X4,X5] :
      ( k3_mcart_1(X4,X5,X6) != sK0
      | ~ r2_hidden(X6,sK3)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:50:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.37  ipcrm: permission denied for id (806715396)
% 0.20/0.38  ipcrm: permission denied for id (806813713)
% 0.20/0.46  ipcrm: permission denied for id (806912075)
% 0.20/0.47  ipcrm: permission denied for id (806944848)
% 0.20/0.50  ipcrm: permission denied for id (806977640)
% 0.20/0.52  ipcrm: permission denied for id (807010422)
% 1.28/0.69  % (30542)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.28/0.69  % (30535)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.28/0.70  % (30542)Refutation found. Thanks to Tanya!
% 1.28/0.70  % SZS status Theorem for theBenchmark
% 1.28/0.70  % SZS output start Proof for theBenchmark
% 1.28/0.70  fof(f46,plain,(
% 1.28/0.70    $false),
% 1.28/0.70    inference(subsumption_resolution,[],[f45,f26])).
% 1.28/0.70  fof(f26,plain,(
% 1.28/0.70    r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 1.28/0.70    inference(definition_unfolding,[],[f15,f21])).
% 1.28/0.70  fof(f21,plain,(
% 1.28/0.70    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.28/0.70    inference(cnf_transformation,[],[f4])).
% 1.28/0.70  fof(f4,axiom,(
% 1.28/0.70    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.28/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.28/0.70  fof(f15,plain,(
% 1.28/0.70    r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3))),
% 1.28/0.70    inference(cnf_transformation,[],[f10])).
% 1.28/0.70  fof(f10,plain,(
% 1.28/0.70    ! [X4,X5,X6] : (k3_mcart_1(X4,X5,X6) != sK0 | ~r2_hidden(X6,sK3) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1)) & r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3))),
% 1.28/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f9])).
% 1.28/0.70  fof(f9,plain,(
% 1.28/0.70    ? [X0,X1,X2,X3] : (! [X4,X5,X6] : (k3_mcart_1(X4,X5,X6) != X0 | ~r2_hidden(X6,X3) | ~r2_hidden(X5,X2) | ~r2_hidden(X4,X1)) & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3))) => (! [X6,X5,X4] : (k3_mcart_1(X4,X5,X6) != sK0 | ~r2_hidden(X6,sK3) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1)) & r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3)))),
% 1.28/0.70    introduced(choice_axiom,[])).
% 1.28/0.70  fof(f7,plain,(
% 1.28/0.70    ? [X0,X1,X2,X3] : (! [X4,X5,X6] : (k3_mcart_1(X4,X5,X6) != X0 | ~r2_hidden(X6,X3) | ~r2_hidden(X5,X2) | ~r2_hidden(X4,X1)) & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)))),
% 1.28/0.70    inference(ennf_transformation,[],[f6])).
% 1.28/0.70  fof(f6,negated_conjecture,(
% 1.28/0.70    ~! [X0,X1,X2,X3] : ~(! [X4,X5,X6] : ~(k3_mcart_1(X4,X5,X6) = X0 & r2_hidden(X6,X3) & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)))),
% 1.28/0.70    inference(negated_conjecture,[],[f5])).
% 1.28/0.70  fof(f5,conjecture,(
% 1.28/0.70    ! [X0,X1,X2,X3] : ~(! [X4,X5,X6] : ~(k3_mcart_1(X4,X5,X6) = X0 & r2_hidden(X6,X3) & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)))),
% 1.28/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_mcart_1)).
% 1.28/0.70  fof(f45,plain,(
% 1.28/0.70    ~r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 1.28/0.70    inference(equality_resolution,[],[f44])).
% 1.28/0.70  fof(f44,plain,(
% 1.28/0.70    ( ! [X0] : (sK0 != X0 | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))) )),
% 1.28/0.70    inference(duplicate_literal_removal,[],[f43])).
% 1.28/0.70  fof(f43,plain,(
% 1.28/0.70    ( ! [X0] : (sK0 != X0 | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))) )),
% 1.28/0.70    inference(resolution,[],[f42,f27])).
% 1.28/0.70  fof(f27,plain,(
% 1.28/0.70    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.28/0.70    inference(equality_resolution,[],[f18])).
% 1.28/0.70  fof(f18,plain,(
% 1.28/0.70    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.28/0.70    inference(cnf_transformation,[],[f12])).
% 1.28/0.70  fof(f12,plain,(
% 1.28/0.70    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.28/0.70    inference(flattening,[],[f11])).
% 1.28/0.70  fof(f11,plain,(
% 1.28/0.70    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.28/0.70    inference(nnf_transformation,[],[f1])).
% 1.28/0.70  fof(f1,axiom,(
% 1.28/0.70    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.28/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.28/0.70  fof(f42,plain,(
% 1.28/0.70    ( ! [X0,X1] : (~r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | sK0 != X0 | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))) )),
% 1.28/0.70    inference(duplicate_literal_removal,[],[f41])).
% 1.28/0.70  fof(f41,plain,(
% 1.28/0.70    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | sK0 != X0 | ~r2_hidden(X0,X1) | ~r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))) )),
% 1.28/0.70    inference(resolution,[],[f40,f27])).
% 1.28/0.70  fof(f40,plain,(
% 1.28/0.70    ( ! [X2,X0,X1] : (~r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r2_hidden(X0,X1) | sK0 != X0 | ~r2_hidden(X0,X2) | ~r1_tarski(X2,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))) )),
% 1.28/0.70    inference(resolution,[],[f39,f22])).
% 1.28/0.70  fof(f22,plain,(
% 1.28/0.70    ( ! [X2,X0,X3,X1] : (r2_hidden(sK4(X1,X2,X3),X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2))) )),
% 1.28/0.70    inference(cnf_transformation,[],[f14])).
% 1.28/0.70  fof(f14,plain,(
% 1.28/0.70    ! [X0,X1,X2,X3] : ((k4_tarski(sK4(X1,X2,X3),sK5(X1,X2,X3)) = X3 & r2_hidden(sK5(X1,X2,X3),X2) & r2_hidden(sK4(X1,X2,X3),X1)) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 1.28/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f8,f13])).
% 1.28/0.70  fof(f13,plain,(
% 1.28/0.70    ! [X3,X2,X1] : (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) => (k4_tarski(sK4(X1,X2,X3),sK5(X1,X2,X3)) = X3 & r2_hidden(sK5(X1,X2,X3),X2) & r2_hidden(sK4(X1,X2,X3),X1)))),
% 1.28/0.70    introduced(choice_axiom,[])).
% 1.28/0.70  fof(f8,plain,(
% 1.28/0.70    ! [X0,X1,X2,X3] : (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 1.28/0.70    inference(ennf_transformation,[],[f2])).
% 1.28/0.70  fof(f2,axiom,(
% 1.28/0.70    ! [X0,X1,X2,X3] : ~(! [X4,X5] : ~(k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 1.28/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).
% 1.28/0.70  fof(f39,plain,(
% 1.28/0.70    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,sK3,X1),k2_zfmisc_1(sK1,sK2)) | sK0 != X1 | ~r2_hidden(X1,k2_zfmisc_1(X0,sK3)) | ~r2_hidden(X1,X2) | ~r1_tarski(X2,k2_zfmisc_1(X0,sK3))) )),
% 1.28/0.70    inference(resolution,[],[f38,f23])).
% 1.28/0.70  fof(f23,plain,(
% 1.28/0.70    ( ! [X2,X0,X3,X1] : (r2_hidden(sK5(X1,X2,X3),X2) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2))) )),
% 1.28/0.70    inference(cnf_transformation,[],[f14])).
% 1.28/0.70  fof(f38,plain,(
% 1.28/0.70    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1,X2),sK3) | ~r2_hidden(sK4(X0,X1,X2),k2_zfmisc_1(sK1,sK2)) | sK0 != X2 | ~r2_hidden(X2,k2_zfmisc_1(X0,X1))) )),
% 1.28/0.70    inference(superposition,[],[f37,f30])).
% 1.28/0.70  fof(f30,plain,(
% 1.28/0.70    ( ! [X2,X0,X1] : (k4_tarski(sK4(X1,X2,X0),sK5(X1,X2,X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.28/0.70    inference(resolution,[],[f24,f27])).
% 1.28/0.70  fof(f24,plain,(
% 1.28/0.70    ( ! [X2,X0,X3,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~r2_hidden(X3,X0) | k4_tarski(sK4(X1,X2,X3),sK5(X1,X2,X3)) = X3) )),
% 1.28/0.70    inference(cnf_transformation,[],[f14])).
% 1.28/0.70  fof(f37,plain,(
% 1.28/0.70    ( ! [X0,X1] : (k4_tarski(X0,X1) != sK0 | ~r2_hidden(X0,k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(X1,sK3)) )),
% 1.28/0.70    inference(duplicate_literal_removal,[],[f36])).
% 1.28/0.70  fof(f36,plain,(
% 1.28/0.70    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(sK1,sK2)) | k4_tarski(X0,X1) != sK0 | ~r2_hidden(X0,k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(X1,sK3)) )),
% 1.28/0.70    inference(resolution,[],[f35,f27])).
% 1.28/0.70  fof(f35,plain,(
% 1.28/0.70    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(X1,k2_zfmisc_1(sK1,sK2)) | sK0 != k4_tarski(X1,X0) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,sK3)) )),
% 1.28/0.70    inference(duplicate_literal_removal,[],[f34])).
% 1.28/0.70  fof(f34,plain,(
% 1.28/0.70    ( ! [X2,X0,X1] : (~r2_hidden(X0,sK3) | ~r2_hidden(X1,k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(X1,k2_zfmisc_1(sK1,sK2)) | sK0 != k4_tarski(X1,X0) | ~r2_hidden(X1,X2) | ~r1_tarski(X2,k2_zfmisc_1(sK1,sK2))) )),
% 1.28/0.70    inference(resolution,[],[f33,f27])).
% 1.28/0.70  fof(f33,plain,(
% 1.28/0.70    ( ! [X2,X0,X3,X1] : (~r1_tarski(X2,k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(X1,sK3) | ~r2_hidden(X0,k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(X0,X2) | k4_tarski(X0,X1) != sK0 | ~r2_hidden(X0,X3) | ~r1_tarski(X3,k2_zfmisc_1(sK1,sK2))) )),
% 1.28/0.70    inference(resolution,[],[f32,f22])).
% 1.28/0.70  fof(f32,plain,(
% 1.28/0.70    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK4(X2,sK2,X1),sK1) | sK0 != k4_tarski(X1,X0) | ~r2_hidden(X0,sK3) | ~r2_hidden(X1,k2_zfmisc_1(X2,sK2)) | ~r2_hidden(X1,X3) | ~r1_tarski(X3,k2_zfmisc_1(X2,sK2))) )),
% 1.28/0.70    inference(resolution,[],[f31,f23])).
% 1.28/0.70  fof(f31,plain,(
% 1.28/0.70    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK5(X0,X1,X2),sK2) | ~r2_hidden(X3,sK3) | sK0 != k4_tarski(X2,X3) | ~r2_hidden(sK4(X0,X1,X2),sK1) | ~r2_hidden(X2,k2_zfmisc_1(X0,X1))) )),
% 1.28/0.70    inference(superposition,[],[f25,f30])).
% 1.28/0.70  fof(f25,plain,(
% 1.28/0.70    ( ! [X6,X4,X5] : (sK0 != k4_tarski(k4_tarski(X4,X5),X6) | ~r2_hidden(X6,sK3) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1)) )),
% 1.28/0.70    inference(definition_unfolding,[],[f16,f20])).
% 1.28/0.70  fof(f20,plain,(
% 1.28/0.70    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.28/0.70    inference(cnf_transformation,[],[f3])).
% 1.28/0.70  fof(f3,axiom,(
% 1.28/0.70    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.28/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.28/0.70  fof(f16,plain,(
% 1.28/0.70    ( ! [X6,X4,X5] : (k3_mcart_1(X4,X5,X6) != sK0 | ~r2_hidden(X6,sK3) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1)) )),
% 1.28/0.70    inference(cnf_transformation,[],[f10])).
% 1.28/0.70  % SZS output end Proof for theBenchmark
% 1.28/0.70  % (30542)------------------------------
% 1.28/0.70  % (30542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.70  % (30542)Termination reason: Refutation
% 1.28/0.70  
% 1.28/0.70  % (30542)Memory used [KB]: 6268
% 1.28/0.70  % (30542)Time elapsed: 0.061 s
% 1.28/0.70  % (30542)------------------------------
% 1.28/0.70  % (30542)------------------------------
% 1.28/0.70  % (30523)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.28/0.71  % (30359)Success in time 0.347 s
%------------------------------------------------------------------------------
