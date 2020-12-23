%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 114 expanded)
%              Number of leaves         :   10 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :  129 ( 367 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f107,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f65,f49,f78,f34])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f78,plain,(
    r2_hidden(sK5(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1)),sK4(sK1,sK2(sK0,k3_tarski(sK1)))) ),
    inference(unit_resulting_resolution,[],[f45,f48,f34])).

fof(f48,plain,(
    r2_hidden(sK5(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1)),sK2(sK0,k3_tarski(sK1))) ),
    inference(unit_resulting_resolution,[],[f38,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f38,plain,(
    ~ r1_tarski(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1)) ),
    inference(unit_resulting_resolution,[],[f26,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK2(X0,X1),X1)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f26,plain,(
    ~ r1_tarski(k3_tarski(sK0),k3_tarski(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(k3_tarski(sK0),k3_tarski(sK1))
    & r1_setfam_1(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k3_tarski(X0),k3_tarski(X1))
        & r1_setfam_1(X0,X1) )
   => ( ~ r1_tarski(k3_tarski(sK0),k3_tarski(sK1))
      & r1_setfam_1(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k3_tarski(X0),k3_tarski(X1))
      & r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_setfam_1(X0,X1)
       => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_setfam_1)).

fof(f45,plain,(
    r1_tarski(sK2(sK0,k3_tarski(sK1)),sK4(sK1,sK2(sK0,k3_tarski(sK1)))) ),
    inference(unit_resulting_resolution,[],[f25,f37,f31])).

fof(f31,plain,(
    ! [X4,X0,X1] :
      ( r1_tarski(X4,sK4(X1,X4))
      | ~ r2_hidden(X4,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ( ! [X3] :
              ( ~ r1_tarski(sK3(X0,X1),X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X4] :
            ( ( r1_tarski(X4,sK4(X1,X4))
              & r2_hidden(sK4(X1,X4),X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f17,f19,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) )
     => ( ! [X3] :
            ( ~ r1_tarski(sK3(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X4,X1] :
      ( ? [X5] :
          ( r1_tarski(X4,X5)
          & r2_hidden(X5,X1) )
     => ( r1_tarski(X4,sK4(X1,X4))
        & r2_hidden(sK4(X1,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( r1_tarski(X4,X5)
                & r2_hidden(X5,X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( r1_tarski(X2,X3)
                & r2_hidden(X3,X1) )
            | ~ r2_hidden(X2,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f37,plain,(
    r2_hidden(sK2(sK0,k3_tarski(sK1)),sK0) ),
    inference(unit_resulting_resolution,[],[f26,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f25,plain,(
    r1_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f49,plain,(
    ~ r2_hidden(sK5(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1)),k3_tarski(sK1)) ),
    inference(unit_resulting_resolution,[],[f38,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    r1_tarski(sK4(sK1,sK2(sK0,k3_tarski(sK1))),k3_tarski(sK1)) ),
    inference(unit_resulting_resolution,[],[f44,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f44,plain,(
    r2_hidden(sK4(sK1,sK2(sK0,k3_tarski(sK1))),sK1) ),
    inference(unit_resulting_resolution,[],[f25,f37,f30])).

fof(f30,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(sK4(X1,X4),X1)
      | ~ r2_hidden(X4,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:21:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (24012)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.22/0.48  % (24007)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (24004)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.49  % (24004)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (24013)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.22/0.49  % (24005)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f65,f49,f78,f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.50    inference(rectify,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.50    inference(nnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    r2_hidden(sK5(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1)),sK4(sK1,sK2(sK0,k3_tarski(sK1))))),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f45,f48,f34])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    r2_hidden(sK5(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1)),sK2(sK0,k3_tarski(sK1)))),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f38,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ~r1_tarski(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1))),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f26,f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(sK2(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | (~r1_tarski(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)) => (~r1_tarski(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ~r1_tarski(k3_tarski(sK0),k3_tarski(sK1))),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ~r1_tarski(k3_tarski(sK0),k3_tarski(sK1)) & r1_setfam_1(sK0,sK1)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ? [X0,X1] : (~r1_tarski(k3_tarski(X0),k3_tarski(X1)) & r1_setfam_1(X0,X1)) => (~r1_tarski(k3_tarski(sK0),k3_tarski(sK1)) & r1_setfam_1(sK0,sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f7,plain,(
% 0.22/0.50    ? [X0,X1] : (~r1_tarski(k3_tarski(X0),k3_tarski(X1)) & r1_setfam_1(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1] : (r1_setfam_1(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.22/0.50    inference(negated_conjecture,[],[f5])).
% 0.22/0.50  fof(f5,conjecture,(
% 0.22/0.50    ! [X0,X1] : (r1_setfam_1(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_setfam_1)).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    r1_tarski(sK2(sK0,k3_tarski(sK1)),sK4(sK1,sK2(sK0,k3_tarski(sK1))))),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f25,f37,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X4,X0,X1] : (r1_tarski(X4,sK4(X1,X4)) | ~r2_hidden(X4,X0) | ~r1_setfam_1(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_setfam_1(X0,X1) | (! [X3] : (~r1_tarski(sK3(X0,X1),X3) | ~r2_hidden(X3,X1)) & r2_hidden(sK3(X0,X1),X0))) & (! [X4] : ((r1_tarski(X4,sK4(X1,X4)) & r2_hidden(sK4(X1,X4),X1)) | ~r2_hidden(X4,X0)) | ~r1_setfam_1(X0,X1)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f17,f19,f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0)) => (! [X3] : (~r1_tarski(sK3(X0,X1),X3) | ~r2_hidden(X3,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X4,X1] : (? [X5] : (r1_tarski(X4,X5) & r2_hidden(X5,X1)) => (r1_tarski(X4,sK4(X1,X4)) & r2_hidden(sK4(X1,X4),X1)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_setfam_1(X0,X1) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0))) & (! [X4] : (? [X5] : (r1_tarski(X4,X5) & r2_hidden(X5,X1)) | ~r2_hidden(X4,X0)) | ~r1_setfam_1(X0,X1)))),
% 0.22/0.50    inference(rectify,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_setfam_1(X0,X1) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0))) & (! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1)))),
% 0.22/0.50    inference(nnf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    r2_hidden(sK2(sK0,k3_tarski(sK1)),sK0)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f26,f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    r1_setfam_1(sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ~r2_hidden(sK5(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1)),k3_tarski(sK1))),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f38,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    r1_tarski(sK4(sK1,sK2(sK0,k3_tarski(sK1))),k3_tarski(sK1))),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f44,f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    r2_hidden(sK4(sK1,sK2(sK0,k3_tarski(sK1))),sK1)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f25,f37,f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ( ! [X4,X0,X1] : (r2_hidden(sK4(X1,X4),X1) | ~r2_hidden(X4,X0) | ~r1_setfam_1(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (24004)------------------------------
% 0.22/0.50  % (24004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (24004)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (24004)Memory used [KB]: 895
% 0.22/0.50  % (24004)Time elapsed: 0.059 s
% 0.22/0.50  % (24004)------------------------------
% 0.22/0.50  % (24004)------------------------------
% 0.22/0.50  % (24009)WARNING: option uwaf not known.
% 0.22/0.50  % (23998)Success in time 0.128 s
%------------------------------------------------------------------------------
