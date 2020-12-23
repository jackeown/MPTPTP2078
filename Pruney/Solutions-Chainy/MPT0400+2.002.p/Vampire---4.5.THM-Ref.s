%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 119 expanded)
%              Number of leaves         :    7 (  35 expanded)
%              Depth                    :   20
%              Number of atoms          :  125 ( 493 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f118,plain,(
    $false ),
    inference(global_subsumption,[],[f20,f18,f117])).

fof(f117,plain,
    ( ~ r1_setfam_1(sK0,sK1)
    | r1_setfam_1(sK0,sK2) ),
    inference(resolution,[],[f116,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f14,f16,f15])).

fof(f15,plain,(
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

fof(f16,plain,(
    ! [X4,X1] :
      ( ? [X5] :
          ( r1_tarski(X4,X5)
          & r2_hidden(X5,X1) )
     => ( r1_tarski(X4,sK4(X1,X4))
        & r2_hidden(sK4(X1,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
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
    inference(rectify,[],[f13])).

fof(f13,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f116,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK0,sK2),X0)
      | ~ r1_setfam_1(X0,sK1) ) ),
    inference(global_subsumption,[],[f19,f115])).

fof(f115,plain,(
    ! [X0] :
      ( ~ r1_setfam_1(sK1,sK2)
      | ~ r2_hidden(sK3(sK0,sK2),X0)
      | ~ r1_setfam_1(X0,sK1) ) ),
    inference(resolution,[],[f113,f22])).

fof(f22,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(sK4(X1,X4),X1)
      | ~ r2_hidden(X4,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f113,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(sK1,sK3(sK0,sK2)),X0)
      | ~ r1_setfam_1(X0,sK2) ) ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(sK1,sK3(sK0,sK2)),X0)
      | ~ r1_setfam_1(X0,sK2)
      | ~ r1_setfam_1(X0,sK2) ) ),
    inference(factoring,[],[f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(sK1,sK3(sK0,sK2)),X0)
      | ~ r2_hidden(sK4(sK1,sK3(sK0,sK2)),X1)
      | ~ r1_setfam_1(X0,sK2)
      | ~ r1_setfam_1(X1,sK2) ) ),
    inference(resolution,[],[f93,f22])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,sK4(sK1,sK3(sK0,sK2))),sK2)
      | ~ r2_hidden(sK4(sK1,sK3(sK0,sK2)),X1)
      | ~ r1_setfam_1(X1,X0) ) ),
    inference(resolution,[],[f92,f23])).

fof(f23,plain,(
    ! [X4,X0,X1] :
      ( r1_tarski(X4,sK4(X1,X4))
      | ~ r2_hidden(X4,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f92,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK4(sK1,sK3(sK0,sK2)),X0)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(global_subsumption,[],[f20,f90])).

fof(f90,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK4(sK1,sK3(sK0,sK2)),X0)
      | r1_setfam_1(sK0,sK2)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f89,f25])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(sK3(X0,X1),X3)
      | r1_setfam_1(X0,X1)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f89,plain,(
    ! [X5] :
      ( r1_tarski(sK3(sK0,sK2),X5)
      | ~ r1_tarski(sK4(sK1,sK3(sK0,sK2)),X5) ) ),
    inference(superposition,[],[f26,f84])).

fof(f84,plain,(
    sK4(sK1,sK3(sK0,sK2)) = k2_xboole_0(sK3(sK0,sK2),sK4(sK1,sK3(sK0,sK2))) ),
    inference(resolution,[],[f80,f18])).

fof(f80,plain,(
    ! [X0] :
      ( ~ r1_setfam_1(sK0,X0)
      | sK4(X0,sK3(sK0,sK2)) = k2_xboole_0(sK3(sK0,sK2),sK4(X0,sK3(sK0,sK2))) ) ),
    inference(resolution,[],[f30,f20])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_setfam_1(X0,X1)
      | sK4(X2,sK3(X0,X1)) = k2_xboole_0(sK3(X0,X1),sK4(X2,sK3(X0,X1)))
      | ~ r1_setfam_1(X0,X2) ) ),
    inference(resolution,[],[f27,f24])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_setfam_1(X1,X2)
      | sK4(X2,X0) = k2_xboole_0(X0,sK4(X2,X0)) ) ),
    inference(resolution,[],[f23,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f19,plain,(
    r1_setfam_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ r1_setfam_1(sK0,sK2)
    & r1_setfam_1(sK1,sK2)
    & r1_setfam_1(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_setfam_1(X0,X2)
        & r1_setfam_1(X1,X2)
        & r1_setfam_1(X0,X1) )
   => ( ~ r1_setfam_1(sK0,sK2)
      & r1_setfam_1(sK1,sK2)
      & r1_setfam_1(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_setfam_1(X0,X2)
      & r1_setfam_1(X1,X2)
      & r1_setfam_1(X0,X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_setfam_1(X0,X2)
      & r1_setfam_1(X1,X2)
      & r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_setfam_1(X1,X2)
          & r1_setfam_1(X0,X1) )
       => r1_setfam_1(X0,X2) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_setfam_1(X1,X2)
        & r1_setfam_1(X0,X1) )
     => r1_setfam_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_setfam_1)).

fof(f18,plain,(
    r1_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f20,plain,(
    ~ r1_setfam_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:19:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.43  % (15609)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.44  % (15604)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.44  % (15608)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.44  % (15611)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.20/0.44  % (15604)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f118,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(global_subsumption,[],[f20,f18,f117])).
% 0.20/0.44  fof(f117,plain,(
% 0.20/0.44    ~r1_setfam_1(sK0,sK1) | r1_setfam_1(sK0,sK2)),
% 0.20/0.44    inference(resolution,[],[f116,f24])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_setfam_1(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f17])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    ! [X0,X1] : ((r1_setfam_1(X0,X1) | (! [X3] : (~r1_tarski(sK3(X0,X1),X3) | ~r2_hidden(X3,X1)) & r2_hidden(sK3(X0,X1),X0))) & (! [X4] : ((r1_tarski(X4,sK4(X1,X4)) & r2_hidden(sK4(X1,X4),X1)) | ~r2_hidden(X4,X0)) | ~r1_setfam_1(X0,X1)))),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f14,f16,f15])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0)) => (! [X3] : (~r1_tarski(sK3(X0,X1),X3) | ~r2_hidden(X3,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    ! [X4,X1] : (? [X5] : (r1_tarski(X4,X5) & r2_hidden(X5,X1)) => (r1_tarski(X4,sK4(X1,X4)) & r2_hidden(sK4(X1,X4),X1)))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    ! [X0,X1] : ((r1_setfam_1(X0,X1) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0))) & (! [X4] : (? [X5] : (r1_tarski(X4,X5) & r2_hidden(X5,X1)) | ~r2_hidden(X4,X0)) | ~r1_setfam_1(X0,X1)))),
% 0.20/0.44    inference(rectify,[],[f13])).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    ! [X0,X1] : ((r1_setfam_1(X0,X1) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0))) & (! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1)))),
% 0.20/0.44    inference(nnf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,plain,(
% 0.20/0.44    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.20/0.44  fof(f116,plain,(
% 0.20/0.44    ( ! [X0] : (~r2_hidden(sK3(sK0,sK2),X0) | ~r1_setfam_1(X0,sK1)) )),
% 0.20/0.44    inference(global_subsumption,[],[f19,f115])).
% 0.20/0.44  fof(f115,plain,(
% 0.20/0.44    ( ! [X0] : (~r1_setfam_1(sK1,sK2) | ~r2_hidden(sK3(sK0,sK2),X0) | ~r1_setfam_1(X0,sK1)) )),
% 0.20/0.44    inference(resolution,[],[f113,f22])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    ( ! [X4,X0,X1] : (r2_hidden(sK4(X1,X4),X1) | ~r2_hidden(X4,X0) | ~r1_setfam_1(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f17])).
% 0.20/0.44  fof(f113,plain,(
% 0.20/0.44    ( ! [X0] : (~r2_hidden(sK4(sK1,sK3(sK0,sK2)),X0) | ~r1_setfam_1(X0,sK2)) )),
% 0.20/0.44    inference(duplicate_literal_removal,[],[f112])).
% 0.20/0.44  fof(f112,plain,(
% 0.20/0.44    ( ! [X0] : (~r2_hidden(sK4(sK1,sK3(sK0,sK2)),X0) | ~r1_setfam_1(X0,sK2) | ~r1_setfam_1(X0,sK2)) )),
% 0.20/0.44    inference(factoring,[],[f104])).
% 0.20/0.44  fof(f104,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r2_hidden(sK4(sK1,sK3(sK0,sK2)),X0) | ~r2_hidden(sK4(sK1,sK3(sK0,sK2)),X1) | ~r1_setfam_1(X0,sK2) | ~r1_setfam_1(X1,sK2)) )),
% 0.20/0.44    inference(resolution,[],[f93,f22])).
% 0.20/0.44  fof(f93,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r2_hidden(sK4(X0,sK4(sK1,sK3(sK0,sK2))),sK2) | ~r2_hidden(sK4(sK1,sK3(sK0,sK2)),X1) | ~r1_setfam_1(X1,X0)) )),
% 0.20/0.44    inference(resolution,[],[f92,f23])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    ( ! [X4,X0,X1] : (r1_tarski(X4,sK4(X1,X4)) | ~r2_hidden(X4,X0) | ~r1_setfam_1(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f17])).
% 0.20/0.44  fof(f92,plain,(
% 0.20/0.44    ( ! [X0] : (~r1_tarski(sK4(sK1,sK3(sK0,sK2)),X0) | ~r2_hidden(X0,sK2)) )),
% 0.20/0.44    inference(global_subsumption,[],[f20,f90])).
% 0.20/0.44  fof(f90,plain,(
% 0.20/0.44    ( ! [X0] : (~r1_tarski(sK4(sK1,sK3(sK0,sK2)),X0) | r1_setfam_1(sK0,sK2) | ~r2_hidden(X0,sK2)) )),
% 0.20/0.44    inference(resolution,[],[f89,f25])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ( ! [X0,X3,X1] : (~r1_tarski(sK3(X0,X1),X3) | r1_setfam_1(X0,X1) | ~r2_hidden(X3,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f17])).
% 0.20/0.44  fof(f89,plain,(
% 0.20/0.44    ( ! [X5] : (r1_tarski(sK3(sK0,sK2),X5) | ~r1_tarski(sK4(sK1,sK3(sK0,sK2)),X5)) )),
% 0.20/0.44    inference(superposition,[],[f26,f84])).
% 0.20/0.44  fof(f84,plain,(
% 0.20/0.44    sK4(sK1,sK3(sK0,sK2)) = k2_xboole_0(sK3(sK0,sK2),sK4(sK1,sK3(sK0,sK2)))),
% 0.20/0.44    inference(resolution,[],[f80,f18])).
% 0.20/0.44  fof(f80,plain,(
% 0.20/0.44    ( ! [X0] : (~r1_setfam_1(sK0,X0) | sK4(X0,sK3(sK0,sK2)) = k2_xboole_0(sK3(sK0,sK2),sK4(X0,sK3(sK0,sK2)))) )),
% 0.20/0.44    inference(resolution,[],[f30,f20])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (r1_setfam_1(X0,X1) | sK4(X2,sK3(X0,X1)) = k2_xboole_0(sK3(X0,X1),sK4(X2,sK3(X0,X1))) | ~r1_setfam_1(X0,X2)) )),
% 0.20/0.44    inference(resolution,[],[f27,f24])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r1_setfam_1(X1,X2) | sK4(X2,X0) = k2_xboole_0(X0,sK4(X2,X0))) )),
% 0.20/0.44    inference(resolution,[],[f23,f21])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.20/0.44    inference(cnf_transformation,[],[f8])).
% 0.20/0.44  fof(f8,plain,(
% 0.20/0.44    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f10])).
% 0.20/0.44  fof(f10,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.20/0.44    inference(ennf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    r1_setfam_1(sK1,sK2)),
% 0.20/0.44    inference(cnf_transformation,[],[f12])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    ~r1_setfam_1(sK0,sK2) & r1_setfam_1(sK1,sK2) & r1_setfam_1(sK0,sK1)),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f11])).
% 0.20/0.44  fof(f11,plain,(
% 0.20/0.44    ? [X0,X1,X2] : (~r1_setfam_1(X0,X2) & r1_setfam_1(X1,X2) & r1_setfam_1(X0,X1)) => (~r1_setfam_1(sK0,sK2) & r1_setfam_1(sK1,sK2) & r1_setfam_1(sK0,sK1))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f7,plain,(
% 0.20/0.44    ? [X0,X1,X2] : (~r1_setfam_1(X0,X2) & r1_setfam_1(X1,X2) & r1_setfam_1(X0,X1))),
% 0.20/0.44    inference(flattening,[],[f6])).
% 0.20/0.44  fof(f6,plain,(
% 0.20/0.44    ? [X0,X1,X2] : (~r1_setfam_1(X0,X2) & (r1_setfam_1(X1,X2) & r1_setfam_1(X0,X1)))),
% 0.20/0.44    inference(ennf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,negated_conjecture,(
% 0.20/0.44    ~! [X0,X1,X2] : ((r1_setfam_1(X1,X2) & r1_setfam_1(X0,X1)) => r1_setfam_1(X0,X2))),
% 0.20/0.44    inference(negated_conjecture,[],[f4])).
% 0.20/0.44  fof(f4,conjecture,(
% 0.20/0.44    ! [X0,X1,X2] : ((r1_setfam_1(X1,X2) & r1_setfam_1(X0,X1)) => r1_setfam_1(X0,X2))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_setfam_1)).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    r1_setfam_1(sK0,sK1)),
% 0.20/0.44    inference(cnf_transformation,[],[f12])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    ~r1_setfam_1(sK0,sK2)),
% 0.20/0.44    inference(cnf_transformation,[],[f12])).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (15604)------------------------------
% 0.20/0.44  % (15604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (15604)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (15604)Memory used [KB]: 6268
% 0.20/0.44  % (15604)Time elapsed: 0.008 s
% 0.20/0.44  % (15604)------------------------------
% 0.20/0.44  % (15604)------------------------------
% 0.20/0.45  % (15599)Success in time 0.082 s
%------------------------------------------------------------------------------
