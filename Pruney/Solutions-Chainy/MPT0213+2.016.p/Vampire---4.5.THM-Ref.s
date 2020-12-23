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
% DateTime   : Thu Dec  3 12:34:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  39 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :    9
%              Number of atoms          :  104 ( 131 expanded)
%              Number of equality atoms :   16 (  18 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f49,plain,(
    $false ),
    inference(global_subsumption,[],[f18,f47])).

fof(f47,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(resolution,[],[f43,f37])).

fof(f37,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(global_subsumption,[],[f19,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f22,f20])).

fof(f20,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).

fof(f10,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f19,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f43,plain,(
    ! [X6] :
      ( r2_hidden(sK1(k1_xboole_0,X6),X6)
      | k3_tarski(k1_xboole_0) = X6 ) ),
    inference(resolution,[],[f27,f37])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k3_tarski(X0) = X1
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK1(X0,X1),X3) )
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( ( r2_hidden(sK2(X0,X1),X0)
              & r2_hidden(sK1(X0,X1),sK2(X0,X1)) )
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK3(X0,X5),X0)
                & r2_hidden(X5,sK3(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f16,f15,f14])).

fof(f14,plain,(
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
              | ~ r2_hidden(sK1(X0,X1),X3) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK1(X0,X1),X4) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK1(X0,X1),X4) )
     => ( r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(sK1(X0,X1),sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK3(X0,X5),X0)
        & r2_hidden(X5,sK3(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f12,plain,(
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

fof(f18,plain,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(flattening,[],[f6])).

fof(f6,negated_conjecture,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:50:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (12981)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  % (12979)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (12980)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.51  % (12987)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.52  % (12979)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(global_subsumption,[],[f18,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.52    inference(resolution,[],[f43,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 0.21/0.52    inference(global_subsumption,[],[f19,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(superposition,[],[f22,f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(rectify,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X6] : (r2_hidden(sK1(k1_xboole_0,X6),X6) | k3_tarski(k1_xboole_0) = X6) )),
% 0.21/0.52    inference(resolution,[],[f27,f37])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k3_tarski(X0) = X1 | r2_hidden(sK1(X0,X1),X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & ((r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),sK2(X0,X1))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f16,f15,f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK1(X0,X1),X4)) | r2_hidden(sK1(X0,X1),X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK1(X0,X1),X4)) => (r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),sK2(X0,X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 0.21/0.52    inference(rectify,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    k1_xboole_0 != k3_tarski(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,plain,(
% 0.21/0.52    k1_xboole_0 != k3_tarski(k1_xboole_0)),
% 0.21/0.52    inference(flattening,[],[f6])).
% 0.21/0.52  fof(f6,negated_conjecture,(
% 0.21/0.52    ~k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.52    inference(negated_conjecture,[],[f5])).
% 0.21/0.52  fof(f5,conjecture,(
% 0.21/0.52    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (12979)------------------------------
% 0.21/0.52  % (12979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12979)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (12979)Memory used [KB]: 10618
% 0.21/0.52  % (12979)Time elapsed: 0.071 s
% 0.21/0.52  % (12979)------------------------------
% 0.21/0.52  % (12979)------------------------------
% 0.21/0.52  % (12988)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.52  % (12988)Refutation not found, incomplete strategy% (12988)------------------------------
% 0.21/0.52  % (12988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12989)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.52  % (12988)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (12988)Memory used [KB]: 6012
% 0.21/0.52  % (12988)Time elapsed: 0.080 s
% 0.21/0.52  % (12988)------------------------------
% 0.21/0.52  % (12988)------------------------------
% 0.21/0.53  % (12972)Success in time 0.164 s
%------------------------------------------------------------------------------
