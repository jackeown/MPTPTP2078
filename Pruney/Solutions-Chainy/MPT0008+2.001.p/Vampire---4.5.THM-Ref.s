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
% DateTime   : Thu Dec  3 12:29:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   25 (  56 expanded)
%              Number of leaves         :    4 (  14 expanded)
%              Depth                    :   12
%              Number of atoms          :   76 ( 205 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,plain,(
    $false ),
    inference(subsumption_resolution,[],[f35,f15])).

fof(f15,plain,(
    ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( ~ r1_tarski(sK0,sK2)
    & r1_tarski(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X2)
        & r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(sK0,sK2)
      & r1_tarski(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X2)
      & r1_tarski(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X2)
      & r1_tarski(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X1,X2)
          & r1_tarski(X0,X1) )
       => r1_tarski(X0,X2) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f35,plain,(
    r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f34,f13])).

fof(f13,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | r1_tarski(X0,sK2) ) ),
    inference(duplicate_literal_removal,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK2)
      | ~ r1_tarski(X0,sK1)
      | r1_tarski(X0,sK2) ) ),
    inference(resolution,[],[f26,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f11])).

fof(f11,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
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

fof(f26,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK3(X2,X3),sK2)
      | r1_tarski(X2,X3)
      | ~ r1_tarski(X2,sK1) ) ),
    inference(resolution,[],[f23,f14])).

fof(f14,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r1_tarski(X3,X5)
      | r1_tarski(X2,X4)
      | r2_hidden(sK3(X2,X4),X5)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f21,f16])).

fof(f16,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1),X2)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f16,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (17911)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.20/0.47  % (17908)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.20/0.47  % (17911)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(subsumption_resolution,[],[f35,f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ~r1_tarski(sK0,sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ~r1_tarski(sK0,sK2) & r1_tarski(sK1,sK2) & r1_tarski(sK0,sK1)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f7])).
% 0.20/0.47  fof(f7,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (~r1_tarski(X0,X2) & r1_tarski(X1,X2) & r1_tarski(X0,X1)) => (~r1_tarski(sK0,sK2) & r1_tarski(sK1,sK2) & r1_tarski(sK0,sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f5,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (~r1_tarski(X0,X2) & r1_tarski(X1,X2) & r1_tarski(X0,X1))),
% 0.20/0.47    inference(flattening,[],[f4])).
% 0.20/0.47  fof(f4,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (~r1_tarski(X0,X2) & (r1_tarski(X1,X2) & r1_tarski(X0,X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.47    inference(negated_conjecture,[],[f2])).
% 0.20/0.47  fof(f2,conjecture,(
% 0.20/0.47    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    r1_tarski(sK0,sK2)),
% 0.20/0.47    inference(resolution,[],[f34,f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    r1_tarski(sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(X0,sK1) | r1_tarski(X0,sK2)) )),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X0] : (r1_tarski(X0,sK2) | ~r1_tarski(X0,sK1) | r1_tarski(X0,sK2)) )),
% 0.20/0.47    inference(resolution,[],[f26,f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.47    inference(rectify,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.47    inference(nnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,plain,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ( ! [X2,X3] : (r2_hidden(sK3(X2,X3),sK2) | r1_tarski(X2,X3) | ~r1_tarski(X2,sK1)) )),
% 0.20/0.47    inference(resolution,[],[f23,f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    r1_tarski(sK1,sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ( ! [X4,X2,X5,X3] : (~r1_tarski(X3,X5) | r1_tarski(X2,X4) | r2_hidden(sK3(X2,X4),X5) | ~r1_tarski(X2,X3)) )),
% 0.20/0.47    inference(resolution,[],[f21,f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1),X2) | ~r1_tarski(X0,X2) | r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(resolution,[],[f16,f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (17911)------------------------------
% 0.20/0.47  % (17911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (17911)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (17911)Memory used [KB]: 5373
% 0.20/0.47  % (17911)Time elapsed: 0.052 s
% 0.20/0.47  % (17911)------------------------------
% 0.20/0.47  % (17911)------------------------------
% 0.20/0.47  % (17903)Success in time 0.114 s
%------------------------------------------------------------------------------
