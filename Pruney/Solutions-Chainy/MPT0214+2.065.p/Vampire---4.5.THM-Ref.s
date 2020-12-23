%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:07 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   30 (  46 expanded)
%              Number of leaves         :    6 (  13 expanded)
%              Depth                    :   10
%              Number of atoms          :   94 ( 153 expanded)
%              Number of equality atoms :   46 (  82 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f36,plain,(
    $false ),
    inference(subsumption_resolution,[],[f34,f16])).

fof(f16,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( sK0 != sK1
    & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f9])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & r1_tarski(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f34,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f33,f29])).

fof(f29,plain,(
    ! [X3] : r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f18,f21])).

fof(f21,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_enumset1)).

fof(f18,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f13])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
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
    inference(rectify,[],[f11])).

fof(f11,plain,(
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

fof(f33,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
      | sK1 = X0 ) ),
    inference(resolution,[],[f23,f32])).

fof(f32,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(X3,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | ~ r2_hidden(X2,X3)
      | X1 = X2 ) ),
    inference(resolution,[],[f30,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f30,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f17,f21])).

fof(f17,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f23,plain,(
    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f15,f21,f21])).

fof(f15,plain,(
    r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n005.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 18:50:47 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.19/0.45  % (32462)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.45  % (32462)Refutation found. Thanks to Tanya!
% 0.19/0.45  % SZS status Theorem for theBenchmark
% 0.19/0.45  % SZS output start Proof for theBenchmark
% 0.19/0.45  fof(f36,plain,(
% 0.19/0.45    $false),
% 0.19/0.45    inference(subsumption_resolution,[],[f34,f16])).
% 0.19/0.45  fof(f16,plain,(
% 0.19/0.45    sK0 != sK1),
% 0.19/0.45    inference(cnf_transformation,[],[f10])).
% 0.19/0.45  fof(f10,plain,(
% 0.19/0.45    sK0 != sK1 & r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 0.19/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f9])).
% 0.19/0.45  fof(f9,plain,(
% 0.19/0.45    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.19/0.45    introduced(choice_axiom,[])).
% 0.19/0.45  fof(f7,plain,(
% 0.19/0.45    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.19/0.45    inference(ennf_transformation,[],[f5])).
% 0.19/0.45  fof(f5,negated_conjecture,(
% 0.19/0.45    ~! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.19/0.45    inference(negated_conjecture,[],[f4])).
% 0.19/0.45  fof(f4,conjecture,(
% 0.19/0.45    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 0.19/0.45  fof(f34,plain,(
% 0.19/0.45    sK0 = sK1),
% 0.19/0.45    inference(resolution,[],[f33,f29])).
% 0.19/0.45  fof(f29,plain,(
% 0.19/0.45    ( ! [X3] : (r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) )),
% 0.19/0.45    inference(equality_resolution,[],[f28])).
% 0.19/0.45  fof(f28,plain,(
% 0.19/0.45    ( ! [X3,X1] : (r2_hidden(X3,X1) | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 0.19/0.45    inference(equality_resolution,[],[f26])).
% 0.19/0.45  fof(f26,plain,(
% 0.19/0.45    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 0.19/0.45    inference(definition_unfolding,[],[f18,f21])).
% 0.19/0.45  fof(f21,plain,(
% 0.19/0.45    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f3])).
% 0.19/0.45  fof(f3,axiom,(
% 0.19/0.45    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_enumset1)).
% 0.19/0.45  fof(f18,plain,(
% 0.19/0.45    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.19/0.45    inference(cnf_transformation,[],[f14])).
% 0.19/0.45  fof(f14,plain,(
% 0.19/0.45    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.19/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f13])).
% 0.19/0.45  fof(f13,plain,(
% 0.19/0.45    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 0.19/0.45    introduced(choice_axiom,[])).
% 0.19/0.45  fof(f12,plain,(
% 0.19/0.45    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.19/0.45    inference(rectify,[],[f11])).
% 0.19/0.45  fof(f11,plain,(
% 0.19/0.45    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.19/0.45    inference(nnf_transformation,[],[f2])).
% 0.19/0.45  fof(f2,axiom,(
% 0.19/0.45    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.19/0.45  fof(f33,plain,(
% 0.19/0.45    ( ! [X0] : (~r2_hidden(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | sK1 = X0) )),
% 0.19/0.45    inference(resolution,[],[f23,f32])).
% 0.19/0.46  fof(f32,plain,(
% 0.19/0.46    ( ! [X2,X3,X1] : (~r1_tarski(X3,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | ~r2_hidden(X2,X3) | X1 = X2) )),
% 0.19/0.46    inference(resolution,[],[f30,f22])).
% 0.19/0.47  fof(f22,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f8])).
% 0.19/0.47  fof(f8,plain,(
% 0.19/0.47    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.19/0.47    inference(ennf_transformation,[],[f6])).
% 0.19/0.47  fof(f6,plain,(
% 0.19/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.19/0.47    inference(unused_predicate_definition_removal,[],[f1])).
% 0.19/0.47  fof(f1,axiom,(
% 0.19/0.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.19/0.47  fof(f30,plain,(
% 0.19/0.47    ( ! [X0,X3] : (~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | X0 = X3) )),
% 0.19/0.47    inference(equality_resolution,[],[f27])).
% 0.19/0.47  fof(f27,plain,(
% 0.19/0.47    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 0.19/0.47    inference(definition_unfolding,[],[f17,f21])).
% 0.19/0.47  fof(f17,plain,(
% 0.19/0.47    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.19/0.47    inference(cnf_transformation,[],[f14])).
% 0.19/0.47  fof(f23,plain,(
% 0.19/0.47    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.19/0.47    inference(definition_unfolding,[],[f15,f21,f21])).
% 0.19/0.47  fof(f15,plain,(
% 0.19/0.47    r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 0.19/0.47    inference(cnf_transformation,[],[f10])).
% 0.19/0.47  % SZS output end Proof for theBenchmark
% 0.19/0.47  % (32462)------------------------------
% 0.19/0.47  % (32462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (32462)Termination reason: Refutation
% 0.19/0.47  
% 0.19/0.47  % (32462)Memory used [KB]: 6140
% 0.19/0.47  % (32462)Time elapsed: 0.077 s
% 0.19/0.47  % (32462)------------------------------
% 0.19/0.47  % (32462)------------------------------
% 0.19/0.47  % (32456)Success in time 0.133 s
%------------------------------------------------------------------------------
