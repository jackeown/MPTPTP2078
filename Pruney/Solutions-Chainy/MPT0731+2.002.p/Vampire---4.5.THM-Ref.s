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
% DateTime   : Thu Dec  3 12:55:14 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   32 (  32 expanded)
%              Number of leaves         :    9 (   9 expanded)
%              Depth                    :    9
%              Number of atoms          :  105 ( 105 expanded)
%              Number of equality atoms :   69 (  69 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f53,plain,(
    $false ),
    inference(subsumption_resolution,[],[f50,f40])).

fof(f40,plain,(
    ! [X0,X1] : ~ r1_tarski(k2_tarski(X0,X1),X1) ),
    inference(unit_resulting_resolution,[],[f33,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f33,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK1(X0,X1,X2) != X1
              & sK1(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( sK1(X0,X1,X2) = X1
            | sK1(X0,X1,X2) = X0
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f16])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK1(X0,X1,X2) != X1
            & sK1(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( sK1(X0,X1,X2) = X1
          | sK1(X0,X1,X2) = X0
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f50,plain,(
    r1_tarski(k2_tarski(sK0,sK0),sK0) ),
    inference(superposition,[],[f43,f31])).

fof(f31,plain,(
    sK0 = k2_xboole_0(sK0,k2_tarski(sK0,sK0)) ),
    inference(definition_unfolding,[],[f18,f30])).

fof(f30,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k2_tarski(X0,X0)) ),
    inference(definition_unfolding,[],[f20,f19])).

fof(f19,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f18,plain,(
    sK0 = k1_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    sK0 = k1_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f11])).

fof(f11,plain,
    ( ? [X0] : k1_ordinal1(X0) = X0
   => sK0 = k1_ordinal1(sK0) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] : k1_ordinal1(X0) = X0 ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] : k1_ordinal1(X0) != X0 ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_ordinal1)).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f21,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.31  % Computer   : n001.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 12:53:14 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.17/0.47  % (30615)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.17/0.47  % (30611)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.17/0.48  % (30621)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.17/0.48  % (30615)Refutation found. Thanks to Tanya!
% 0.17/0.48  % SZS status Theorem for theBenchmark
% 0.17/0.48  % SZS output start Proof for theBenchmark
% 0.17/0.48  fof(f53,plain,(
% 0.17/0.48    $false),
% 0.17/0.48    inference(subsumption_resolution,[],[f50,f40])).
% 0.17/0.48  fof(f40,plain,(
% 0.17/0.48    ( ! [X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X1)) )),
% 0.17/0.48    inference(unit_resulting_resolution,[],[f33,f23])).
% 0.17/0.48  fof(f23,plain,(
% 0.17/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.17/0.48    inference(cnf_transformation,[],[f10])).
% 0.17/0.48  fof(f10,plain,(
% 0.17/0.48    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.17/0.48    inference(ennf_transformation,[],[f6])).
% 0.17/0.48  fof(f6,axiom,(
% 0.17/0.48    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.17/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.17/0.48  fof(f33,plain,(
% 0.17/0.48    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 0.17/0.48    inference(equality_resolution,[],[f32])).
% 0.17/0.48  fof(f32,plain,(
% 0.17/0.48    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 0.17/0.48    inference(equality_resolution,[],[f26])).
% 0.17/0.48  fof(f26,plain,(
% 0.17/0.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.17/0.48    inference(cnf_transformation,[],[f17])).
% 0.17/0.48  fof(f17,plain,(
% 0.17/0.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.17/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f16])).
% 0.17/0.48  fof(f16,plain,(
% 0.17/0.48    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 0.17/0.48    introduced(choice_axiom,[])).
% 0.17/0.48  fof(f15,plain,(
% 0.17/0.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.17/0.48    inference(rectify,[],[f14])).
% 0.17/0.48  fof(f14,plain,(
% 0.17/0.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.17/0.48    inference(flattening,[],[f13])).
% 0.17/0.48  fof(f13,plain,(
% 0.17/0.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.17/0.48    inference(nnf_transformation,[],[f3])).
% 0.17/0.48  fof(f3,axiom,(
% 0.17/0.48    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.17/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.17/0.48  fof(f50,plain,(
% 0.17/0.48    r1_tarski(k2_tarski(sK0,sK0),sK0)),
% 0.17/0.48    inference(superposition,[],[f43,f31])).
% 0.17/0.48  fof(f31,plain,(
% 0.17/0.48    sK0 = k2_xboole_0(sK0,k2_tarski(sK0,sK0))),
% 0.17/0.48    inference(definition_unfolding,[],[f18,f30])).
% 0.17/0.48  fof(f30,plain,(
% 0.17/0.48    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k2_tarski(X0,X0))) )),
% 0.17/0.48    inference(definition_unfolding,[],[f20,f19])).
% 0.17/0.48  fof(f19,plain,(
% 0.17/0.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.17/0.48    inference(cnf_transformation,[],[f4])).
% 0.17/0.48  fof(f4,axiom,(
% 0.17/0.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.17/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.17/0.48  fof(f20,plain,(
% 0.17/0.48    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.17/0.48    inference(cnf_transformation,[],[f5])).
% 0.17/0.48  fof(f5,axiom,(
% 0.17/0.48    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.17/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.17/0.48  fof(f18,plain,(
% 0.17/0.48    sK0 = k1_ordinal1(sK0)),
% 0.17/0.48    inference(cnf_transformation,[],[f12])).
% 0.17/0.48  fof(f12,plain,(
% 0.17/0.48    sK0 = k1_ordinal1(sK0)),
% 0.17/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f11])).
% 0.17/0.48  fof(f11,plain,(
% 0.17/0.48    ? [X0] : k1_ordinal1(X0) = X0 => sK0 = k1_ordinal1(sK0)),
% 0.17/0.48    introduced(choice_axiom,[])).
% 0.17/0.48  fof(f9,plain,(
% 0.17/0.48    ? [X0] : k1_ordinal1(X0) = X0),
% 0.17/0.48    inference(ennf_transformation,[],[f8])).
% 0.17/0.48  fof(f8,negated_conjecture,(
% 0.17/0.48    ~! [X0] : k1_ordinal1(X0) != X0),
% 0.17/0.48    inference(negated_conjecture,[],[f7])).
% 0.17/0.48  fof(f7,conjecture,(
% 0.17/0.48    ! [X0] : k1_ordinal1(X0) != X0),
% 0.17/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_ordinal1)).
% 0.17/0.48  fof(f43,plain,(
% 0.17/0.48    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 0.17/0.48    inference(superposition,[],[f21,f22])).
% 0.17/0.48  fof(f22,plain,(
% 0.17/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.17/0.48    inference(cnf_transformation,[],[f1])).
% 0.17/0.48  fof(f1,axiom,(
% 0.17/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.17/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.17/0.48  fof(f21,plain,(
% 0.17/0.48    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.17/0.48    inference(cnf_transformation,[],[f2])).
% 0.17/0.48  fof(f2,axiom,(
% 0.17/0.48    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.17/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.17/0.48  % SZS output end Proof for theBenchmark
% 0.17/0.48  % (30615)------------------------------
% 0.17/0.48  % (30615)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.48  % (30615)Termination reason: Refutation
% 0.17/0.48  
% 0.17/0.48  % (30615)Memory used [KB]: 1663
% 0.17/0.48  % (30615)Time elapsed: 0.093 s
% 0.17/0.48  % (30615)------------------------------
% 0.17/0.48  % (30615)------------------------------
% 0.17/0.48  % (30610)Success in time 0.153 s
%------------------------------------------------------------------------------
