%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:55 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 271 expanded)
%              Number of leaves         :   13 (  87 expanded)
%              Depth                    :   18
%              Number of atoms          :  175 ( 966 expanded)
%              Number of equality atoms :   93 ( 497 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f301,plain,(
    $false ),
    inference(subsumption_resolution,[],[f298,f296])).

fof(f296,plain,(
    ! [X6,X7] : k2_enumset1(X6,X6,X6,X6) = k1_relat_1(k2_enumset1(k4_tarski(X6,X7),k4_tarski(X6,X7),k4_tarski(X6,X7),k4_tarski(X6,X7))) ),
    inference(resolution,[],[f276,f48])).

fof(f48,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f33,f39])).

fof(f39,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f24,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f25,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f25,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f24,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f276,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),k2_enumset1(X0,X0,X0,X0))
      | k2_enumset1(X1,X1,X1,X1) = k1_relat_1(k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(resolution,[],[f275,f45])).

fof(f45,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f14,f17,f16,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f275,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_relat_1(k2_enumset1(X5,X5,X5,X5)))
      | k1_relat_1(k2_enumset1(X5,X5,X5,X5)) = k2_enumset1(X4,X4,X4,X4) ) ),
    inference(subsumption_resolution,[],[f273,f57])).

fof(f57,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_relat_1(k2_enumset1(X5,X5,X5,X5)))
      | k1_mcart_1(X5) = X4 ) ),
    inference(superposition,[],[f26,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_tarski(X0,sK5(k2_enumset1(X1,X1,X1,X1),X0)) = X1
      | ~ r2_hidden(X0,k1_relat_1(k2_enumset1(X1,X1,X1,X1))) ) ),
    inference(resolution,[],[f46,f49])).

fof(f49,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f32,f39])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f26,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f273,plain,(
    ! [X4,X5] :
      ( k1_relat_1(k2_enumset1(X5,X5,X5,X5)) = k2_enumset1(X4,X4,X4,X4)
      | ~ r2_hidden(X4,k1_relat_1(k2_enumset1(X5,X5,X5,X5)))
      | k1_mcart_1(X5) != X4 ) ),
    inference(trivial_inequality_removal,[],[f272])).

fof(f272,plain,(
    ! [X4,X5] :
      ( X4 != X4
      | k1_relat_1(k2_enumset1(X5,X5,X5,X5)) = k2_enumset1(X4,X4,X4,X4)
      | ~ r2_hidden(X4,k1_relat_1(k2_enumset1(X5,X5,X5,X5)))
      | k1_mcart_1(X5) != X4 ) ),
    inference(duplicate_literal_removal,[],[f271])).

fof(f271,plain,(
    ! [X4,X5] :
      ( X4 != X4
      | k1_relat_1(k2_enumset1(X5,X5,X5,X5)) = k2_enumset1(X4,X4,X4,X4)
      | ~ r2_hidden(X4,k1_relat_1(k2_enumset1(X5,X5,X5,X5)))
      | k1_mcart_1(X5) != X4
      | k1_relat_1(k2_enumset1(X5,X5,X5,X5)) = k2_enumset1(X4,X4,X4,X4) ) ),
    inference(superposition,[],[f41,f239])).

fof(f239,plain,(
    ! [X0,X1] :
      ( sK6(X0,k1_relat_1(k2_enumset1(X1,X1,X1,X1))) = X0
      | k1_mcart_1(X1) != X0
      | k2_enumset1(X0,X0,X0,X0) = k1_relat_1(k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(equality_factoring,[],[f62])).

fof(f62,plain,(
    ! [X8,X7] :
      ( k1_mcart_1(X7) = sK6(X8,k1_relat_1(k2_enumset1(X7,X7,X7,X7)))
      | sK6(X8,k1_relat_1(k2_enumset1(X7,X7,X7,X7))) = X8
      | k1_relat_1(k2_enumset1(X7,X7,X7,X7)) = k2_enumset1(X8,X8,X8,X8) ) ),
    inference(resolution,[],[f57,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | sK6(X0,X1) = X0
      | k2_enumset1(X0,X0,X0,X0) = X1 ) ),
    inference(definition_unfolding,[],[f34,f39])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK6(X0,X1) = X0
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X0,X1] :
      ( sK6(X0,X1) != X0
      | k2_enumset1(X0,X0,X0,X0) = X1
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f35,f39])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK6(X0,X1) != X0
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f298,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) ),
    inference(backward_demodulation,[],[f40,f296])).

fof(f40,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2)))) ),
    inference(definition_unfolding,[],[f23,f39,f39,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f23,plain,(
    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))
   => k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:14:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (27481)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.51  % (27504)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (27496)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.52  % (27482)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (27496)Refutation not found, incomplete strategy% (27496)------------------------------
% 0.22/0.52  % (27496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (27496)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (27496)Memory used [KB]: 1663
% 0.22/0.52  % (27496)Time elapsed: 0.111 s
% 0.22/0.52  % (27496)------------------------------
% 0.22/0.52  % (27496)------------------------------
% 0.22/0.52  % (27480)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (27484)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (27504)Refutation not found, incomplete strategy% (27504)------------------------------
% 0.22/0.52  % (27504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (27504)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (27504)Memory used [KB]: 6140
% 0.22/0.52  % (27504)Time elapsed: 0.119 s
% 0.22/0.52  % (27504)------------------------------
% 0.22/0.52  % (27504)------------------------------
% 0.22/0.53  % (27483)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (27485)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (27498)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.53  % (27501)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.53  % (27505)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (27505)Refutation not found, incomplete strategy% (27505)------------------------------
% 0.22/0.54  % (27505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (27505)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (27505)Memory used [KB]: 6140
% 0.22/0.54  % (27505)Time elapsed: 0.131 s
% 0.22/0.54  % (27505)------------------------------
% 0.22/0.54  % (27505)------------------------------
% 0.22/0.54  % (27503)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (27507)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (27502)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (27502)Refutation not found, incomplete strategy% (27502)------------------------------
% 0.22/0.54  % (27502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (27502)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (27502)Memory used [KB]: 10618
% 0.22/0.54  % (27502)Time elapsed: 0.129 s
% 0.22/0.54  % (27502)------------------------------
% 0.22/0.54  % (27502)------------------------------
% 0.22/0.54  % (27479)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (27478)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (27506)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (27493)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (27488)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.54  % (27500)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (27489)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (27499)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (27489)Refutation not found, incomplete strategy% (27489)------------------------------
% 0.22/0.54  % (27489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (27489)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (27489)Memory used [KB]: 6140
% 0.22/0.54  % (27489)Time elapsed: 0.139 s
% 0.22/0.54  % (27489)------------------------------
% 0.22/0.54  % (27489)------------------------------
% 0.22/0.54  % (27479)Refutation not found, incomplete strategy% (27479)------------------------------
% 0.22/0.54  % (27479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (27479)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (27479)Memory used [KB]: 1663
% 0.22/0.54  % (27479)Time elapsed: 0.135 s
% 0.22/0.54  % (27479)------------------------------
% 0.22/0.54  % (27479)------------------------------
% 0.22/0.54  % (27497)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (27490)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (27494)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (27491)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.55  % (27486)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (27495)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (27494)Refutation not found, incomplete strategy% (27494)------------------------------
% 0.22/0.55  % (27494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (27487)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (27503)Refutation not found, incomplete strategy% (27503)------------------------------
% 0.22/0.55  % (27503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (27503)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (27503)Memory used [KB]: 6140
% 0.22/0.55  % (27503)Time elapsed: 0.139 s
% 0.22/0.55  % (27503)------------------------------
% 0.22/0.55  % (27503)------------------------------
% 1.48/0.55  % (27492)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.48/0.56  % (27494)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (27494)Memory used [KB]: 10618
% 1.48/0.56  % (27494)Time elapsed: 0.141 s
% 1.48/0.56  % (27494)------------------------------
% 1.48/0.56  % (27494)------------------------------
% 1.48/0.56  % (27492)Refutation not found, incomplete strategy% (27492)------------------------------
% 1.48/0.56  % (27492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (27492)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (27492)Memory used [KB]: 1663
% 1.48/0.56  % (27492)Time elapsed: 0.150 s
% 1.48/0.56  % (27492)------------------------------
% 1.48/0.56  % (27492)------------------------------
% 1.48/0.56  % (27507)Refutation not found, incomplete strategy% (27507)------------------------------
% 1.48/0.56  % (27507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (27507)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (27507)Memory used [KB]: 1663
% 1.48/0.56  % (27507)Time elapsed: 0.149 s
% 1.48/0.56  % (27507)------------------------------
% 1.48/0.56  % (27507)------------------------------
% 1.64/0.57  % (27495)Refutation not found, incomplete strategy% (27495)------------------------------
% 1.64/0.57  % (27495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.57  % (27495)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.57  
% 1.64/0.57  % (27495)Memory used [KB]: 1663
% 1.64/0.57  % (27495)Time elapsed: 0.159 s
% 1.64/0.57  % (27495)------------------------------
% 1.64/0.57  % (27495)------------------------------
% 1.64/0.60  % (27500)Refutation found. Thanks to Tanya!
% 1.64/0.60  % SZS status Theorem for theBenchmark
% 1.64/0.60  % SZS output start Proof for theBenchmark
% 1.64/0.60  fof(f301,plain,(
% 1.64/0.60    $false),
% 1.64/0.60    inference(subsumption_resolution,[],[f298,f296])).
% 1.64/0.60  fof(f296,plain,(
% 1.64/0.60    ( ! [X6,X7] : (k2_enumset1(X6,X6,X6,X6) = k1_relat_1(k2_enumset1(k4_tarski(X6,X7),k4_tarski(X6,X7),k4_tarski(X6,X7),k4_tarski(X6,X7)))) )),
% 1.64/0.60    inference(resolution,[],[f276,f48])).
% 1.64/0.60  fof(f48,plain,(
% 1.64/0.60    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 1.64/0.60    inference(equality_resolution,[],[f47])).
% 1.64/0.60  fof(f47,plain,(
% 1.64/0.60    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 1.64/0.60    inference(equality_resolution,[],[f43])).
% 1.64/0.60  fof(f43,plain,(
% 1.64/0.60    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.64/0.60    inference(definition_unfolding,[],[f33,f39])).
% 1.64/0.60  fof(f39,plain,(
% 1.64/0.60    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.64/0.60    inference(definition_unfolding,[],[f24,f38])).
% 1.64/0.60  fof(f38,plain,(
% 1.64/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.64/0.60    inference(definition_unfolding,[],[f25,f37])).
% 1.64/0.60  fof(f37,plain,(
% 1.64/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.64/0.60    inference(cnf_transformation,[],[f4])).
% 1.64/0.60  fof(f4,axiom,(
% 1.64/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.64/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.64/0.60  fof(f25,plain,(
% 1.64/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.64/0.60    inference(cnf_transformation,[],[f3])).
% 1.64/0.60  fof(f3,axiom,(
% 1.64/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.64/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.64/0.60  fof(f24,plain,(
% 1.64/0.60    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.64/0.60    inference(cnf_transformation,[],[f2])).
% 1.64/0.60  fof(f2,axiom,(
% 1.64/0.60    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.64/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.64/0.60  fof(f33,plain,(
% 1.64/0.60    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.64/0.60    inference(cnf_transformation,[],[f22])).
% 1.64/0.60  fof(f22,plain,(
% 1.64/0.60    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.64/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f21])).
% 1.64/0.60  fof(f21,plain,(
% 1.64/0.60    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1))))),
% 1.64/0.60    introduced(choice_axiom,[])).
% 1.64/0.60  fof(f20,plain,(
% 1.64/0.60    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.64/0.60    inference(rectify,[],[f19])).
% 1.64/0.60  fof(f19,plain,(
% 1.64/0.60    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.64/0.60    inference(nnf_transformation,[],[f1])).
% 1.64/0.60  fof(f1,axiom,(
% 1.64/0.60    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.64/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.64/0.60  fof(f276,plain,(
% 1.64/0.60    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X1,X2),k2_enumset1(X0,X0,X0,X0)) | k2_enumset1(X1,X1,X1,X1) = k1_relat_1(k2_enumset1(X0,X0,X0,X0))) )),
% 1.64/0.60    inference(resolution,[],[f275,f45])).
% 1.64/0.60  fof(f45,plain,(
% 1.64/0.60    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 1.64/0.60    inference(equality_resolution,[],[f29])).
% 1.64/0.60  fof(f29,plain,(
% 1.64/0.60    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 1.64/0.60    inference(cnf_transformation,[],[f18])).
% 1.64/0.60  fof(f18,plain,(
% 1.64/0.60    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.64/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f14,f17,f16,f15])).
% 1.64/0.60  fof(f15,plain,(
% 1.64/0.60    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.64/0.60    introduced(choice_axiom,[])).
% 1.64/0.60  fof(f16,plain,(
% 1.64/0.60    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0))),
% 1.64/0.60    introduced(choice_axiom,[])).
% 1.64/0.60  fof(f17,plain,(
% 1.64/0.60    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0))),
% 1.64/0.60    introduced(choice_axiom,[])).
% 1.64/0.60  fof(f14,plain,(
% 1.64/0.60    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.64/0.60    inference(rectify,[],[f13])).
% 1.64/0.60  fof(f13,plain,(
% 1.64/0.60    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 1.64/0.60    inference(nnf_transformation,[],[f5])).
% 1.64/0.60  fof(f5,axiom,(
% 1.64/0.60    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.64/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 1.64/0.60  fof(f275,plain,(
% 1.64/0.60    ( ! [X4,X5] : (~r2_hidden(X4,k1_relat_1(k2_enumset1(X5,X5,X5,X5))) | k1_relat_1(k2_enumset1(X5,X5,X5,X5)) = k2_enumset1(X4,X4,X4,X4)) )),
% 1.64/0.60    inference(subsumption_resolution,[],[f273,f57])).
% 1.64/0.60  fof(f57,plain,(
% 1.64/0.60    ( ! [X4,X5] : (~r2_hidden(X4,k1_relat_1(k2_enumset1(X5,X5,X5,X5))) | k1_mcart_1(X5) = X4) )),
% 1.64/0.60    inference(superposition,[],[f26,f51])).
% 1.64/0.60  fof(f51,plain,(
% 1.64/0.60    ( ! [X0,X1] : (k4_tarski(X0,sK5(k2_enumset1(X1,X1,X1,X1),X0)) = X1 | ~r2_hidden(X0,k1_relat_1(k2_enumset1(X1,X1,X1,X1)))) )),
% 1.64/0.60    inference(resolution,[],[f46,f49])).
% 1.64/0.60  fof(f49,plain,(
% 1.64/0.60    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 1.64/0.60    inference(equality_resolution,[],[f44])).
% 1.64/0.60  fof(f44,plain,(
% 1.64/0.60    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.64/0.60    inference(definition_unfolding,[],[f32,f39])).
% 1.64/0.60  fof(f32,plain,(
% 1.64/0.60    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.64/0.60    inference(cnf_transformation,[],[f22])).
% 1.64/0.60  fof(f46,plain,(
% 1.64/0.60    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 1.64/0.60    inference(equality_resolution,[],[f28])).
% 1.64/0.60  fof(f28,plain,(
% 1.64/0.60    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 1.64/0.60    inference(cnf_transformation,[],[f18])).
% 1.64/0.60  fof(f26,plain,(
% 1.64/0.60    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 1.64/0.60    inference(cnf_transformation,[],[f7])).
% 1.64/0.60  fof(f7,axiom,(
% 1.64/0.60    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.64/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.64/0.60  fof(f273,plain,(
% 1.64/0.60    ( ! [X4,X5] : (k1_relat_1(k2_enumset1(X5,X5,X5,X5)) = k2_enumset1(X4,X4,X4,X4) | ~r2_hidden(X4,k1_relat_1(k2_enumset1(X5,X5,X5,X5))) | k1_mcart_1(X5) != X4) )),
% 1.64/0.60    inference(trivial_inequality_removal,[],[f272])).
% 1.64/0.60  fof(f272,plain,(
% 1.64/0.60    ( ! [X4,X5] : (X4 != X4 | k1_relat_1(k2_enumset1(X5,X5,X5,X5)) = k2_enumset1(X4,X4,X4,X4) | ~r2_hidden(X4,k1_relat_1(k2_enumset1(X5,X5,X5,X5))) | k1_mcart_1(X5) != X4) )),
% 1.64/0.60    inference(duplicate_literal_removal,[],[f271])).
% 1.64/0.60  fof(f271,plain,(
% 1.64/0.60    ( ! [X4,X5] : (X4 != X4 | k1_relat_1(k2_enumset1(X5,X5,X5,X5)) = k2_enumset1(X4,X4,X4,X4) | ~r2_hidden(X4,k1_relat_1(k2_enumset1(X5,X5,X5,X5))) | k1_mcart_1(X5) != X4 | k1_relat_1(k2_enumset1(X5,X5,X5,X5)) = k2_enumset1(X4,X4,X4,X4)) )),
% 1.64/0.60    inference(superposition,[],[f41,f239])).
% 1.64/0.60  fof(f239,plain,(
% 1.64/0.60    ( ! [X0,X1] : (sK6(X0,k1_relat_1(k2_enumset1(X1,X1,X1,X1))) = X0 | k1_mcart_1(X1) != X0 | k2_enumset1(X0,X0,X0,X0) = k1_relat_1(k2_enumset1(X1,X1,X1,X1))) )),
% 1.64/0.60    inference(equality_factoring,[],[f62])).
% 1.64/0.60  fof(f62,plain,(
% 1.64/0.60    ( ! [X8,X7] : (k1_mcart_1(X7) = sK6(X8,k1_relat_1(k2_enumset1(X7,X7,X7,X7))) | sK6(X8,k1_relat_1(k2_enumset1(X7,X7,X7,X7))) = X8 | k1_relat_1(k2_enumset1(X7,X7,X7,X7)) = k2_enumset1(X8,X8,X8,X8)) )),
% 1.64/0.60    inference(resolution,[],[f57,f42])).
% 1.64/0.60  fof(f42,plain,(
% 1.64/0.60    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X1) | sK6(X0,X1) = X0 | k2_enumset1(X0,X0,X0,X0) = X1) )),
% 1.64/0.60    inference(definition_unfolding,[],[f34,f39])).
% 1.64/0.60  fof(f34,plain,(
% 1.64/0.60    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1)) )),
% 1.64/0.60    inference(cnf_transformation,[],[f22])).
% 1.64/0.60  fof(f41,plain,(
% 1.64/0.60    ( ! [X0,X1] : (sK6(X0,X1) != X0 | k2_enumset1(X0,X0,X0,X0) = X1 | ~r2_hidden(sK6(X0,X1),X1)) )),
% 1.64/0.60    inference(definition_unfolding,[],[f35,f39])).
% 1.64/0.60  fof(f35,plain,(
% 1.64/0.60    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) )),
% 1.64/0.60    inference(cnf_transformation,[],[f22])).
% 1.64/0.60  fof(f298,plain,(
% 1.64/0.60    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))),
% 1.64/0.60    inference(backward_demodulation,[],[f40,f296])).
% 1.64/0.60  fof(f40,plain,(
% 1.64/0.60    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2))))),
% 1.64/0.60    inference(definition_unfolding,[],[f23,f39,f39,f36])).
% 1.64/0.60  fof(f36,plain,(
% 1.64/0.60    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.64/0.60    inference(cnf_transformation,[],[f6])).
% 1.64/0.60  fof(f6,axiom,(
% 1.64/0.60    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.64/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.64/0.60  fof(f23,plain,(
% 1.64/0.60    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2))))),
% 1.64/0.60    inference(cnf_transformation,[],[f12])).
% 1.64/0.60  fof(f12,plain,(
% 1.64/0.60    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2))))),
% 1.64/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).
% 1.64/0.60  fof(f11,plain,(
% 1.64/0.60    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) => k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2))))),
% 1.64/0.60    introduced(choice_axiom,[])).
% 1.64/0.60  fof(f10,plain,(
% 1.64/0.60    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 1.64/0.60    inference(ennf_transformation,[],[f9])).
% 1.64/0.60  fof(f9,negated_conjecture,(
% 1.64/0.60    ~! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 1.64/0.60    inference(negated_conjecture,[],[f8])).
% 1.64/0.60  fof(f8,conjecture,(
% 1.64/0.60    ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 1.64/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_mcart_1)).
% 1.64/0.60  % SZS output end Proof for theBenchmark
% 1.64/0.60  % (27500)------------------------------
% 1.64/0.60  % (27500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.60  % (27500)Termination reason: Refutation
% 1.64/0.60  
% 1.64/0.60  % (27500)Memory used [KB]: 6780
% 1.64/0.60  % (27500)Time elapsed: 0.165 s
% 1.64/0.60  % (27500)------------------------------
% 1.64/0.60  % (27500)------------------------------
% 1.64/0.61  % (27477)Success in time 0.236 s
%------------------------------------------------------------------------------
