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
% DateTime   : Thu Dec  3 12:58:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  68 expanded)
%              Number of leaves         :    7 (  19 expanded)
%              Depth                    :   12
%              Number of atoms          :  135 ( 254 expanded)
%              Number of equality atoms :   44 (  94 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f73,plain,(
    $false ),
    inference(subsumption_resolution,[],[f72,f37])).

fof(f37,plain,(
    r2_hidden(k1_mcart_1(sK2),sK3) ),
    inference(resolution,[],[f20,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f20,plain,(
    r2_hidden(sK2,k2_zfmisc_1(sK3,k2_tarski(sK4,sK5))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( ( sK5 != k2_mcart_1(sK2)
        & sK4 != k2_mcart_1(sK2) )
      | ~ r2_hidden(k1_mcart_1(sK2),sK3) )
    & r2_hidden(sK2,k2_zfmisc_1(sK3,k2_tarski(sK4,sK5))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f5,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ( k2_mcart_1(X0) != X3
            & k2_mcart_1(X0) != X2 )
          | ~ r2_hidden(k1_mcart_1(X0),X1) )
        & r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) )
   => ( ( ( sK5 != k2_mcart_1(sK2)
          & sK4 != k2_mcart_1(sK2) )
        | ~ r2_hidden(k1_mcart_1(sK2),sK3) )
      & r2_hidden(sK2,k2_zfmisc_1(sK3,k2_tarski(sK4,sK5))) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ( k2_mcart_1(X0) != X3
          & k2_mcart_1(X0) != X2 )
        | ~ r2_hidden(k1_mcart_1(X0),X1) )
      & r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
       => ( ( k2_mcart_1(X0) = X3
            | k2_mcart_1(X0) = X2 )
          & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
     => ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_mcart_1)).

fof(f72,plain,(
    ~ r2_hidden(k1_mcart_1(sK2),sK3) ),
    inference(trivial_inequality_removal,[],[f65])).

fof(f65,plain,
    ( sK4 != sK4
    | ~ r2_hidden(k1_mcart_1(sK2),sK3) ),
    inference(backward_demodulation,[],[f21,f64])).

fof(f64,plain,(
    sK4 = k2_mcart_1(sK2) ),
    inference(subsumption_resolution,[],[f60,f44])).

fof(f44,plain,(
    sK5 != k2_mcart_1(sK2) ),
    inference(subsumption_resolution,[],[f22,f37])).

fof(f22,plain,
    ( sK5 != k2_mcart_1(sK2)
    | ~ r2_hidden(k1_mcart_1(sK2),sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f60,plain,
    ( sK5 = k2_mcart_1(sK2)
    | sK4 = k2_mcart_1(sK2) ),
    inference(resolution,[],[f53,f36])).

fof(f36,plain,(
    ! [X0,X1] : sP1(X0,X1,k2_tarski(X0,X1)) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f1,f8,f7])).

fof(f7,plain,(
    ! [X3,X1,X0] :
      ( sP0(X3,X1,X0)
    <=> ( X1 = X3
        | X0 = X3 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X3,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1,k2_tarski(sK4,sK5))
      | k2_mcart_1(sK2) = X1
      | k2_mcart_1(sK2) = X0 ) ),
    inference(resolution,[],[f42,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( X0 = X1
      | X0 = X2
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( X0 != X1
          & X0 != X2 ) )
      & ( X0 = X1
        | X0 = X2
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X3,X1,X0] :
      ( ( sP0(X3,X1,X0)
        | ( X1 != X3
          & X0 != X3 ) )
      & ( X1 = X3
        | X0 = X3
        | ~ sP0(X3,X1,X0) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X3,X1,X0] :
      ( ( sP0(X3,X1,X0)
        | ( X1 != X3
          & X0 != X3 ) )
      & ( X1 = X3
        | X0 = X3
        | ~ sP0(X3,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X0,X1] :
      ( sP0(k2_mcart_1(sK2),X0,X1)
      | ~ sP1(X1,X0,k2_tarski(sK4,sK5)) ) ),
    inference(resolution,[],[f38,f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( sP0(X4,X1,X0)
      | ~ r2_hidden(X4,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(sK6(X0,X1,X2),X1,X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sP0(sK6(X0,X1,X2),X1,X0)
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X4,X1,X0) )
            & ( sP0(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f13,f14])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X3,X1,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X3,X1,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(sK6(X0,X1,X2),X1,X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sP0(sK6(X0,X1,X2),X1,X0)
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X4,X1,X0) )
            & ( sP0(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X3,X1,X0) )
            & ( sP0(X3,X1,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f38,plain,(
    r2_hidden(k2_mcart_1(sK2),k2_tarski(sK4,sK5)) ),
    inference(resolution,[],[f20,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f21,plain,
    ( sK4 != k2_mcart_1(sK2)
    | ~ r2_hidden(k1_mcart_1(sK2),sK3) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:31:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (16040)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (16037)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.50  % (16037)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (16045)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.50  % (16031)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f72,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    r2_hidden(k1_mcart_1(sK2),sK3)),
% 0.21/0.50    inference(resolution,[],[f20,f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    r2_hidden(sK2,k2_zfmisc_1(sK3,k2_tarski(sK4,sK5)))),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ((sK5 != k2_mcart_1(sK2) & sK4 != k2_mcart_1(sK2)) | ~r2_hidden(k1_mcart_1(sK2),sK3)) & r2_hidden(sK2,k2_zfmisc_1(sK3,k2_tarski(sK4,sK5)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f5,f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (((k2_mcart_1(X0) != X3 & k2_mcart_1(X0) != X2) | ~r2_hidden(k1_mcart_1(X0),X1)) & r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))) => (((sK5 != k2_mcart_1(sK2) & sK4 != k2_mcart_1(sK2)) | ~r2_hidden(k1_mcart_1(sK2),sK3)) & r2_hidden(sK2,k2_zfmisc_1(sK3,k2_tarski(sK4,sK5))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f5,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (((k2_mcart_1(X0) != X3 & k2_mcart_1(X0) != X2) | ~r2_hidden(k1_mcart_1(X0),X1)) & r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.50    inference(negated_conjecture,[],[f3])).
% 0.21/0.50  fof(f3,conjecture,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_mcart_1)).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ~r2_hidden(k1_mcart_1(sK2),sK3)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    sK4 != sK4 | ~r2_hidden(k1_mcart_1(sK2),sK3)),
% 0.21/0.50    inference(backward_demodulation,[],[f21,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    sK4 = k2_mcart_1(sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f60,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    sK5 != k2_mcart_1(sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f22,f37])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    sK5 != k2_mcart_1(sK2) | ~r2_hidden(k1_mcart_1(sK2),sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    sK5 = k2_mcart_1(sK2) | sK4 = k2_mcart_1(sK2)),
% 0.21/0.50    inference(resolution,[],[f53,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sP1(X0,X1,k2_tarski(X0,X1))) )),
% 0.21/0.50    inference(equality_resolution,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k2_tarski(X0,X1) != X2))),
% 0.21/0.50    inference(nnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 0.21/0.50    inference(definition_folding,[],[f1,f8,f7])).
% 0.21/0.50  fof(f7,plain,(
% 0.21/0.50    ! [X3,X1,X0] : (sP0(X3,X1,X0) <=> (X1 = X3 | X0 = X3))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X3,X1,X0)))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~sP1(X0,X1,k2_tarski(sK4,sK5)) | k2_mcart_1(sK2) = X1 | k2_mcart_1(sK2) = X0) )),
% 0.21/0.50    inference(resolution,[],[f42,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (X0 = X1 | X0 = X2 | ~sP0(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (X0 != X1 & X0 != X2)) & (X0 = X1 | X0 = X2 | ~sP0(X0,X1,X2)))),
% 0.21/0.50    inference(rectify,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X3,X1,X0] : ((sP0(X3,X1,X0) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~sP0(X3,X1,X0)))),
% 0.21/0.50    inference(flattening,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X3,X1,X0] : ((sP0(X3,X1,X0) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~sP0(X3,X1,X0)))),
% 0.21/0.50    inference(nnf_transformation,[],[f7])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sP0(k2_mcart_1(sK2),X0,X1) | ~sP1(X1,X0,k2_tarski(sK4,sK5))) )),
% 0.21/0.50    inference(resolution,[],[f38,f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X1] : (sP0(X4,X1,X0) | ~r2_hidden(X4,X2) | ~sP1(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(sK6(X0,X1,X2),X1,X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sP0(sK6(X0,X1,X2),X1,X0) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X4,X1,X0)) & (sP0(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f13,f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2))) => ((~sP0(sK6(X0,X1,X2),X1,X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sP0(sK6(X0,X1,X2),X1,X0) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X4,X1,X0)) & (sP0(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.21/0.50    inference(rectify,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X3,X1,X0)) & (sP0(X3,X1,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 0.21/0.50    inference(nnf_transformation,[],[f8])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    r2_hidden(k2_mcart_1(sK2),k2_tarski(sK4,sK5))),
% 0.21/0.50    inference(resolution,[],[f20,f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    sK4 != k2_mcart_1(sK2) | ~r2_hidden(k1_mcart_1(sK2),sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (16037)------------------------------
% 0.21/0.50  % (16037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (16037)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (16037)Memory used [KB]: 1663
% 0.21/0.50  % (16037)Time elapsed: 0.104 s
% 0.21/0.50  % (16037)------------------------------
% 0.21/0.50  % (16037)------------------------------
% 0.21/0.50  % (16028)Success in time 0.144 s
%------------------------------------------------------------------------------
