%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 114 expanded)
%              Number of leaves         :    4 (  24 expanded)
%              Depth                    :   16
%              Number of atoms          :  204 ( 911 expanded)
%              Number of equality atoms :  159 ( 712 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f480,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f463])).

fof(f463,plain,
    ( sK0 != sK0
    | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
    inference(superposition,[],[f42,f376])).

fof(f376,plain,(
    sK0 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2)) ),
    inference(trivial_inequality_removal,[],[f360])).

fof(f360,plain,
    ( sK1 != sK1
    | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
    | sK0 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2)) ),
    inference(superposition,[],[f37,f328])).

fof(f328,plain,
    ( sK1 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2))
    | sK0 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2)) ),
    inference(trivial_inequality_removal,[],[f313])).

fof(f313,plain,
    ( sK2 != sK2
    | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
    | sK1 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2))
    | sK0 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2)) ),
    inference(superposition,[],[f43,f184])).

fof(f184,plain,
    ( sK2 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2))
    | sK1 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2))
    | sK0 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2)) ),
    inference(duplicate_literal_removal,[],[f183])).

fof(f183,plain,
    ( sK0 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2))
    | sK1 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2))
    | sK2 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2))
    | sK2 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2))
    | sK1 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2))
    | sK0 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2)) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X5,X3] :
      ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(X3,X4,X5)
      | sK0 = sK3(sK1,sK0,sK2,k1_enumset1(X3,X4,X5))
      | sK1 = sK3(sK1,sK0,sK2,k1_enumset1(X3,X4,X5))
      | sK2 = sK3(sK1,sK0,sK2,k1_enumset1(X3,X4,X5))
      | sK3(sK1,sK0,sK2,k1_enumset1(X3,X4,X5)) = X5
      | sK3(sK1,sK0,sK2,k1_enumset1(X3,X4,X5)) = X4
      | sK3(sK1,sK0,sK2,k1_enumset1(X3,X4,X5)) = X3 ) ),
    inference(resolution,[],[f29,f28])).

fof(f28,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k1_enumset1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK3(X0,X1,X2,X3) != X2
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X2
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X0
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f11])).

fof(f11,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK3(X0,X1,X2,X3) != X2
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X2
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X0
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK1,sK0,sK2,X0),X0)
      | sK2 = sK3(sK1,sK0,sK2,X0)
      | sK0 = sK3(sK1,sK0,sK2,X0)
      | sK1 = sK3(sK1,sK0,sK2,X0)
      | k1_enumset1(sK0,sK1,sK2) != X0 ) ),
    inference(superposition,[],[f13,f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK3(X0,X1,X2,X3) = X2
      | sK3(X0,X1,X2,X3) = X1
      | sK3(X0,X1,X2,X3) = X0
      | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f4,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2)
   => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2) ),
    introduced(choice_axiom,[])).

fof(f4,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( sK2 != sK3(sK1,sK0,sK2,k1_enumset1(X0,X1,sK2))
      | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(X0,X1,sK2) ) ),
    inference(resolution,[],[f35,f23])).

fof(f23,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK2,X3)
      | sK2 != sK3(sK1,sK0,sK2,X3)
      | k1_enumset1(sK0,sK1,sK2) != X3 ) ),
    inference(inner_rewriting,[],[f32])).

fof(f32,plain,(
    ! [X3] :
      ( k1_enumset1(sK0,sK1,sK2) != X3
      | sK2 != sK3(sK1,sK0,sK2,X3)
      | ~ r2_hidden(sK3(sK1,sK0,sK2,X3),X3) ) ),
    inference(superposition,[],[f13,f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK3(X0,X1,X2,X3) != X2
      | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X2,X3] :
      ( sK1 != sK3(sK1,sK0,sK2,k1_enumset1(X2,sK1,X3))
      | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(X2,sK1,X3) ) ),
    inference(resolution,[],[f33,f25])).

fof(f25,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k1_enumset1(X0,X5,X2)) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK1,X1)
      | sK1 != sK3(sK1,sK0,sK2,X1)
      | k1_enumset1(sK0,sK1,sK2) != X1 ) ),
    inference(inner_rewriting,[],[f30])).

fof(f30,plain,(
    ! [X1] :
      ( k1_enumset1(sK0,sK1,sK2) != X1
      | sK1 != sK3(sK1,sK0,sK2,X1)
      | ~ r2_hidden(sK3(sK1,sK0,sK2,X1),X1) ) ),
    inference(superposition,[],[f13,f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK3(X0,X1,X2,X3) != X0
      | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f42,plain,(
    ! [X4,X5] :
      ( sK0 != sK3(sK1,sK0,sK2,k1_enumset1(sK0,X4,X5))
      | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,X4,X5) ) ),
    inference(resolution,[],[f34,f27])).

fof(f27,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK0,X2)
      | sK0 != sK3(sK1,sK0,sK2,X2)
      | k1_enumset1(sK0,sK1,sK2) != X2 ) ),
    inference(inner_rewriting,[],[f31])).

fof(f31,plain,(
    ! [X2] :
      ( k1_enumset1(sK0,sK1,sK2) != X2
      | sK0 != sK3(sK1,sK0,sK2,X2)
      | ~ r2_hidden(sK3(sK1,sK0,sK2,X2),X2) ) ),
    inference(superposition,[],[f13,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK3(X0,X1,X2,X3) != X1
      | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:20:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (14894)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (14892)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (14894)Refutation not found, incomplete strategy% (14894)------------------------------
% 0.21/0.48  % (14894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (14894)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (14894)Memory used [KB]: 6140
% 0.21/0.48  % (14894)Time elapsed: 0.065 s
% 0.21/0.48  % (14894)------------------------------
% 0.21/0.48  % (14894)------------------------------
% 0.21/0.48  % (14898)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.48  % (14902)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (14902)Refutation not found, incomplete strategy% (14902)------------------------------
% 0.21/0.48  % (14902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (14902)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (14902)Memory used [KB]: 10490
% 0.21/0.48  % (14902)Time elapsed: 0.067 s
% 0.21/0.48  % (14902)------------------------------
% 0.21/0.48  % (14902)------------------------------
% 0.21/0.49  % (14900)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.49  % (14887)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (14893)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (14890)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (14895)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (14893)Refutation not found, incomplete strategy% (14893)------------------------------
% 0.21/0.49  % (14893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (14893)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (14893)Memory used [KB]: 10618
% 0.21/0.49  % (14893)Time elapsed: 0.086 s
% 0.21/0.49  % (14893)------------------------------
% 0.21/0.49  % (14893)------------------------------
% 0.21/0.49  % (14895)Refutation not found, incomplete strategy% (14895)------------------------------
% 0.21/0.49  % (14895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (14895)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (14895)Memory used [KB]: 1535
% 0.21/0.49  % (14895)Time elapsed: 0.047 s
% 0.21/0.49  % (14895)------------------------------
% 0.21/0.49  % (14895)------------------------------
% 0.21/0.50  % (14891)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (14892)Refutation not found, incomplete strategy% (14892)------------------------------
% 0.21/0.50  % (14892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (14892)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (14892)Memory used [KB]: 6012
% 0.21/0.50  % (14892)Time elapsed: 0.068 s
% 0.21/0.50  % (14892)------------------------------
% 0.21/0.50  % (14892)------------------------------
% 0.21/0.50  % (14886)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (14883)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (14888)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (14883)Refutation not found, incomplete strategy% (14883)------------------------------
% 0.21/0.50  % (14883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (14883)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (14883)Memory used [KB]: 10490
% 0.21/0.50  % (14883)Time elapsed: 0.092 s
% 0.21/0.50  % (14883)------------------------------
% 0.21/0.50  % (14883)------------------------------
% 0.21/0.50  % (14897)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (14897)Refutation not found, incomplete strategy% (14897)------------------------------
% 0.21/0.50  % (14897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (14897)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (14897)Memory used [KB]: 6140
% 0.21/0.50  % (14897)Time elapsed: 0.093 s
% 0.21/0.50  % (14897)------------------------------
% 0.21/0.50  % (14897)------------------------------
% 0.21/0.50  % (14885)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (14901)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  % (14885)Refutation not found, incomplete strategy% (14885)------------------------------
% 0.21/0.51  % (14885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (14885)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (14885)Memory used [KB]: 10490
% 0.21/0.51  % (14885)Time elapsed: 0.089 s
% 0.21/0.51  % (14885)------------------------------
% 0.21/0.51  % (14885)------------------------------
% 0.21/0.51  % (14882)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (14889)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.51  % (14884)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (14899)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.52  % (14882)Refutation not found, incomplete strategy% (14882)------------------------------
% 0.21/0.52  % (14882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14882)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (14882)Memory used [KB]: 6012
% 0.21/0.52  % (14882)Time elapsed: 0.074 s
% 0.21/0.52  % (14882)------------------------------
% 0.21/0.52  % (14882)------------------------------
% 0.21/0.52  % (14886)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f480,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f463])).
% 0.21/0.52  fof(f463,plain,(
% 0.21/0.52    sK0 != sK0 | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)),
% 0.21/0.52    inference(superposition,[],[f42,f376])).
% 0.21/0.52  fof(f376,plain,(
% 0.21/0.52    sK0 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2))),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f360])).
% 0.21/0.52  fof(f360,plain,(
% 0.21/0.52    sK1 != sK1 | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) | sK0 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2))),
% 0.21/0.52    inference(superposition,[],[f37,f328])).
% 0.21/0.52  fof(f328,plain,(
% 0.21/0.52    sK1 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2)) | sK0 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2))),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f313])).
% 0.21/0.52  fof(f313,plain,(
% 0.21/0.52    sK2 != sK2 | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) | sK1 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2)) | sK0 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2))),
% 0.21/0.52    inference(superposition,[],[f43,f184])).
% 0.21/0.52  fof(f184,plain,(
% 0.21/0.52    sK2 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2)) | sK1 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2)) | sK0 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2))),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f183])).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    sK0 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2)) | sK1 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2)) | sK2 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2)) | sK2 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2)) | sK1 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2)) | sK0 = sK3(sK1,sK0,sK2,k1_enumset1(sK0,sK1,sK2))),
% 0.21/0.52    inference(equality_resolution,[],[f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X4,X5,X3] : (k1_enumset1(sK0,sK1,sK2) != k1_enumset1(X3,X4,X5) | sK0 = sK3(sK1,sK0,sK2,k1_enumset1(X3,X4,X5)) | sK1 = sK3(sK1,sK0,sK2,k1_enumset1(X3,X4,X5)) | sK2 = sK3(sK1,sK0,sK2,k1_enumset1(X3,X4,X5)) | sK3(sK1,sK0,sK2,k1_enumset1(X3,X4,X5)) = X5 | sK3(sK1,sK0,sK2,k1_enumset1(X3,X4,X5)) = X4 | sK3(sK1,sK0,sK2,k1_enumset1(X3,X4,X5)) = X3) )),
% 0.21/0.52    inference(resolution,[],[f29,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k1_enumset1(X0,X1,X2))) )),
% 0.21/0.52    inference(equality_resolution,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.52    inference(rectify,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.52    inference(flattening,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.52    inference(nnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK3(sK1,sK0,sK2,X0),X0) | sK2 = sK3(sK1,sK0,sK2,X0) | sK0 = sK3(sK1,sK0,sK2,X0) | sK1 = sK3(sK1,sK0,sK2,X0) | k1_enumset1(sK0,sK1,sK2) != X0) )),
% 0.21/0.52    inference(superposition,[],[f13,f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,plain,(
% 0.21/0.52    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f4,f6])).
% 0.21/0.52  fof(f6,plain,(
% 0.21/0.52    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2) => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2)),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f4,plain,(
% 0.21/0.52    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2)),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 0.21/0.52    inference(negated_conjecture,[],[f2])).
% 0.21/0.52  fof(f2,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sK2 != sK3(sK1,sK0,sK2,k1_enumset1(X0,X1,sK2)) | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(X0,X1,sK2)) )),
% 0.21/0.52    inference(resolution,[],[f35,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X0,X5,X1] : (r2_hidden(X5,k1_enumset1(X0,X1,X5))) )),
% 0.21/0.52    inference(equality_resolution,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X0,X1,X5) != X3) )),
% 0.21/0.52    inference(equality_resolution,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X3] : (~r2_hidden(sK2,X3) | sK2 != sK3(sK1,sK0,sK2,X3) | k1_enumset1(sK0,sK1,sK2) != X3) )),
% 0.21/0.52    inference(inner_rewriting,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X3] : (k1_enumset1(sK0,sK1,sK2) != X3 | sK2 != sK3(sK1,sK0,sK2,X3) | ~r2_hidden(sK3(sK1,sK0,sK2,X3),X3)) )),
% 0.21/0.52    inference(superposition,[],[f13,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK3(X0,X1,X2,X3) != X2 | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X2,X3] : (sK1 != sK3(sK1,sK0,sK2,k1_enumset1(X2,sK1,X3)) | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(X2,sK1,X3)) )),
% 0.21/0.52    inference(resolution,[],[f33,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X2,X0,X5] : (r2_hidden(X5,k1_enumset1(X0,X5,X2))) )),
% 0.21/0.52    inference(equality_resolution,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k1_enumset1(X0,X5,X2) != X3) )),
% 0.21/0.52    inference(equality_resolution,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X1] : (~r2_hidden(sK1,X1) | sK1 != sK3(sK1,sK0,sK2,X1) | k1_enumset1(sK0,sK1,sK2) != X1) )),
% 0.21/0.52    inference(inner_rewriting,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X1] : (k1_enumset1(sK0,sK1,sK2) != X1 | sK1 != sK3(sK1,sK0,sK2,X1) | ~r2_hidden(sK3(sK1,sK0,sK2,X1),X1)) )),
% 0.21/0.52    inference(superposition,[],[f13,f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK3(X0,X1,X2,X3) != X0 | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X4,X5] : (sK0 != sK3(sK1,sK0,sK2,k1_enumset1(sK0,X4,X5)) | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,X4,X5)) )),
% 0.21/0.52    inference(resolution,[],[f34,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X2,X5,X1] : (r2_hidden(X5,k1_enumset1(X5,X1,X2))) )),
% 0.21/0.52    inference(equality_resolution,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X5,X1,X2) != X3) )),
% 0.21/0.52    inference(equality_resolution,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X2] : (~r2_hidden(sK0,X2) | sK0 != sK3(sK1,sK0,sK2,X2) | k1_enumset1(sK0,sK1,sK2) != X2) )),
% 0.21/0.52    inference(inner_rewriting,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X2] : (k1_enumset1(sK0,sK1,sK2) != X2 | sK0 != sK3(sK1,sK0,sK2,X2) | ~r2_hidden(sK3(sK1,sK0,sK2,X2),X2)) )),
% 0.21/0.52    inference(superposition,[],[f13,f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK3(X0,X1,X2,X3) != X1 | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (14886)------------------------------
% 0.21/0.52  % (14886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14886)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (14886)Memory used [KB]: 2046
% 0.21/0.52  % (14886)Time elapsed: 0.102 s
% 0.21/0.52  % (14886)------------------------------
% 0.21/0.52  % (14886)------------------------------
% 0.21/0.52  % (14881)Success in time 0.157 s
%------------------------------------------------------------------------------
