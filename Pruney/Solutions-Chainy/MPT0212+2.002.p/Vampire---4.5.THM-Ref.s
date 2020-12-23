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
% DateTime   : Thu Dec  3 12:34:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 202 expanded)
%              Number of leaves         :    7 (  49 expanded)
%              Depth                    :   19
%              Number of atoms          :  196 (1189 expanded)
%              Number of equality atoms :   98 ( 675 expanded)
%              Maximal formula depth    :    9 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f222,plain,(
    $false ),
    inference(resolution,[],[f208,f39])).

fof(f39,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f208,plain,(
    ! [X4] : ~ r2_hidden(k1_xboole_0,k1_tarski(X4)) ),
    inference(subsumption_resolution,[],[f183,f77])).

fof(f77,plain,(
    ! [X2,X3] :
      ( k1_tarski(X3) = k1_tarski(X2)
      | ~ r2_hidden(X2,k1_tarski(X3)) ) ),
    inference(subsumption_resolution,[],[f75,f40])).

fof(f40,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f75,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_tarski(X3))
      | k1_tarski(X3) = k1_tarski(X2)
      | X2 != X3 ) ),
    inference(trivial_inequality_removal,[],[f74])).

fof(f74,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_tarski(X3))
      | X2 != X2
      | k1_tarski(X3) = k1_tarski(X2)
      | X2 != X3 ) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_tarski(X3))
      | X2 != X2
      | k1_tarski(X3) = k1_tarski(X2)
      | k1_tarski(X3) = k1_tarski(X2)
      | X2 != X3 ) ),
    inference(superposition,[],[f33,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( sK1(X0,k1_tarski(X1)) = X0
      | k1_tarski(X0) = k1_tarski(X1)
      | X0 != X1 ) ),
    inference(subsumption_resolution,[],[f68,f39])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X1))
      | X0 != X1
      | k1_tarski(X0) = k1_tarski(X1)
      | sK1(X0,k1_tarski(X1)) = X0 ) ),
    inference(duplicate_literal_removal,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X1))
      | X0 != X1
      | k1_tarski(X0) = k1_tarski(X1)
      | k1_tarski(X0) = k1_tarski(X1)
      | sK1(X0,k1_tarski(X1)) = X0 ) ),
    inference(superposition,[],[f33,f51])).

fof(f51,plain,(
    ! [X2,X3] :
      ( sK1(X2,k1_tarski(X3)) = X3
      | k1_tarski(X3) = k1_tarski(X2)
      | sK1(X2,k1_tarski(X3)) = X2 ) ),
    inference(resolution,[],[f32,f40])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | sK1(X0,X1) = X0
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1(X0,X1),X1)
      | sK1(X0,X1) != X0
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f183,plain,(
    ! [X4] :
      ( k1_tarski(k1_xboole_0) != k1_tarski(X4)
      | ~ r2_hidden(k1_xboole_0,k1_tarski(X4)) ) ),
    inference(superposition,[],[f20,f177])).

fof(f177,plain,(
    ! [X3] :
      ( k1_zfmisc_1(k1_xboole_0) = k1_tarski(X3)
      | ~ r2_hidden(k1_xboole_0,k1_tarski(X3)) ) ),
    inference(subsumption_resolution,[],[f176,f117])).

fof(f117,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,k1_tarski(X1))
      | X2 = X3
      | ~ r2_hidden(X0,k1_tarski(X3))
      | ~ r2_hidden(X0,k1_tarski(X1)) ) ),
    inference(superposition,[],[f85,f77])).

fof(f85,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k1_tarski(X3))
      | X2 = X4
      | ~ r2_hidden(X3,k1_tarski(X2)) ) ),
    inference(superposition,[],[f40,f77])).

fof(f176,plain,(
    ! [X3] :
      ( ~ r2_hidden(k1_xboole_0,k1_tarski(X3))
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(X3)
      | k1_xboole_0 != X3 ) ),
    inference(subsumption_resolution,[],[f173,f34])).

fof(f34,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f11])).

% (10040)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
fof(f11,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
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

fof(f173,plain,(
    ! [X3] :
      ( ~ r2_hidden(k1_xboole_0,k1_tarski(X3))
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(X3)
      | k1_xboole_0 != X3 ) ),
    inference(duplicate_literal_removal,[],[f170])).

fof(f170,plain,(
    ! [X3] :
      ( ~ r2_hidden(k1_xboole_0,k1_tarski(X3))
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(X3)
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(X3)
      | k1_xboole_0 != X3 ) ),
    inference(superposition,[],[f29,f109])).

fof(f109,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0(k1_xboole_0,k1_tarski(X0))
      | k1_tarski(X0) = k1_zfmisc_1(k1_xboole_0)
      | k1_xboole_0 != X0 ) ),
    inference(equality_factoring,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( sK0(k1_xboole_0,k1_tarski(X0)) = X0
      | k1_tarski(X0) = k1_zfmisc_1(k1_xboole_0)
      | k1_xboole_0 = sK0(k1_xboole_0,k1_tarski(X0)) ) ),
    inference(resolution,[],[f46,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f46,plain,(
    ! [X2,X3] :
      ( r1_tarski(sK0(X2,k1_tarski(X3)),X2)
      | k1_tarski(X3) = k1_zfmisc_1(X2)
      | sK0(X2,k1_tarski(X3)) = X3 ) ),
    inference(resolution,[],[f28,f40])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_tarski(sK0(X0,X1),X0)
      | k1_zfmisc_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK0(X0,X1),X1)
      | ~ r1_tarski(sK0(X0,X1),X0)
      | k1_zfmisc_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f20,plain,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(flattening,[],[f7])).

fof(f7,negated_conjecture,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:18:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (10037)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (10045)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (10047)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (10053)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.52  % (10042)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (10053)Refutation not found, incomplete strategy% (10053)------------------------------
% 0.21/0.52  % (10053)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10045)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (10053)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (10053)Memory used [KB]: 1663
% 0.21/0.52  % (10053)Time elapsed: 0.101 s
% 0.21/0.52  % (10053)------------------------------
% 0.21/0.52  % (10053)------------------------------
% 0.21/0.52  % (10054)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (10054)Refutation not found, incomplete strategy% (10054)------------------------------
% 0.21/0.52  % (10054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10054)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (10054)Memory used [KB]: 1663
% 0.21/0.52  % (10054)Time elapsed: 0.101 s
% 0.21/0.52  % (10054)------------------------------
% 0.21/0.52  % (10054)------------------------------
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f222,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(resolution,[],[f208,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.21/0.52    inference(equality_resolution,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.21/0.52    inference(equality_resolution,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.52    inference(rectify,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.52  fof(f208,plain,(
% 0.21/0.52    ( ! [X4] : (~r2_hidden(k1_xboole_0,k1_tarski(X4))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f183,f77])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ( ! [X2,X3] : (k1_tarski(X3) = k1_tarski(X2) | ~r2_hidden(X2,k1_tarski(X3))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f75,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.21/0.52    inference(equality_resolution,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~r2_hidden(X2,k1_tarski(X3)) | k1_tarski(X3) = k1_tarski(X2) | X2 != X3) )),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f74])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~r2_hidden(X2,k1_tarski(X3)) | X2 != X2 | k1_tarski(X3) = k1_tarski(X2) | X2 != X3) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~r2_hidden(X2,k1_tarski(X3)) | X2 != X2 | k1_tarski(X3) = k1_tarski(X2) | k1_tarski(X3) = k1_tarski(X2) | X2 != X3) )),
% 0.21/0.52    inference(superposition,[],[f33,f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sK1(X0,k1_tarski(X1)) = X0 | k1_tarski(X0) = k1_tarski(X1) | X0 != X1) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f68,f39])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(X1)) | X0 != X1 | k1_tarski(X0) = k1_tarski(X1) | sK1(X0,k1_tarski(X1)) = X0) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(X1)) | X0 != X1 | k1_tarski(X0) = k1_tarski(X1) | k1_tarski(X0) = k1_tarski(X1) | sK1(X0,k1_tarski(X1)) = X0) )),
% 0.21/0.52    inference(superposition,[],[f33,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X2,X3] : (sK1(X2,k1_tarski(X3)) = X3 | k1_tarski(X3) = k1_tarski(X2) | sK1(X2,k1_tarski(X3)) = X2) )),
% 0.21/0.52    inference(resolution,[],[f32,f40])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | sK1(X0,X1) = X0 | k1_tarski(X0) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK1(X0,X1),X1) | sK1(X0,X1) != X0 | k1_tarski(X0) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    ( ! [X4] : (k1_tarski(k1_xboole_0) != k1_tarski(X4) | ~r2_hidden(k1_xboole_0,k1_tarski(X4))) )),
% 0.21/0.52    inference(superposition,[],[f20,f177])).
% 0.21/0.52  fof(f177,plain,(
% 0.21/0.52    ( ! [X3] : (k1_zfmisc_1(k1_xboole_0) = k1_tarski(X3) | ~r2_hidden(k1_xboole_0,k1_tarski(X3))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f176,f117])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X2,k1_tarski(X1)) | X2 = X3 | ~r2_hidden(X0,k1_tarski(X3)) | ~r2_hidden(X0,k1_tarski(X1))) )),
% 0.21/0.52    inference(superposition,[],[f85,f77])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    ( ! [X4,X2,X3] : (~r2_hidden(X4,k1_tarski(X3)) | X2 = X4 | ~r2_hidden(X3,k1_tarski(X2))) )),
% 0.21/0.52    inference(superposition,[],[f40,f77])).
% 0.21/0.52  fof(f176,plain,(
% 0.21/0.52    ( ! [X3] : (~r2_hidden(k1_xboole_0,k1_tarski(X3)) | k1_zfmisc_1(k1_xboole_0) = k1_tarski(X3) | k1_xboole_0 != X3) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f173,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  % (10040)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f173,plain,(
% 0.21/0.52    ( ! [X3] : (~r2_hidden(k1_xboole_0,k1_tarski(X3)) | ~r1_tarski(k1_xboole_0,k1_xboole_0) | k1_zfmisc_1(k1_xboole_0) = k1_tarski(X3) | k1_xboole_0 != X3) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f170])).
% 0.21/0.52  fof(f170,plain,(
% 0.21/0.52    ( ! [X3] : (~r2_hidden(k1_xboole_0,k1_tarski(X3)) | ~r1_tarski(k1_xboole_0,k1_xboole_0) | k1_zfmisc_1(k1_xboole_0) = k1_tarski(X3) | k1_zfmisc_1(k1_xboole_0) = k1_tarski(X3) | k1_xboole_0 != X3) )),
% 0.21/0.52    inference(superposition,[],[f29,f109])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = sK0(k1_xboole_0,k1_tarski(X0)) | k1_tarski(X0) = k1_zfmisc_1(k1_xboole_0) | k1_xboole_0 != X0) )),
% 0.21/0.52    inference(equality_factoring,[],[f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0] : (sK0(k1_xboole_0,k1_tarski(X0)) = X0 | k1_tarski(X0) = k1_zfmisc_1(k1_xboole_0) | k1_xboole_0 = sK0(k1_xboole_0,k1_tarski(X0))) )),
% 0.21/0.52    inference(resolution,[],[f46,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X2,X3] : (r1_tarski(sK0(X2,k1_tarski(X3)),X2) | k1_tarski(X3) = k1_zfmisc_1(X2) | sK0(X2,k1_tarski(X3)) = X3) )),
% 0.21/0.52    inference(resolution,[],[f28,f40])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_tarski(sK0(X0,X1),X0) | k1_zfmisc_1(X0) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.52    inference(rectify,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK0(X0,X1),X1) | ~r1_tarski(sK0(X0,X1),X0) | k1_zfmisc_1(X0) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0)),
% 0.21/0.52    inference(flattening,[],[f7])).
% 0.21/0.52  fof(f7,negated_conjecture,(
% 0.21/0.52    ~k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.21/0.52    inference(negated_conjecture,[],[f6])).
% 0.21/0.52  fof(f6,conjecture,(
% 0.21/0.52    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (10045)------------------------------
% 0.21/0.52  % (10045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10045)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (10045)Memory used [KB]: 1791
% 0.21/0.52  % (10045)Time elapsed: 0.113 s
% 0.21/0.52  % (10045)------------------------------
% 0.21/0.52  % (10045)------------------------------
% 0.21/0.53  % (10035)Success in time 0.163 s
%------------------------------------------------------------------------------
