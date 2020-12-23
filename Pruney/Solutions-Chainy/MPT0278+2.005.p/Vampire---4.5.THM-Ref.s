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
% DateTime   : Thu Dec  3 12:41:33 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   50 (  75 expanded)
%              Number of leaves         :   10 (  19 expanded)
%              Depth                    :   11
%              Number of atoms          :  157 ( 266 expanded)
%              Number of equality atoms :   20 (  32 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f103,plain,(
    $false ),
    inference(subsumption_resolution,[],[f100,f27])).

fof(f27,plain,(
    ~ r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f100,plain,(
    r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f86,f57])).

fof(f57,plain,(
    ~ r1_tarski(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),sK1) ),
    inference(resolution,[],[f48,f27])).

fof(f48,plain,(
    ! [X2,X1] :
      ( r1_tarski(X1,k1_zfmisc_1(X2))
      | ~ r1_tarski(sK3(X1,k1_zfmisc_1(X2)),X2) ) ),
    inference(resolution,[],[f37,f41])).

fof(f41,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f86,plain,(
    ! [X2] :
      ( r1_tarski(sK3(k1_zfmisc_1(sK0),X2),sK1)
      | r1_tarski(k1_zfmisc_1(sK0),X2) ) ),
    inference(resolution,[],[f77,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK3(k1_zfmisc_1(X0),X1),X0)
      | r1_tarski(k1_zfmisc_1(X0),X1) ) ),
    inference(resolution,[],[f36,f42])).

fof(f42,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f77,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK0)
      | r1_tarski(X1,sK1) ) ),
    inference(superposition,[],[f33,f73])).

fof(f73,plain,(
    sK1 = k2_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f67,f26])).

fof(f26,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X1,X0) = X1 ) ),
    inference(subsumption_resolution,[],[f64,f43])).

fof(f43,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X1)
      | k2_xboole_0(X1,X0) = X1 ) ),
    inference(resolution,[],[f32,f54])).

fof(f54,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_xboole_0(X1,X2),X1)
      | k2_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f40,f34])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:17:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.46  % (19581)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.23/0.48  % (19581)Refutation found. Thanks to Tanya!
% 0.23/0.48  % SZS status Theorem for theBenchmark
% 0.23/0.49  % (19605)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.23/0.49  % SZS output start Proof for theBenchmark
% 0.23/0.49  fof(f103,plain,(
% 0.23/0.49    $false),
% 0.23/0.49    inference(subsumption_resolution,[],[f100,f27])).
% 0.23/0.49  fof(f27,plain,(
% 0.23/0.49    ~r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),
% 0.23/0.49    inference(cnf_transformation,[],[f15])).
% 0.23/0.49  fof(f15,plain,(
% 0.23/0.49    ~r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) & r1_tarski(sK0,sK1)),
% 0.23/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f14])).
% 0.23/0.49  fof(f14,plain,(
% 0.23/0.49    ? [X0,X1] : (~r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) & r1_tarski(X0,X1)) => (~r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) & r1_tarski(sK0,sK1))),
% 0.23/0.49    introduced(choice_axiom,[])).
% 0.23/0.49  fof(f9,plain,(
% 0.23/0.49    ? [X0,X1] : (~r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) & r1_tarski(X0,X1))),
% 0.23/0.49    inference(ennf_transformation,[],[f8])).
% 0.23/0.49  fof(f8,negated_conjecture,(
% 0.23/0.49    ~! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 0.23/0.49    inference(negated_conjecture,[],[f7])).
% 0.23/0.49  fof(f7,conjecture,(
% 0.23/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 0.23/0.49  fof(f100,plain,(
% 0.23/0.49    r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),
% 0.23/0.49    inference(resolution,[],[f86,f57])).
% 0.23/0.49  fof(f57,plain,(
% 0.23/0.49    ~r1_tarski(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),sK1)),
% 0.23/0.49    inference(resolution,[],[f48,f27])).
% 0.23/0.49  fof(f48,plain,(
% 0.23/0.49    ( ! [X2,X1] : (r1_tarski(X1,k1_zfmisc_1(X2)) | ~r1_tarski(sK3(X1,k1_zfmisc_1(X2)),X2)) )),
% 0.23/0.49    inference(resolution,[],[f37,f41])).
% 0.23/0.49  fof(f41,plain,(
% 0.23/0.49    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.23/0.49    inference(equality_resolution,[],[f29])).
% 0.23/0.49  fof(f29,plain,(
% 0.23/0.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.23/0.49    inference(cnf_transformation,[],[f19])).
% 0.23/0.49  fof(f19,plain,(
% 0.23/0.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.23/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).
% 0.23/0.49  fof(f18,plain,(
% 0.23/0.49    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.23/0.49    introduced(choice_axiom,[])).
% 0.23/0.49  fof(f17,plain,(
% 0.23/0.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.23/0.49    inference(rectify,[],[f16])).
% 0.23/0.49  fof(f16,plain,(
% 0.23/0.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.23/0.49    inference(nnf_transformation,[],[f6])).
% 0.23/0.49  fof(f6,axiom,(
% 0.23/0.49    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.23/0.49  fof(f37,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f23])).
% 0.23/0.49  fof(f23,plain,(
% 0.23/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.23/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).
% 0.23/0.49  fof(f22,plain,(
% 0.23/0.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.23/0.49    introduced(choice_axiom,[])).
% 0.23/0.49  fof(f21,plain,(
% 0.23/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.23/0.49    inference(rectify,[],[f20])).
% 0.23/0.49  fof(f20,plain,(
% 0.23/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.23/0.49    inference(nnf_transformation,[],[f13])).
% 0.23/0.49  fof(f13,plain,(
% 0.23/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.23/0.49    inference(ennf_transformation,[],[f1])).
% 0.23/0.49  fof(f1,axiom,(
% 0.23/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.23/0.49  fof(f86,plain,(
% 0.23/0.49    ( ! [X2] : (r1_tarski(sK3(k1_zfmisc_1(sK0),X2),sK1) | r1_tarski(k1_zfmisc_1(sK0),X2)) )),
% 0.23/0.49    inference(resolution,[],[f77,f46])).
% 0.23/0.49  fof(f46,plain,(
% 0.23/0.49    ( ! [X0,X1] : (r1_tarski(sK3(k1_zfmisc_1(X0),X1),X0) | r1_tarski(k1_zfmisc_1(X0),X1)) )),
% 0.23/0.49    inference(resolution,[],[f36,f42])).
% 0.23/0.49  fof(f42,plain,(
% 0.23/0.49    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 0.23/0.49    inference(equality_resolution,[],[f28])).
% 0.23/0.49  fof(f28,plain,(
% 0.23/0.49    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.23/0.49    inference(cnf_transformation,[],[f19])).
% 0.23/0.49  fof(f36,plain,(
% 0.23/0.49    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f23])).
% 0.23/0.49  fof(f77,plain,(
% 0.23/0.49    ( ! [X1] : (~r1_tarski(X1,sK0) | r1_tarski(X1,sK1)) )),
% 0.23/0.49    inference(superposition,[],[f33,f73])).
% 0.23/0.49  fof(f73,plain,(
% 0.23/0.49    sK1 = k2_xboole_0(sK1,sK0)),
% 0.23/0.49    inference(resolution,[],[f67,f26])).
% 0.23/0.49  fof(f26,plain,(
% 0.23/0.49    r1_tarski(sK0,sK1)),
% 0.23/0.49    inference(cnf_transformation,[],[f15])).
% 0.23/0.49  fof(f67,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X1,X0) = X1) )),
% 0.23/0.49    inference(subsumption_resolution,[],[f64,f43])).
% 0.23/0.49  fof(f43,plain,(
% 0.23/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.23/0.49    inference(equality_resolution,[],[f39])).
% 0.23/0.49  fof(f39,plain,(
% 0.23/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.23/0.49    inference(cnf_transformation,[],[f25])).
% 0.23/0.49  fof(f25,plain,(
% 0.23/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.49    inference(flattening,[],[f24])).
% 0.23/0.49  fof(f24,plain,(
% 0.23/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.49    inference(nnf_transformation,[],[f2])).
% 0.23/0.49  fof(f2,axiom,(
% 0.23/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.23/0.49  fof(f64,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X1) | k2_xboole_0(X1,X0) = X1) )),
% 0.23/0.49    inference(resolution,[],[f32,f54])).
% 0.23/0.49  fof(f54,plain,(
% 0.23/0.49    ( ! [X2,X1] : (~r1_tarski(k2_xboole_0(X1,X2),X1) | k2_xboole_0(X1,X2) = X1) )),
% 0.23/0.49    inference(resolution,[],[f40,f34])).
% 0.23/0.49  fof(f34,plain,(
% 0.23/0.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f4])).
% 0.23/0.49  fof(f4,axiom,(
% 0.23/0.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.23/0.49  fof(f40,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.23/0.49    inference(cnf_transformation,[],[f25])).
% 0.23/0.49  fof(f32,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f11])).
% 0.23/0.49  fof(f11,plain,(
% 0.23/0.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.23/0.49    inference(flattening,[],[f10])).
% 0.23/0.49  fof(f10,plain,(
% 0.23/0.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.23/0.49    inference(ennf_transformation,[],[f5])).
% 0.23/0.49  fof(f5,axiom,(
% 0.23/0.49    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.23/0.49  fof(f33,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f12])).
% 0.23/0.49  fof(f12,plain,(
% 0.23/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.23/0.49    inference(ennf_transformation,[],[f3])).
% 0.23/0.49  fof(f3,axiom,(
% 0.23/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.23/0.49  % SZS output end Proof for theBenchmark
% 0.23/0.49  % (19581)------------------------------
% 0.23/0.49  % (19581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % (19581)Termination reason: Refutation
% 0.23/0.49  
% 0.23/0.49  % (19581)Memory used [KB]: 6268
% 0.23/0.49  % (19581)Time elapsed: 0.088 s
% 0.23/0.49  % (19581)------------------------------
% 0.23/0.49  % (19581)------------------------------
% 0.23/0.49  % (19575)Success in time 0.123 s
%------------------------------------------------------------------------------
