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
% DateTime   : Thu Dec  3 12:39:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 130 expanded)
%              Number of leaves         :   10 (  34 expanded)
%              Depth                    :   18
%              Number of atoms          :  171 ( 668 expanded)
%              Number of equality atoms :   30 ( 129 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f193,plain,(
    $false ),
    inference(resolution,[],[f151,f52])).

fof(f52,plain,(
    r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f43,f22])).

fof(f22,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f43,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | r2_hidden(sK0,sK1) ),
    inference(superposition,[],[f28,f39])).

fof(f39,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f21,f24])).

fof(f24,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f21,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f14])).

fof(f14,plain,
    ( ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)
   => k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

fof(f151,plain,(
    ! [X4] : ~ r2_hidden(X4,sK1) ),
    inference(subsumption_resolution,[],[f150,f49])).

fof(f49,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK1)
      | r2_hidden(X5,k1_xboole_0) ) ),
    inference(superposition,[],[f40,f39])).

fof(f40,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & ~ r2_hidden(sK2(X0,X1,X2),X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( r2_hidden(sK2(X0,X1,X2),X1)
            | r2_hidden(sK2(X0,X1,X2),X0)
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & ~ r2_hidden(sK2(X0,X1,X2),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(sK2(X0,X1,X2),X1)
          | r2_hidden(sK2(X0,X1,X2),X0)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f150,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(subsumption_resolution,[],[f149,f54])).

fof(f54,plain,(
    ! [X2] : r1_xboole_0(X2,sK1) ),
    inference(subsumption_resolution,[],[f46,f23])).

fof(f23,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f46,plain,(
    ! [X2] :
      ( ~ r1_xboole_0(X2,k1_xboole_0)
      | r1_xboole_0(X2,sK1) ) ),
    inference(superposition,[],[f27,f39])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f149,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ r2_hidden(X4,sK1)
      | ~ r1_xboole_0(k1_xboole_0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ r2_hidden(X4,sK1)
      | ~ r2_hidden(X4,k1_xboole_0)
      | ~ r1_xboole_0(k1_xboole_0,sK1) ) ),
    inference(superposition,[],[f38,f139])).

fof(f139,plain,(
    k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1) ),
    inference(subsumption_resolution,[],[f138,f121])).

fof(f121,plain,(
    ! [X1] :
      ( r2_hidden(sK2(k1_xboole_0,sK1,X1),k1_xboole_0)
      | r2_hidden(sK2(k1_xboole_0,sK1,X1),X1)
      | k2_xboole_0(k1_xboole_0,sK1) = X1 ) ),
    inference(factoring,[],[f58])).

fof(f58,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK2(X2,sK1,X3),k1_xboole_0)
      | r2_hidden(sK2(X2,sK1,X3),X3)
      | r2_hidden(sK2(X2,sK1,X3),X2)
      | k2_xboole_0(X2,sK1) = X3 ) ),
    inference(resolution,[],[f49,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f138,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1)
    | ~ r2_hidden(sK2(k1_xboole_0,sK1,k1_xboole_0),k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1)
    | ~ r2_hidden(sK2(k1_xboole_0,sK1,k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1) ),
    inference(resolution,[],[f134,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f134,plain,(
    ! [X2] :
      ( r2_hidden(sK2(X2,sK1,X2),k1_xboole_0)
      | k2_xboole_0(X2,sK1) = X2 ) ),
    inference(subsumption_resolution,[],[f122,f33])).

fof(f122,plain,(
    ! [X2] :
      ( r2_hidden(sK2(X2,sK1,X2),k1_xboole_0)
      | r2_hidden(sK2(X2,sK1,X2),X2)
      | k2_xboole_0(X2,sK1) = X2 ) ),
    inference(factoring,[],[f58])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X2,X0)
        & r2_hidden(X2,X1) )
      | ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,X1) )
        & ~ ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) )
        & r2_hidden(X2,k2_xboole_0(X0,X1))
        & r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:09:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (11448)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (11448)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (11440)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (11444)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f193,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(resolution,[],[f151,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    r2_hidden(sK0,sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f43,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ~r1_tarski(k1_xboole_0,sK1) | r2_hidden(sK0,sK1)),
% 0.21/0.52    inference(superposition,[],[f28,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK0),sK1)),
% 0.21/0.52    inference(definition_unfolding,[],[f21,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) => k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.52    inference(negated_conjecture,[],[f8])).
% 0.21/0.52  fof(f8,conjecture,(
% 0.21/0.52    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) | r2_hidden(X0,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r2_hidden(X0,X2) | ~r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    ( ! [X4] : (~r2_hidden(X4,sK1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f150,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X5] : (~r2_hidden(X5,sK1) | r2_hidden(X5,k1_xboole_0)) )),
% 0.21/0.52    inference(superposition,[],[f40,f39])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.52    inference(rectify,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0) | ~r2_hidden(X4,sK1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f149,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X2] : (r1_xboole_0(X2,sK1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f46,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X2] : (~r1_xboole_0(X2,k1_xboole_0) | r1_xboole_0(X2,sK1)) )),
% 0.21/0.52    inference(superposition,[],[f27,f39])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0) | ~r2_hidden(X4,sK1) | ~r1_xboole_0(k1_xboole_0,sK1)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f145])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0) | ~r2_hidden(X4,sK1) | ~r2_hidden(X4,k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,sK1)) )),
% 0.21/0.52    inference(superposition,[],[f38,f139])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f138,f121])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    ( ! [X1] : (r2_hidden(sK2(k1_xboole_0,sK1,X1),k1_xboole_0) | r2_hidden(sK2(k1_xboole_0,sK1,X1),X1) | k2_xboole_0(k1_xboole_0,sK1) = X1) )),
% 0.21/0.52    inference(factoring,[],[f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X2,X3] : (r2_hidden(sK2(X2,sK1,X3),k1_xboole_0) | r2_hidden(sK2(X2,sK1,X3),X3) | r2_hidden(sK2(X2,sK1,X3),X2) | k2_xboole_0(X2,sK1) = X3) )),
% 0.21/0.52    inference(resolution,[],[f49,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | k2_xboole_0(X0,X1) = X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1) | ~r2_hidden(sK2(k1_xboole_0,sK1,k1_xboole_0),k1_xboole_0)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f135])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1) | ~r2_hidden(sK2(k1_xboole_0,sK1,k1_xboole_0),k1_xboole_0) | k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1)),
% 0.21/0.52    inference(resolution,[],[f134,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | ~r2_hidden(sK2(X0,X1,X2),X0) | k2_xboole_0(X0,X1) = X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    ( ! [X2] : (r2_hidden(sK2(X2,sK1,X2),k1_xboole_0) | k2_xboole_0(X2,sK1) = X2) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f122,f33])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    ( ! [X2] : (r2_hidden(sK2(X2,sK1,X2),k1_xboole_0) | r2_hidden(sK2(X2,sK1,X2),X2) | k2_xboole_0(X2,sK1) = X2) )),
% 0.21/0.52    inference(factoring,[],[f58])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ~(~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & ~(~r2_hidden(X2,X1) & r2_hidden(X2,X0)) & r2_hidden(X2,k2_xboole_0(X0,X1)) & r1_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (11448)------------------------------
% 0.21/0.52  % (11448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11448)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (11448)Memory used [KB]: 10874
% 0.21/0.52  % (11448)Time elapsed: 0.094 s
% 0.21/0.52  % (11448)------------------------------
% 0.21/0.52  % (11448)------------------------------
% 0.21/0.52  % (11439)Success in time 0.161 s
%------------------------------------------------------------------------------
