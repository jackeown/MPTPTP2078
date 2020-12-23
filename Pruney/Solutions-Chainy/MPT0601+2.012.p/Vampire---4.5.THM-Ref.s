%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 189 expanded)
%              Number of leaves         :    8 (  44 expanded)
%              Depth                    :   15
%              Number of atoms          :  182 ( 778 expanded)
%              Number of equality atoms :   72 ( 284 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f139,plain,(
    $false ),
    inference(global_subsumption,[],[f58,f136])).

fof(f136,plain,(
    k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    inference(resolution,[],[f132,f57])).

fof(f57,plain,(
    ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f25,f56])).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 != k11_relat_1(sK1,X0)
      | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f55,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,k1_tarski(X1))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f29,f37])).

fof(f37,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f55,plain,(
    ! [X0] :
      ( r1_xboole_0(k1_relat_1(sK1),k1_tarski(X0))
      | k1_xboole_0 != k11_relat_1(sK1,X0) ) ),
    inference(global_subsumption,[],[f23,f54])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 != k11_relat_1(sK1,X0)
      | r1_xboole_0(k1_relat_1(sK1),k1_tarski(X0))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f30,f46])).

fof(f46,plain,(
    ! [X0] : k11_relat_1(sK1,X0) = k9_relat_1(sK1,k1_tarski(X0)) ),
    inference(resolution,[],[f26,f23])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) != k1_xboole_0
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( k9_relat_1(X1,X0) = k1_xboole_0
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k9_relat_1(X1,X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k9_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k9_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f23,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
      | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
    & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
      | r2_hidden(sK0,k1_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
        | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
      & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
        | r2_hidden(sK0,k1_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f25,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f132,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_relat_1(sK1))
      | k1_xboole_0 = k11_relat_1(sK1,X0) ) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,(
    ! [X0] :
      ( k1_xboole_0 = k11_relat_1(sK1,X0)
      | r2_hidden(X0,k1_relat_1(sK1))
      | k1_xboole_0 = k11_relat_1(sK1,X0) ) ),
    inference(forward_demodulation,[],[f128,f46])).

fof(f128,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_relat_1(sK1))
      | k1_xboole_0 = k11_relat_1(sK1,X0)
      | k1_xboole_0 = k9_relat_1(sK1,k1_tarski(X0)) ) ),
    inference(resolution,[],[f64,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k1_relat_1(sK1),X0)
      | k1_xboole_0 = k9_relat_1(sK1,X0) ) ),
    inference(resolution,[],[f31,f23])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | k9_relat_1(X1,X0) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f64,plain,(
    ! [X1] :
      ( r1_xboole_0(k1_relat_1(sK1),k1_tarski(X1))
      | r2_hidden(X1,k1_relat_1(sK1))
      | k1_xboole_0 = k11_relat_1(sK1,X1) ) ),
    inference(superposition,[],[f27,f62])).

fof(f62,plain,(
    ! [X1] :
      ( sK2(k1_relat_1(sK1),k1_tarski(X1)) = X1
      | k1_xboole_0 = k11_relat_1(sK1,X1) ) ),
    inference(forward_demodulation,[],[f61,f46])).

fof(f61,plain,(
    ! [X1] :
      ( k1_xboole_0 = k9_relat_1(sK1,k1_tarski(X1))
      | sK2(k1_relat_1(sK1),k1_tarski(X1)) = X1 ) ),
    inference(resolution,[],[f59,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,k1_tarski(X1))
      | sK2(X0,k1_tarski(X1)) = X1 ) ),
    inference(resolution,[],[f28,f38])).

fof(f38,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,(
    k1_xboole_0 != k11_relat_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f24,f57])).

fof(f24,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:12:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (8527)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.48  % (8535)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.49  % (8527)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f139,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(global_subsumption,[],[f58,f136])).
% 0.22/0.49  fof(f136,plain,(
% 0.22/0.49    k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.22/0.49    inference(resolution,[],[f132,f57])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f25,f56])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 != k11_relat_1(sK1,X0) | ~r2_hidden(X0,k1_relat_1(sK1))) )),
% 0.22/0.49    inference(resolution,[],[f55,f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_xboole_0(X0,k1_tarski(X1)) | ~r2_hidden(X1,X0)) )),
% 0.22/0.49    inference(resolution,[],[f29,f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.22/0.49    inference(equality_resolution,[],[f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.22/0.49    inference(equality_resolution,[],[f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.49    inference(rectify,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,plain,(
% 0.22/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.49    inference(rectify,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ( ! [X0] : (r1_xboole_0(k1_relat_1(sK1),k1_tarski(X0)) | k1_xboole_0 != k11_relat_1(sK1,X0)) )),
% 0.22/0.49    inference(global_subsumption,[],[f23,f54])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 != k11_relat_1(sK1,X0) | r1_xboole_0(k1_relat_1(sK1),k1_tarski(X0)) | ~v1_relat_1(sK1)) )),
% 0.22/0.49    inference(superposition,[],[f30,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X0] : (k11_relat_1(sK1,X0) = k9_relat_1(sK1,k1_tarski(X0))) )),
% 0.22/0.49    inference(resolution,[],[f26,f23])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k9_relat_1(X1,X0) != k1_xboole_0 | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1] : (((k9_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k9_relat_1(X1,X0) != k1_xboole_0)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ! [X0,X1] : ((k9_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => (k9_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    v1_relat_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    (k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.22/0.49    inference(negated_conjecture,[],[f5])).
% 0.22/0.49  fof(f5,conjecture,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ~r2_hidden(sK0,k1_relat_1(sK1)) | k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f132,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(X0,k1_relat_1(sK1)) | k1_xboole_0 = k11_relat_1(sK1,X0)) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f131])).
% 0.22/0.49  fof(f131,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = k11_relat_1(sK1,X0) | r2_hidden(X0,k1_relat_1(sK1)) | k1_xboole_0 = k11_relat_1(sK1,X0)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f128,f46])).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(X0,k1_relat_1(sK1)) | k1_xboole_0 = k11_relat_1(sK1,X0) | k1_xboole_0 = k9_relat_1(sK1,k1_tarski(X0))) )),
% 0.22/0.49    inference(resolution,[],[f64,f59])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ( ! [X0] : (~r1_xboole_0(k1_relat_1(sK1),X0) | k1_xboole_0 = k9_relat_1(sK1,X0)) )),
% 0.22/0.49    inference(resolution,[],[f31,f23])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k1_relat_1(X1),X0) | k9_relat_1(X1,X0) = k1_xboole_0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    ( ! [X1] : (r1_xboole_0(k1_relat_1(sK1),k1_tarski(X1)) | r2_hidden(X1,k1_relat_1(sK1)) | k1_xboole_0 = k11_relat_1(sK1,X1)) )),
% 0.22/0.49    inference(superposition,[],[f27,f62])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    ( ! [X1] : (sK2(k1_relat_1(sK1),k1_tarski(X1)) = X1 | k1_xboole_0 = k11_relat_1(sK1,X1)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f61,f46])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    ( ! [X1] : (k1_xboole_0 = k9_relat_1(sK1,k1_tarski(X1)) | sK2(k1_relat_1(sK1),k1_tarski(X1)) = X1) )),
% 0.22/0.49    inference(resolution,[],[f59,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_xboole_0(X0,k1_tarski(X1)) | sK2(X0,k1_tarski(X1)) = X1) )),
% 0.22/0.49    inference(resolution,[],[f28,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.22/0.49    inference(equality_resolution,[],[f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    k1_xboole_0 != k11_relat_1(sK1,sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f24,f57])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (8527)------------------------------
% 0.22/0.49  % (8527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (8527)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (8527)Memory used [KB]: 6268
% 0.22/0.49  % (8527)Time elapsed: 0.063 s
% 0.22/0.49  % (8527)------------------------------
% 0.22/0.49  % (8527)------------------------------
% 0.22/0.50  % (8514)Success in time 0.133 s
%------------------------------------------------------------------------------
