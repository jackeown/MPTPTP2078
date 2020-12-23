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
% DateTime   : Thu Dec  3 12:55:36 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 321 expanded)
%              Number of leaves         :    8 (  87 expanded)
%              Depth                    :   18
%              Number of atoms          :  196 (1609 expanded)
%              Number of equality atoms :   16 (  46 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f134,plain,(
    $false ),
    inference(subsumption_resolution,[],[f133,f68])).

fof(f68,plain,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f133,plain,(
    ~ r2_hidden(sK0,k1_ordinal1(sK0)) ),
    inference(forward_demodulation,[],[f132,f115])).

fof(f115,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f112,f101])).

fof(f101,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f99,f87])).

fof(f87,plain,
    ( ~ r2_hidden(sK1,sK0)
    | r2_hidden(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f84,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_ordinal1(X1))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f84,plain,
    ( r2_hidden(sK0,k1_ordinal1(sK1))
    | ~ r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f80,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f80,plain,
    ( r1_tarski(sK0,sK1)
    | r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(subsumption_resolution,[],[f79,f39])).

fof(f39,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ~ r1_ordinal1(sK0,sK1)
      | ~ r2_hidden(sK0,k1_ordinal1(sK1)) )
    & ( r1_ordinal1(sK0,sK1)
      | r2_hidden(sK0,k1_ordinal1(sK1)) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) )
            & ( r1_ordinal1(X0,X1)
              | r2_hidden(X0,k1_ordinal1(X1)) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(sK0,X1)
            | ~ r2_hidden(sK0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(sK0,X1)
            | r2_hidden(sK0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(sK0,X1)
          | ~ r2_hidden(sK0,k1_ordinal1(X1)) )
        & ( r1_ordinal1(sK0,X1)
          | r2_hidden(sK0,k1_ordinal1(X1)) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(sK0,sK1)
        | ~ r2_hidden(sK0,k1_ordinal1(sK1)) )
      & ( r1_ordinal1(sK0,sK1)
        | r2_hidden(sK0,k1_ordinal1(sK1)) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f79,plain,
    ( r2_hidden(sK0,k1_ordinal1(sK1))
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f78,f40])).

fof(f40,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f78,plain,
    ( r2_hidden(sK0,k1_ordinal1(sK1))
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f41,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f41,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f99,plain,
    ( r2_hidden(sK1,sK0)
    | r2_hidden(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f74,f40])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r2_hidden(X0,sK0)
      | r2_hidden(sK0,X0)
      | sK0 = X0 ) ),
    inference(resolution,[],[f39,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | X0 = X1
      | r2_hidden(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f112,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f110,f52])).

fof(f110,plain,
    ( r1_tarski(sK1,sK0)
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f104,f81])).

fof(f81,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f42,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

% (31034)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
fof(f42,plain,
    ( ~ r2_hidden(sK0,k1_ordinal1(sK1))
    | ~ r1_ordinal1(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f104,plain,
    ( r1_ordinal1(sK0,sK1)
    | r1_tarski(sK1,sK0) ),
    inference(subsumption_resolution,[],[f103,f40])).

fof(f103,plain,
    ( r1_ordinal1(sK0,sK1)
    | r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(subsumption_resolution,[],[f102,f39])).

fof(f102,plain,
    ( r1_ordinal1(sK0,sK1)
    | r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f89,f43])).

fof(f89,plain,
    ( r1_ordinal1(sK1,sK0)
    | r1_ordinal1(sK0,sK1) ),
    inference(resolution,[],[f75,f40])).

fof(f75,plain,(
    ! [X1] :
      ( ~ v3_ordinal1(X1)
      | r1_ordinal1(sK0,X1)
      | r1_ordinal1(X1,sK0) ) ),
    inference(resolution,[],[f39,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X1)
      | r1_ordinal1(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f132,plain,(
    ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(subsumption_resolution,[],[f118,f90])).

fof(f90,plain,(
    r1_ordinal1(sK0,sK0) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,
    ( r1_ordinal1(sK0,sK0)
    | r1_ordinal1(sK0,sK0) ),
    inference(resolution,[],[f75,f39])).

fof(f118,plain,
    ( ~ r1_ordinal1(sK0,sK0)
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(backward_demodulation,[],[f42,f115])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:31:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (31042)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.51  % (31060)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.17/0.51  % (31038)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.17/0.52  % (31037)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.17/0.52  % (31039)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.17/0.52  % (31051)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.17/0.53  % (31040)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.17/0.53  % (31059)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.31/0.53  % (31049)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.31/0.53  % (31056)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.31/0.53  % (31049)Refutation found. Thanks to Tanya!
% 1.31/0.53  % SZS status Theorem for theBenchmark
% 1.31/0.53  % (31041)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.31/0.53  % (31035)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.31/0.53  % SZS output start Proof for theBenchmark
% 1.31/0.53  fof(f134,plain,(
% 1.31/0.53    $false),
% 1.31/0.53    inference(subsumption_resolution,[],[f133,f68])).
% 1.31/0.54  fof(f68,plain,(
% 1.31/0.54    ( ! [X1] : (r2_hidden(X1,k1_ordinal1(X1))) )),
% 1.31/0.54    inference(equality_resolution,[],[f55])).
% 1.31/0.54  fof(f55,plain,(
% 1.31/0.54    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 1.31/0.54    inference(cnf_transformation,[],[f32])).
% 1.31/0.54  fof(f32,plain,(
% 1.31/0.54    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 1.31/0.54    inference(flattening,[],[f31])).
% 1.31/0.54  fof(f31,plain,(
% 1.31/0.54    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 1.31/0.54    inference(nnf_transformation,[],[f7])).
% 1.31/0.54  fof(f7,axiom,(
% 1.31/0.54    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).
% 1.31/0.54  fof(f133,plain,(
% 1.31/0.54    ~r2_hidden(sK0,k1_ordinal1(sK0))),
% 1.31/0.54    inference(forward_demodulation,[],[f132,f115])).
% 1.31/0.54  fof(f115,plain,(
% 1.31/0.54    sK0 = sK1),
% 1.31/0.54    inference(resolution,[],[f112,f101])).
% 1.31/0.54  fof(f101,plain,(
% 1.31/0.54    r2_hidden(sK0,sK1) | sK0 = sK1),
% 1.31/0.54    inference(subsumption_resolution,[],[f99,f87])).
% 1.31/0.54  fof(f87,plain,(
% 1.31/0.54    ~r2_hidden(sK1,sK0) | r2_hidden(sK0,sK1) | sK0 = sK1),
% 1.31/0.54    inference(resolution,[],[f84,f53])).
% 1.31/0.54  fof(f53,plain,(
% 1.31/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k1_ordinal1(X1)) | r2_hidden(X0,X1) | X0 = X1) )),
% 1.31/0.54    inference(cnf_transformation,[],[f32])).
% 1.31/0.54  fof(f84,plain,(
% 1.31/0.54    r2_hidden(sK0,k1_ordinal1(sK1)) | ~r2_hidden(sK1,sK0)),
% 1.31/0.54    inference(resolution,[],[f80,f52])).
% 1.31/0.54  fof(f52,plain,(
% 1.31/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f17])).
% 1.31/0.54  fof(f17,plain,(
% 1.31/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.31/0.54    inference(ennf_transformation,[],[f9])).
% 1.31/0.54  fof(f9,axiom,(
% 1.31/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.31/0.54  fof(f80,plain,(
% 1.31/0.54    r1_tarski(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))),
% 1.31/0.54    inference(subsumption_resolution,[],[f79,f39])).
% 1.31/0.54  fof(f39,plain,(
% 1.31/0.54    v3_ordinal1(sK0)),
% 1.31/0.54    inference(cnf_transformation,[],[f24])).
% 1.31/0.54  fof(f24,plain,(
% 1.31/0.54    ((~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))) & (r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 1.31/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23,f22])).
% 1.31/0.54  fof(f22,plain,(
% 1.31/0.54    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK0,X1) | ~r2_hidden(sK0,k1_ordinal1(X1))) & (r1_ordinal1(sK0,X1) | r2_hidden(sK0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 1.31/0.54    introduced(choice_axiom,[])).
% 1.31/0.54  fof(f23,plain,(
% 1.31/0.54    ? [X1] : ((~r1_ordinal1(sK0,X1) | ~r2_hidden(sK0,k1_ordinal1(X1))) & (r1_ordinal1(sK0,X1) | r2_hidden(sK0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))) & (r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))) & v3_ordinal1(sK1))),
% 1.31/0.54    introduced(choice_axiom,[])).
% 1.31/0.54  fof(f21,plain,(
% 1.31/0.54    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.31/0.54    inference(flattening,[],[f20])).
% 1.31/0.54  fof(f20,plain,(
% 1.31/0.54    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.31/0.54    inference(nnf_transformation,[],[f12])).
% 1.31/0.54  fof(f12,plain,(
% 1.31/0.54    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.31/0.54    inference(ennf_transformation,[],[f11])).
% 1.31/0.54  fof(f11,negated_conjecture,(
% 1.31/0.54    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.31/0.54    inference(negated_conjecture,[],[f10])).
% 1.31/0.54  fof(f10,conjecture,(
% 1.31/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 1.31/0.54  fof(f79,plain,(
% 1.31/0.54    r2_hidden(sK0,k1_ordinal1(sK1)) | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0)),
% 1.31/0.54    inference(subsumption_resolution,[],[f78,f40])).
% 1.31/0.54  fof(f40,plain,(
% 1.31/0.54    v3_ordinal1(sK1)),
% 1.31/0.54    inference(cnf_transformation,[],[f24])).
% 1.31/0.54  fof(f78,plain,(
% 1.31/0.54    r2_hidden(sK0,k1_ordinal1(sK1)) | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0)),
% 1.31/0.54    inference(resolution,[],[f41,f43])).
% 1.31/0.54  fof(f43,plain,(
% 1.31/0.54    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f25])).
% 1.31/0.54  fof(f25,plain,(
% 1.31/0.54    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.31/0.54    inference(nnf_transformation,[],[f14])).
% 1.31/0.54  fof(f14,plain,(
% 1.31/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.31/0.54    inference(flattening,[],[f13])).
% 1.31/0.54  fof(f13,plain,(
% 1.31/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.31/0.54    inference(ennf_transformation,[],[f6])).
% 1.31/0.54  fof(f6,axiom,(
% 1.31/0.54    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 1.31/0.54  fof(f41,plain,(
% 1.31/0.54    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))),
% 1.31/0.54    inference(cnf_transformation,[],[f24])).
% 1.31/0.54  fof(f99,plain,(
% 1.31/0.54    r2_hidden(sK1,sK0) | r2_hidden(sK0,sK1) | sK0 = sK1),
% 1.31/0.54    inference(resolution,[],[f74,f40])).
% 1.31/0.54  fof(f74,plain,(
% 1.31/0.54    ( ! [X0] : (~v3_ordinal1(X0) | r2_hidden(X0,sK0) | r2_hidden(sK0,X0) | sK0 = X0) )),
% 1.31/0.54    inference(resolution,[],[f39,f60])).
% 1.31/0.54  fof(f60,plain,(
% 1.31/0.54    ( ! [X0,X1] : (~v3_ordinal1(X1) | X0 = X1 | r2_hidden(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X0)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f19])).
% 1.31/0.54  fof(f19,plain,(
% 1.31/0.54    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.31/0.54    inference(flattening,[],[f18])).
% 1.31/0.54  fof(f18,plain,(
% 1.31/0.54    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.31/0.54    inference(ennf_transformation,[],[f8])).
% 1.31/0.54  fof(f8,axiom,(
% 1.31/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 1.31/0.54  fof(f112,plain,(
% 1.31/0.54    ~r2_hidden(sK0,sK1)),
% 1.31/0.54    inference(subsumption_resolution,[],[f110,f52])).
% 1.31/0.54  fof(f110,plain,(
% 1.31/0.54    r1_tarski(sK1,sK0) | ~r2_hidden(sK0,sK1)),
% 1.31/0.54    inference(resolution,[],[f104,f81])).
% 1.31/0.54  fof(f81,plain,(
% 1.31/0.54    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,sK1)),
% 1.31/0.54    inference(resolution,[],[f42,f54])).
% 1.31/0.54  fof(f54,plain,(
% 1.31/0.54    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f32])).
% 1.31/0.54  % (31034)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.31/0.54  fof(f42,plain,(
% 1.31/0.54    ~r2_hidden(sK0,k1_ordinal1(sK1)) | ~r1_ordinal1(sK0,sK1)),
% 1.31/0.54    inference(cnf_transformation,[],[f24])).
% 1.31/0.54  fof(f104,plain,(
% 1.31/0.54    r1_ordinal1(sK0,sK1) | r1_tarski(sK1,sK0)),
% 1.31/0.54    inference(subsumption_resolution,[],[f103,f40])).
% 1.31/0.54  fof(f103,plain,(
% 1.31/0.54    r1_ordinal1(sK0,sK1) | r1_tarski(sK1,sK0) | ~v3_ordinal1(sK1)),
% 1.31/0.54    inference(subsumption_resolution,[],[f102,f39])).
% 1.31/0.54  fof(f102,plain,(
% 1.31/0.54    r1_ordinal1(sK0,sK1) | r1_tarski(sK1,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1)),
% 1.31/0.54    inference(resolution,[],[f89,f43])).
% 1.31/0.54  fof(f89,plain,(
% 1.31/0.54    r1_ordinal1(sK1,sK0) | r1_ordinal1(sK0,sK1)),
% 1.31/0.54    inference(resolution,[],[f75,f40])).
% 1.31/0.54  fof(f75,plain,(
% 1.31/0.54    ( ! [X1] : (~v3_ordinal1(X1) | r1_ordinal1(sK0,X1) | r1_ordinal1(X1,sK0)) )),
% 1.31/0.54    inference(resolution,[],[f39,f45])).
% 1.31/0.54  fof(f45,plain,(
% 1.31/0.54    ( ! [X0,X1] : (~v3_ordinal1(X1) | r1_ordinal1(X0,X1) | r1_ordinal1(X1,X0) | ~v3_ordinal1(X0)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f16])).
% 1.31/0.54  fof(f16,plain,(
% 1.31/0.54    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.31/0.54    inference(flattening,[],[f15])).
% 1.31/0.54  fof(f15,plain,(
% 1.31/0.54    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.31/0.54    inference(ennf_transformation,[],[f4])).
% 1.31/0.54  fof(f4,axiom,(
% 1.31/0.54    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 1.31/0.54  fof(f132,plain,(
% 1.31/0.54    ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 1.31/0.54    inference(subsumption_resolution,[],[f118,f90])).
% 1.31/0.54  fof(f90,plain,(
% 1.31/0.54    r1_ordinal1(sK0,sK0)),
% 1.31/0.54    inference(duplicate_literal_removal,[],[f88])).
% 1.31/0.54  fof(f88,plain,(
% 1.31/0.54    r1_ordinal1(sK0,sK0) | r1_ordinal1(sK0,sK0)),
% 1.31/0.54    inference(resolution,[],[f75,f39])).
% 1.31/0.54  fof(f118,plain,(
% 1.31/0.54    ~r1_ordinal1(sK0,sK0) | ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 1.31/0.54    inference(backward_demodulation,[],[f42,f115])).
% 1.31/0.54  % SZS output end Proof for theBenchmark
% 1.31/0.54  % (31049)------------------------------
% 1.31/0.54  % (31049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (31049)Termination reason: Refutation
% 1.31/0.54  
% 1.31/0.54  % (31049)Memory used [KB]: 1791
% 1.31/0.54  % (31049)Time elapsed: 0.068 s
% 1.31/0.54  % (31049)------------------------------
% 1.31/0.54  % (31049)------------------------------
% 1.31/0.54  % (31057)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.31/0.54  % (31028)Success in time 0.169 s
%------------------------------------------------------------------------------
