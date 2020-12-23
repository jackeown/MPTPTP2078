%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   77 (1615 expanded)
%              Number of leaves         :   10 ( 434 expanded)
%              Depth                    :   23
%              Number of atoms          :  235 (7782 expanded)
%              Number of equality atoms :   19 ( 174 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f271,plain,(
    $false ),
    inference(subsumption_resolution,[],[f270,f84])).

fof(f84,plain,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f270,plain,(
    ~ r2_hidden(sK0,k1_ordinal1(sK0)) ),
    inference(forward_demodulation,[],[f269,f196])).

fof(f196,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f195,f184])).

fof(f184,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f182,f168])).

fof(f168,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f167,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

% (10739)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f167,plain,
    ( r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f139,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f139,plain,
    ( ~ r2_hidden(sK1,k1_ordinal1(sK0))
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f126,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f126,plain,
    ( r1_tarski(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f125,f53])).

fof(f53,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
      | ~ r2_hidden(sK0,sK1) )
    & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
      | r2_hidden(sK0,sK1) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | r2_hidden(X0,X1) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(sK0),X1)
            | ~ r2_hidden(sK0,X1) )
          & ( r1_ordinal1(k1_ordinal1(sK0),X1)
            | r2_hidden(sK0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(k1_ordinal1(sK0),X1)
          | ~ r2_hidden(sK0,X1) )
        & ( r1_ordinal1(k1_ordinal1(sK0),X1)
          | r2_hidden(sK0,X1) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
        | ~ r2_hidden(sK0,sK1) )
      & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
        | r2_hidden(sK0,sK1) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f125,plain,
    ( r1_tarski(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f100,f64])).

fof(f64,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f100,plain,
    ( ~ v3_ordinal1(k1_ordinal1(sK0))
    | r1_tarski(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f99,f54])).

fof(f54,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f99,plain,
    ( r2_hidden(sK0,sK1)
    | r1_tarski(k1_ordinal1(sK0),sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k1_ordinal1(sK0)) ),
    inference(resolution,[],[f55,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f55,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f182,plain,
    ( ~ r2_hidden(sK0,sK1)
    | r2_hidden(sK1,sK0)
    | sK0 = sK1 ),
    inference(resolution,[],[f175,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_ordinal1(X1))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f175,plain,
    ( r2_hidden(sK1,k1_ordinal1(sK0))
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f161,f56])).

fof(f56,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f161,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK1,k1_ordinal1(sK0)) ),
    inference(resolution,[],[f112,f53])).

fof(f112,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r1_ordinal1(k1_ordinal1(X0),sK1)
      | r2_hidden(sK1,k1_ordinal1(X0)) ) ),
    inference(resolution,[],[f97,f64])).

fof(f97,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r2_hidden(sK1,X0)
      | r1_ordinal1(X0,sK1) ) ),
    inference(resolution,[],[f54,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f195,plain,
    ( sK0 = sK1
    | r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f194,f168])).

fof(f194,plain,
    ( sK0 = sK1
    | r2_hidden(sK0,sK1)
    | r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f133,f132])).

fof(f132,plain,
    ( r1_tarski(sK0,sK1)
    | r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f131,f53])).

fof(f131,plain,
    ( r2_hidden(sK1,sK0)
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f130,f54])).

fof(f130,plain,
    ( r2_hidden(sK1,sK0)
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f113,f57])).

fof(f113,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f97,f53])).

fof(f133,plain,
    ( ~ r1_tarski(sK0,sK1)
    | sK0 = sK1
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f124,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f124,plain,
    ( r1_tarski(sK1,sK0)
    | r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f123,f54])).

fof(f123,plain,
    ( r2_hidden(sK0,sK1)
    | r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(subsumption_resolution,[],[f122,f53])).

fof(f122,plain,
    ( r2_hidden(sK0,sK1)
    | r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f104,f57])).

fof(f104,plain,
    ( r1_ordinal1(sK1,sK0)
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f94,f54])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r2_hidden(sK0,X0)
      | r1_ordinal1(X0,sK0) ) ),
    inference(resolution,[],[f53,f60])).

fof(f269,plain,(
    ~ r2_hidden(sK1,k1_ordinal1(sK0)) ),
    inference(subsumption_resolution,[],[f218,f248])).

fof(f248,plain,(
    ~ r2_hidden(sK0,sK0) ),
    inference(forward_demodulation,[],[f247,f196])).

fof(f247,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f199,f246])).

fof(f246,plain,(
    r1_ordinal1(k1_ordinal1(sK0),sK0) ),
    inference(subsumption_resolution,[],[f245,f77])).

fof(f245,plain,
    ( r2_hidden(sK0,sK0)
    | r1_ordinal1(k1_ordinal1(sK0),sK0) ),
    inference(forward_demodulation,[],[f198,f196])).

fof(f198,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK0)
    | r2_hidden(sK0,sK1) ),
    inference(backward_demodulation,[],[f55,f196])).

fof(f199,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK0)
    | ~ r2_hidden(sK0,sK1) ),
    inference(backward_demodulation,[],[f56,f196])).

fof(f218,plain,
    ( r2_hidden(sK0,sK0)
    | ~ r2_hidden(sK1,k1_ordinal1(sK0)) ),
    inference(backward_demodulation,[],[f139,f196])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:07:12 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (10766)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (10742)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (10738)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.51  % (10751)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.51  % (10744)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.51  % (10751)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (10746)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.51  % (10743)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (10753)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f271,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f270,f84])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    ( ! [X1] : (r2_hidden(X1,k1_ordinal1(X1))) )),
% 0.22/0.51    inference(equality_resolution,[],[f63])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.22/0.51    inference(flattening,[],[f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.22/0.51    inference(nnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.22/0.51  fof(f270,plain,(
% 0.22/0.51    ~r2_hidden(sK0,k1_ordinal1(sK0))),
% 0.22/0.51    inference(forward_demodulation,[],[f269,f196])).
% 0.22/0.51  fof(f196,plain,(
% 0.22/0.51    sK0 = sK1),
% 0.22/0.51    inference(subsumption_resolution,[],[f195,f184])).
% 0.22/0.52  fof(f184,plain,(
% 0.22/0.52    ~r2_hidden(sK0,sK1) | sK0 = sK1),
% 0.22/0.52    inference(subsumption_resolution,[],[f182,f168])).
% 0.22/0.52  fof(f168,plain,(
% 0.22/0.52    ~r2_hidden(sK1,sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f167,f77])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f28])).
% 0.22/0.52  % (10739)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.22/0.52  fof(f167,plain,(
% 0.22/0.52    r2_hidden(sK0,sK1) | ~r2_hidden(sK1,sK0)),
% 0.22/0.52    inference(resolution,[],[f139,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f41])).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    ~r2_hidden(sK1,k1_ordinal1(sK0)) | r2_hidden(sK0,sK1)),
% 0.22/0.52    inference(resolution,[],[f126,f72])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,axiom,(
% 0.22/0.52    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    r1_tarski(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f125,f53])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    v3_ordinal1(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.52    inference(flattening,[],[f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,negated_conjecture,(
% 0.22/0.52    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.22/0.52    inference(negated_conjecture,[],[f15])).
% 0.22/0.52  fof(f15,conjecture,(
% 0.22/0.52    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).
% 0.22/0.52  fof(f125,plain,(
% 0.22/0.52    r1_tarski(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.22/0.52    inference(resolution,[],[f100,f64])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,axiom,(
% 0.22/0.52    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.22/0.52  fof(f100,plain,(
% 0.22/0.52    ~v3_ordinal1(k1_ordinal1(sK0)) | r1_tarski(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f99,f54])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    v3_ordinal1(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    r2_hidden(sK0,sK1) | r1_tarski(k1_ordinal1(sK0),sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(k1_ordinal1(sK0))),
% 0.22/0.52    inference(resolution,[],[f55,f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.52    inference(flattening,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f182,plain,(
% 0.22/0.52    ~r2_hidden(sK0,sK1) | r2_hidden(sK1,sK0) | sK0 = sK1),
% 0.22/0.52    inference(resolution,[],[f175,f61])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k1_ordinal1(X1)) | r2_hidden(X0,X1) | X0 = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f41])).
% 0.22/0.52  fof(f175,plain,(
% 0.22/0.52    r2_hidden(sK1,k1_ordinal1(sK0)) | ~r2_hidden(sK0,sK1)),
% 0.22/0.52    inference(resolution,[],[f161,f56])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f161,plain,(
% 0.22/0.52    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK1,k1_ordinal1(sK0))),
% 0.22/0.52    inference(resolution,[],[f112,f53])).
% 0.22/0.52  fof(f112,plain,(
% 0.22/0.52    ( ! [X0] : (~v3_ordinal1(X0) | r1_ordinal1(k1_ordinal1(X0),sK1) | r2_hidden(sK1,k1_ordinal1(X0))) )),
% 0.22/0.52    inference(resolution,[],[f97,f64])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    ( ! [X0] : (~v3_ordinal1(X0) | r2_hidden(sK1,X0) | r1_ordinal1(X0,sK1)) )),
% 0.22/0.52    inference(resolution,[],[f54,f60])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v3_ordinal1(X1) | r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.52    inference(flattening,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.22/0.52  fof(f195,plain,(
% 0.22/0.52    sK0 = sK1 | r2_hidden(sK0,sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f194,f168])).
% 0.22/0.52  fof(f194,plain,(
% 0.22/0.52    sK0 = sK1 | r2_hidden(sK0,sK1) | r2_hidden(sK1,sK0)),
% 0.22/0.52    inference(resolution,[],[f133,f132])).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    r1_tarski(sK0,sK1) | r2_hidden(sK1,sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f131,f53])).
% 0.22/0.52  fof(f131,plain,(
% 0.22/0.52    r2_hidden(sK1,sK0) | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f130,f54])).
% 0.22/0.52  fof(f130,plain,(
% 0.22/0.52    r2_hidden(sK1,sK0) | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0)),
% 0.22/0.52    inference(resolution,[],[f113,f57])).
% 0.22/0.52  fof(f113,plain,(
% 0.22/0.52    r1_ordinal1(sK0,sK1) | r2_hidden(sK1,sK0)),
% 0.22/0.52    inference(resolution,[],[f97,f53])).
% 0.22/0.52  fof(f133,plain,(
% 0.22/0.52    ~r1_tarski(sK0,sK1) | sK0 = sK1 | r2_hidden(sK0,sK1)),
% 0.22/0.52    inference(resolution,[],[f124,f82])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f52])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(flattening,[],[f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.52  fof(f124,plain,(
% 0.22/0.52    r1_tarski(sK1,sK0) | r2_hidden(sK0,sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f123,f54])).
% 0.22/0.52  fof(f123,plain,(
% 0.22/0.52    r2_hidden(sK0,sK1) | r1_tarski(sK1,sK0) | ~v3_ordinal1(sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f122,f53])).
% 0.22/0.52  fof(f122,plain,(
% 0.22/0.52    r2_hidden(sK0,sK1) | r1_tarski(sK1,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1)),
% 0.22/0.52    inference(resolution,[],[f104,f57])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    r1_ordinal1(sK1,sK0) | r2_hidden(sK0,sK1)),
% 0.22/0.52    inference(resolution,[],[f94,f54])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    ( ! [X0] : (~v3_ordinal1(X0) | r2_hidden(sK0,X0) | r1_ordinal1(X0,sK0)) )),
% 0.22/0.52    inference(resolution,[],[f53,f60])).
% 0.22/0.52  fof(f269,plain,(
% 0.22/0.52    ~r2_hidden(sK1,k1_ordinal1(sK0))),
% 0.22/0.52    inference(subsumption_resolution,[],[f218,f248])).
% 0.22/0.52  fof(f248,plain,(
% 0.22/0.52    ~r2_hidden(sK0,sK0)),
% 0.22/0.52    inference(forward_demodulation,[],[f247,f196])).
% 0.22/0.52  fof(f247,plain,(
% 0.22/0.52    ~r2_hidden(sK0,sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f199,f246])).
% 0.22/0.52  fof(f246,plain,(
% 0.22/0.52    r1_ordinal1(k1_ordinal1(sK0),sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f245,f77])).
% 0.22/0.52  fof(f245,plain,(
% 0.22/0.52    r2_hidden(sK0,sK0) | r1_ordinal1(k1_ordinal1(sK0),sK0)),
% 0.22/0.52    inference(forward_demodulation,[],[f198,f196])).
% 0.22/0.52  fof(f198,plain,(
% 0.22/0.52    r1_ordinal1(k1_ordinal1(sK0),sK0) | r2_hidden(sK0,sK1)),
% 0.22/0.52    inference(backward_demodulation,[],[f55,f196])).
% 0.22/0.52  fof(f199,plain,(
% 0.22/0.52    ~r1_ordinal1(k1_ordinal1(sK0),sK0) | ~r2_hidden(sK0,sK1)),
% 0.22/0.52    inference(backward_demodulation,[],[f56,f196])).
% 0.22/0.52  fof(f218,plain,(
% 0.22/0.52    r2_hidden(sK0,sK0) | ~r2_hidden(sK1,k1_ordinal1(sK0))),
% 0.22/0.52    inference(backward_demodulation,[],[f139,f196])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (10751)------------------------------
% 0.22/0.52  % (10751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (10751)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (10751)Memory used [KB]: 1791
% 0.22/0.52  % (10751)Time elapsed: 0.094 s
% 0.22/0.52  % (10751)------------------------------
% 0.22/0.52  % (10751)------------------------------
% 0.22/0.52  % (10745)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (10736)Success in time 0.148 s
%------------------------------------------------------------------------------
