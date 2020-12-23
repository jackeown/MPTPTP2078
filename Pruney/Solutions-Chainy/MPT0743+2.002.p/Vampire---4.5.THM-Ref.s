%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 567 expanded)
%              Number of leaves         :   10 ( 152 expanded)
%              Depth                    :   20
%              Number of atoms          :  235 (2703 expanded)
%              Number of equality atoms :   19 (  62 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f353,plain,(
    $false ),
    inference(subsumption_resolution,[],[f352,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f352,plain,(
    r2_hidden(sK0,sK0) ),
    inference(forward_demodulation,[],[f351,f287])).

fof(f287,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f283,f276])).

fof(f276,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f275,f165])).

fof(f165,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 = sK1
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f136,f145])).

fof(f145,plain,
    ( r1_tarski(sK1,sK0)
    | r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f144,f54])).

fof(f54,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
      | ~ r2_hidden(sK0,sK1) )
    & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
      | r2_hidden(sK0,sK1) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).

fof(f33,plain,
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

fof(f34,plain,
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

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f144,plain,
    ( ~ v3_ordinal1(sK1)
    | r2_hidden(sK0,sK1)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f109,f124])).

fof(f124,plain,
    ( ~ r1_ordinal1(sK1,sK0)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f103,f54])).

fof(f103,plain,(
    ! [X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r1_ordinal1(X1,sK0)
      | r1_tarski(X1,sK0) ) ),
    inference(resolution,[],[f53,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f53,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f109,plain,(
    ! [X7] :
      ( r1_ordinal1(X7,sK0)
      | ~ v3_ordinal1(X7)
      | r2_hidden(sK0,X7) ) ),
    inference(resolution,[],[f53,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f136,plain,
    ( ~ r1_tarski(sK1,sK0)
    | r2_hidden(sK1,sK0)
    | sK0 = sK1 ),
    inference(resolution,[],[f135,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f135,plain,
    ( r1_tarski(sK0,sK1)
    | r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f134,f54])).

fof(f134,plain,
    ( ~ v3_ordinal1(sK1)
    | r2_hidden(sK1,sK0)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f108,f121])).

fof(f121,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f102,f54])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | ~ r1_ordinal1(sK0,X0)
      | r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f53,f57])).

fof(f108,plain,(
    ! [X6] :
      ( r1_ordinal1(sK0,X6)
      | ~ v3_ordinal1(X6)
      | r2_hidden(X6,sK0) ) ),
    inference(resolution,[],[f53,f60])).

fof(f275,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f273,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f273,plain,
    ( ~ r2_hidden(sK1,k1_ordinal1(sK0))
    | ~ r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f266,f67])).

fof(f266,plain,
    ( r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK1,k1_ordinal1(sK0)) ),
    inference(resolution,[],[f243,f55])).

fof(f55,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f243,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK1,k1_ordinal1(sK0)) ),
    inference(resolution,[],[f207,f53])).

fof(f207,plain,(
    ! [X3] :
      ( ~ v3_ordinal1(X3)
      | ~ r1_ordinal1(k1_ordinal1(X3),sK1)
      | ~ r2_hidden(sK1,k1_ordinal1(X3)) ) ),
    inference(resolution,[],[f153,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f153,plain,(
    ! [X0] :
      ( r1_tarski(k1_ordinal1(X0),sK1)
      | ~ r1_ordinal1(k1_ordinal1(X0),sK1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f111,f64])).

fof(f64,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f111,plain,(
    ! [X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r1_ordinal1(X1,sK1)
      | r1_tarski(X1,sK1) ) ),
    inference(resolution,[],[f54,f57])).

fof(f283,plain,
    ( sK0 = sK1
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f278,f213])).

fof(f213,plain,
    ( r2_hidden(sK1,k1_ordinal1(sK0))
    | ~ r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f212,f53])).

fof(f212,plain,
    ( r2_hidden(sK1,k1_ordinal1(sK0))
    | ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f163,f64])).

fof(f163,plain,
    ( ~ v3_ordinal1(k1_ordinal1(sK0))
    | r2_hidden(sK1,k1_ordinal1(sK0))
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f117,f56])).

fof(f56,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f117,plain,(
    ! [X7] :
      ( r1_ordinal1(X7,sK1)
      | ~ v3_ordinal1(X7)
      | r2_hidden(sK1,X7) ) ),
    inference(resolution,[],[f54,f60])).

fof(f278,plain,
    ( ~ r2_hidden(sK1,k1_ordinal1(sK0))
    | sK0 = sK1 ),
    inference(resolution,[],[f275,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | X0 = X1
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f351,plain,(
    r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f289,f227])).

fof(f227,plain,(
    ~ r1_ordinal1(k1_ordinal1(sK0),sK0) ),
    inference(subsumption_resolution,[],[f225,f90])).

fof(f90,plain,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f225,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK0)
    | ~ r2_hidden(sK0,k1_ordinal1(sK0)) ),
    inference(resolution,[],[f189,f53])).

fof(f189,plain,(
    ! [X3] :
      ( ~ v3_ordinal1(X3)
      | ~ r1_ordinal1(k1_ordinal1(X3),sK0)
      | ~ r2_hidden(sK0,k1_ordinal1(X3)) ) ),
    inference(resolution,[],[f122,f66])).

fof(f122,plain,(
    ! [X0] :
      ( r1_tarski(k1_ordinal1(X0),sK0)
      | ~ r1_ordinal1(k1_ordinal1(X0),sK0)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f103,f64])).

fof(f289,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK0)
    | r2_hidden(sK0,sK1) ),
    inference(backward_demodulation,[],[f55,f287])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:00:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (22608)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.52  % (22600)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (22589)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (22590)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (22592)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (22594)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (22595)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (22605)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.54  % (22588)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (22597)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.54  % (22585)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (22586)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (22587)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.55  % (22604)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (22614)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (22613)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (22595)Refutation not found, incomplete strategy% (22595)------------------------------
% 0.22/0.55  % (22595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (22595)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (22595)Memory used [KB]: 10874
% 0.22/0.55  % (22595)Time elapsed: 0.133 s
% 0.22/0.55  % (22595)------------------------------
% 0.22/0.55  % (22595)------------------------------
% 0.22/0.55  % (22609)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.55  % (22612)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (22611)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (22591)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (22601)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (22603)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.56  % (22606)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.56  % (22610)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.56  % (22601)Refutation not found, incomplete strategy% (22601)------------------------------
% 0.22/0.56  % (22601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (22601)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (22601)Memory used [KB]: 10746
% 0.22/0.56  % (22601)Time elapsed: 0.139 s
% 0.22/0.56  % (22601)------------------------------
% 0.22/0.56  % (22601)------------------------------
% 0.22/0.56  % (22603)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f353,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(subsumption_resolution,[],[f352,f67])).
% 0.22/0.56  fof(f67,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.22/0.56  fof(f352,plain,(
% 0.22/0.56    r2_hidden(sK0,sK0)),
% 0.22/0.56    inference(forward_demodulation,[],[f351,f287])).
% 0.22/0.56  fof(f287,plain,(
% 0.22/0.56    sK0 = sK1),
% 0.22/0.56    inference(subsumption_resolution,[],[f283,f276])).
% 0.22/0.56  fof(f276,plain,(
% 0.22/0.56    r2_hidden(sK0,sK1) | sK0 = sK1),
% 0.22/0.56    inference(resolution,[],[f275,f165])).
% 0.22/0.56  fof(f165,plain,(
% 0.22/0.56    r2_hidden(sK1,sK0) | sK0 = sK1 | r2_hidden(sK0,sK1)),
% 0.22/0.56    inference(resolution,[],[f136,f145])).
% 0.22/0.56  fof(f145,plain,(
% 0.22/0.56    r1_tarski(sK1,sK0) | r2_hidden(sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f144,f54])).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    v3_ordinal1(sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f35])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.56    inference(flattening,[],[f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.56    inference(nnf_transformation,[],[f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f17])).
% 0.22/0.56  fof(f17,negated_conjecture,(
% 0.22/0.56    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.22/0.56    inference(negated_conjecture,[],[f16])).
% 0.22/0.56  fof(f16,conjecture,(
% 0.22/0.56    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).
% 0.22/0.56  fof(f144,plain,(
% 0.22/0.56    ~v3_ordinal1(sK1) | r2_hidden(sK0,sK1) | r1_tarski(sK1,sK0)),
% 0.22/0.56    inference(resolution,[],[f109,f124])).
% 0.22/0.56  fof(f124,plain,(
% 0.22/0.56    ~r1_ordinal1(sK1,sK0) | r1_tarski(sK1,sK0)),
% 0.22/0.56    inference(resolution,[],[f103,f54])).
% 0.22/0.56  fof(f103,plain,(
% 0.22/0.56    ( ! [X1] : (~v3_ordinal1(X1) | ~r1_ordinal1(X1,sK0) | r1_tarski(X1,sK0)) )),
% 0.22/0.56    inference(resolution,[],[f53,f57])).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~v3_ordinal1(X0) | ~r1_ordinal1(X0,X1) | r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.56    inference(nnf_transformation,[],[f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.56    inference(flattening,[],[f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,axiom,(
% 0.22/0.56    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    v3_ordinal1(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f35])).
% 0.22/0.56  fof(f109,plain,(
% 0.22/0.56    ( ! [X7] : (r1_ordinal1(X7,sK0) | ~v3_ordinal1(X7) | r2_hidden(sK0,X7)) )),
% 0.22/0.56    inference(resolution,[],[f53,f60])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_ordinal1(X0,X1) | r2_hidden(X1,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.56    inference(flattening,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,axiom,(
% 0.22/0.56    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.22/0.56  fof(f136,plain,(
% 0.22/0.56    ~r1_tarski(sK1,sK0) | r2_hidden(sK1,sK0) | sK0 = sK1),
% 0.22/0.56    inference(resolution,[],[f135,f73])).
% 0.22/0.56  fof(f73,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.56    inference(flattening,[],[f41])).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.56    inference(nnf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.56  fof(f135,plain,(
% 0.22/0.56    r1_tarski(sK0,sK1) | r2_hidden(sK1,sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f134,f54])).
% 0.22/0.56  fof(f134,plain,(
% 0.22/0.56    ~v3_ordinal1(sK1) | r2_hidden(sK1,sK0) | r1_tarski(sK0,sK1)),
% 0.22/0.56    inference(resolution,[],[f108,f121])).
% 0.22/0.56  fof(f121,plain,(
% 0.22/0.56    ~r1_ordinal1(sK0,sK1) | r1_tarski(sK0,sK1)),
% 0.22/0.56    inference(resolution,[],[f102,f54])).
% 0.22/0.56  fof(f102,plain,(
% 0.22/0.56    ( ! [X0] : (~v3_ordinal1(X0) | ~r1_ordinal1(sK0,X0) | r1_tarski(sK0,X0)) )),
% 0.22/0.56    inference(resolution,[],[f53,f57])).
% 0.22/0.56  fof(f108,plain,(
% 0.22/0.56    ( ! [X6] : (r1_ordinal1(sK0,X6) | ~v3_ordinal1(X6) | r2_hidden(X6,sK0)) )),
% 0.22/0.56    inference(resolution,[],[f53,f60])).
% 0.22/0.56  fof(f275,plain,(
% 0.22/0.56    ~r2_hidden(sK1,sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f273,f62])).
% 0.22/0.56  fof(f62,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f38])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.22/0.56    inference(flattening,[],[f37])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.22/0.56    inference(nnf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,axiom,(
% 0.22/0.56    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.22/0.56  fof(f273,plain,(
% 0.22/0.56    ~r2_hidden(sK1,k1_ordinal1(sK0)) | ~r2_hidden(sK1,sK0)),
% 0.22/0.56    inference(resolution,[],[f266,f67])).
% 0.22/0.56  fof(f266,plain,(
% 0.22/0.56    r2_hidden(sK0,sK1) | ~r2_hidden(sK1,k1_ordinal1(sK0))),
% 0.22/0.56    inference(resolution,[],[f243,f55])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f35])).
% 0.22/0.56  fof(f243,plain,(
% 0.22/0.56    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK1,k1_ordinal1(sK0))),
% 0.22/0.56    inference(resolution,[],[f207,f53])).
% 0.22/0.56  fof(f207,plain,(
% 0.22/0.56    ( ! [X3] : (~v3_ordinal1(X3) | ~r1_ordinal1(k1_ordinal1(X3),sK1) | ~r2_hidden(sK1,k1_ordinal1(X3))) )),
% 0.22/0.56    inference(resolution,[],[f153,f66])).
% 0.22/0.56  fof(f66,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f15])).
% 0.22/0.56  fof(f15,axiom,(
% 0.22/0.56    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.56  fof(f153,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(k1_ordinal1(X0),sK1) | ~r1_ordinal1(k1_ordinal1(X0),sK1) | ~v3_ordinal1(X0)) )),
% 0.22/0.56    inference(resolution,[],[f111,f64])).
% 0.22/0.56  fof(f64,plain,(
% 0.22/0.56    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,axiom,(
% 0.22/0.56    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.22/0.56  fof(f111,plain,(
% 0.22/0.56    ( ! [X1] : (~v3_ordinal1(X1) | ~r1_ordinal1(X1,sK1) | r1_tarski(X1,sK1)) )),
% 0.22/0.56    inference(resolution,[],[f54,f57])).
% 0.22/0.56  fof(f283,plain,(
% 0.22/0.56    sK0 = sK1 | ~r2_hidden(sK0,sK1)),
% 0.22/0.56    inference(resolution,[],[f278,f213])).
% 0.22/0.56  fof(f213,plain,(
% 0.22/0.56    r2_hidden(sK1,k1_ordinal1(sK0)) | ~r2_hidden(sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f212,f53])).
% 0.22/0.56  fof(f212,plain,(
% 0.22/0.56    r2_hidden(sK1,k1_ordinal1(sK0)) | ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.22/0.56    inference(resolution,[],[f163,f64])).
% 0.22/0.56  fof(f163,plain,(
% 0.22/0.56    ~v3_ordinal1(k1_ordinal1(sK0)) | r2_hidden(sK1,k1_ordinal1(sK0)) | ~r2_hidden(sK0,sK1)),
% 0.22/0.56    inference(resolution,[],[f117,f56])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f35])).
% 0.22/0.56  fof(f117,plain,(
% 0.22/0.56    ( ! [X7] : (r1_ordinal1(X7,sK1) | ~v3_ordinal1(X7) | r2_hidden(sK1,X7)) )),
% 0.22/0.56    inference(resolution,[],[f54,f60])).
% 0.22/0.56  fof(f278,plain,(
% 0.22/0.56    ~r2_hidden(sK1,k1_ordinal1(sK0)) | sK0 = sK1),
% 0.22/0.56    inference(resolution,[],[f275,f61])).
% 0.22/0.56  fof(f61,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r2_hidden(X0,X1) | X0 = X1 | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f38])).
% 0.22/0.56  fof(f351,plain,(
% 0.22/0.56    r2_hidden(sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f289,f227])).
% 0.22/0.56  fof(f227,plain,(
% 0.22/0.56    ~r1_ordinal1(k1_ordinal1(sK0),sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f225,f90])).
% 0.22/0.56  fof(f90,plain,(
% 0.22/0.56    ( ! [X1] : (r2_hidden(X1,k1_ordinal1(X1))) )),
% 0.22/0.56    inference(equality_resolution,[],[f63])).
% 0.22/0.56  fof(f63,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f38])).
% 0.22/0.56  fof(f225,plain,(
% 0.22/0.56    ~r1_ordinal1(k1_ordinal1(sK0),sK0) | ~r2_hidden(sK0,k1_ordinal1(sK0))),
% 0.22/0.56    inference(resolution,[],[f189,f53])).
% 0.22/0.56  fof(f189,plain,(
% 0.22/0.56    ( ! [X3] : (~v3_ordinal1(X3) | ~r1_ordinal1(k1_ordinal1(X3),sK0) | ~r2_hidden(sK0,k1_ordinal1(X3))) )),
% 0.22/0.56    inference(resolution,[],[f122,f66])).
% 0.22/0.56  fof(f122,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(k1_ordinal1(X0),sK0) | ~r1_ordinal1(k1_ordinal1(X0),sK0) | ~v3_ordinal1(X0)) )),
% 0.22/0.56    inference(resolution,[],[f103,f64])).
% 0.22/0.56  fof(f289,plain,(
% 0.22/0.56    r1_ordinal1(k1_ordinal1(sK0),sK0) | r2_hidden(sK0,sK1)),
% 0.22/0.56    inference(backward_demodulation,[],[f55,f287])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (22603)------------------------------
% 0.22/0.56  % (22603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (22603)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (22603)Memory used [KB]: 1791
% 0.22/0.56  % (22603)Time elapsed: 0.142 s
% 0.22/0.56  % (22603)------------------------------
% 0.22/0.56  % (22603)------------------------------
% 0.22/0.56  % (22584)Success in time 0.193 s
%------------------------------------------------------------------------------
