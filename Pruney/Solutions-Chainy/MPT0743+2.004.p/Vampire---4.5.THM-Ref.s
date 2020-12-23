%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
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
fof(f276,plain,(
    $false ),
    inference(subsumption_resolution,[],[f275,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

% (6466)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% (6476)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
fof(f275,plain,(
    r2_hidden(sK0,sK0) ),
    inference(forward_demodulation,[],[f274,f221])).

fof(f221,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f217,f208])).

fof(f208,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f207,f133])).

fof(f133,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 = sK1
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f107,f114])).

fof(f114,plain,
    ( r1_tarski(sK1,sK0)
    | r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f113,f42])).

fof(f42,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
      | ~ r2_hidden(sK0,sK1) )
    & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
      | r2_hidden(sK0,sK1) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f29,f28])).

fof(f28,plain,
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

fof(f29,plain,
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

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f113,plain,
    ( ~ v3_ordinal1(sK1)
    | r2_hidden(sK0,sK1)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f81,f96])).

fof(f96,plain,
    ( ~ r1_ordinal1(sK1,sK0)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f75,f42])).

fof(f75,plain,(
    ! [X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r1_ordinal1(X1,sK0)
      | r1_tarski(X1,sK0) ) ),
    inference(resolution,[],[f41,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f41,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f81,plain,(
    ! [X7] :
      ( r1_ordinal1(X7,sK0)
      | ~ v3_ordinal1(X7)
      | r2_hidden(sK0,X7) ) ),
    inference(resolution,[],[f41,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f107,plain,
    ( ~ r1_tarski(sK1,sK0)
    | r2_hidden(sK1,sK0)
    | sK0 = sK1 ),
    inference(resolution,[],[f106,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f106,plain,
    ( r1_tarski(sK0,sK1)
    | r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f105,f42])).

fof(f105,plain,
    ( ~ v3_ordinal1(sK1)
    | r2_hidden(sK1,sK0)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f80,f93])).

fof(f93,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f74,f42])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | ~ r1_ordinal1(sK0,X0)
      | r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f41,f45])).

fof(f80,plain,(
    ! [X6] :
      ( r1_ordinal1(sK0,X6)
      | ~ v3_ordinal1(X6)
      | r2_hidden(X6,sK0) ) ),
    inference(resolution,[],[f41,f48])).

fof(f207,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f205,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f205,plain,
    ( ~ r2_hidden(sK1,k1_ordinal1(sK0))
    | ~ r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f201,f55])).

fof(f201,plain,
    ( r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK1,k1_ordinal1(sK0)) ),
    inference(resolution,[],[f190,f43])).

fof(f43,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f190,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK1,k1_ordinal1(sK0)) ),
    inference(resolution,[],[f150,f41])).

fof(f150,plain,(
    ! [X2] :
      ( ~ v3_ordinal1(X2)
      | ~ r1_ordinal1(k1_ordinal1(X2),sK1)
      | ~ r2_hidden(sK1,k1_ordinal1(X2)) ) ),
    inference(resolution,[],[f121,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f121,plain,(
    ! [X0] :
      ( r1_tarski(k1_ordinal1(X0),sK1)
      | ~ r1_ordinal1(k1_ordinal1(X0),sK1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f83,f52])).

fof(f52,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f83,plain,(
    ! [X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r1_ordinal1(X1,sK1)
      | r1_tarski(X1,sK1) ) ),
    inference(resolution,[],[f42,f45])).

fof(f217,plain,
    ( sK0 = sK1
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f210,f155])).

fof(f155,plain,
    ( r2_hidden(sK1,k1_ordinal1(sK0))
    | ~ r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f154,f41])).

fof(f154,plain,
    ( r2_hidden(sK1,k1_ordinal1(sK0))
    | ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f131,f52])).

fof(f131,plain,
    ( ~ v3_ordinal1(k1_ordinal1(sK0))
    | r2_hidden(sK1,k1_ordinal1(sK0))
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f89,f44])).

fof(f44,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f89,plain,(
    ! [X7] :
      ( r1_ordinal1(X7,sK1)
      | ~ v3_ordinal1(X7)
      | r2_hidden(sK1,X7) ) ),
    inference(resolution,[],[f42,f48])).

fof(f210,plain,
    ( ~ r2_hidden(sK1,k1_ordinal1(sK0))
    | sK0 = sK1 ),
    inference(resolution,[],[f207,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | X0 = X1
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f274,plain,(
    r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f223,f172])).

fof(f172,plain,(
    ~ r1_ordinal1(k1_ordinal1(sK0),sK0) ),
    inference(subsumption_resolution,[],[f170,f68])).

fof(f68,plain,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

% (6467)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
fof(f170,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK0)
    | ~ r2_hidden(sK0,k1_ordinal1(sK0)) ),
    inference(resolution,[],[f144,f41])).

fof(f144,plain,(
    ! [X2] :
      ( ~ v3_ordinal1(X2)
      | ~ r1_ordinal1(k1_ordinal1(X2),sK0)
      | ~ r2_hidden(sK0,k1_ordinal1(X2)) ) ),
    inference(resolution,[],[f94,f54])).

fof(f94,plain,(
    ! [X0] :
      ( r1_tarski(k1_ordinal1(X0),sK0)
      | ~ r1_ordinal1(k1_ordinal1(X0),sK0)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f75,f52])).

fof(f223,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK0)
    | r2_hidden(sK0,sK1) ),
    inference(backward_demodulation,[],[f43,f221])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:32:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.57  % (6463)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.58  % (6472)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.58  % (6471)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.58  % (6464)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.58  % (6471)Refutation found. Thanks to Tanya!
% 0.22/0.58  % SZS status Theorem for theBenchmark
% 0.22/0.58  % (6453)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.58  % (6480)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.58  % (6463)Refutation not found, incomplete strategy% (6463)------------------------------
% 0.22/0.58  % (6463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (6479)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.60  % (6456)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.60  % (6455)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.60  % (6457)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.60  % (6454)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.61  % (6458)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.61  % (6463)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.61  
% 0.22/0.61  % (6463)Memory used [KB]: 10746
% 0.22/0.61  % (6463)Time elapsed: 0.141 s
% 0.22/0.61  % (6463)------------------------------
% 0.22/0.61  % (6463)------------------------------
% 0.22/0.61  % SZS output start Proof for theBenchmark
% 0.22/0.61  fof(f276,plain,(
% 0.22/0.61    $false),
% 0.22/0.61    inference(subsumption_resolution,[],[f275,f55])).
% 0.22/0.61  fof(f55,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f25])).
% 0.22/0.61  fof(f25,plain,(
% 0.22/0.61    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.61    inference(ennf_transformation,[],[f1])).
% 0.22/0.61  fof(f1,axiom,(
% 0.22/0.61    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.22/0.61  % (6466)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.61  % (6476)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.61  fof(f275,plain,(
% 0.22/0.61    r2_hidden(sK0,sK0)),
% 0.22/0.61    inference(forward_demodulation,[],[f274,f221])).
% 0.22/0.61  fof(f221,plain,(
% 0.22/0.61    sK0 = sK1),
% 0.22/0.61    inference(subsumption_resolution,[],[f217,f208])).
% 0.22/0.61  fof(f208,plain,(
% 0.22/0.61    r2_hidden(sK0,sK1) | sK0 = sK1),
% 0.22/0.61    inference(resolution,[],[f207,f133])).
% 0.22/0.61  fof(f133,plain,(
% 0.22/0.61    r2_hidden(sK1,sK0) | sK0 = sK1 | r2_hidden(sK0,sK1)),
% 0.22/0.61    inference(resolution,[],[f107,f114])).
% 0.22/0.61  fof(f114,plain,(
% 0.22/0.61    r1_tarski(sK1,sK0) | r2_hidden(sK0,sK1)),
% 0.22/0.61    inference(subsumption_resolution,[],[f113,f42])).
% 0.22/0.61  fof(f42,plain,(
% 0.22/0.61    v3_ordinal1(sK1)),
% 0.22/0.61    inference(cnf_transformation,[],[f30])).
% 0.22/0.61  fof(f30,plain,(
% 0.22/0.61    ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.22/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f29,f28])).
% 0.22/0.61  fof(f28,plain,(
% 0.22/0.61    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.22/0.61    introduced(choice_axiom,[])).
% 0.22/0.61  fof(f29,plain,(
% 0.22/0.61    ? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1))),
% 0.22/0.61    introduced(choice_axiom,[])).
% 0.22/0.61  fof(f27,plain,(
% 0.22/0.61    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.61    inference(flattening,[],[f26])).
% 0.22/0.61  fof(f26,plain,(
% 0.22/0.61    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.61    inference(nnf_transformation,[],[f16])).
% 0.22/0.61  fof(f16,plain,(
% 0.22/0.61    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.61    inference(ennf_transformation,[],[f15])).
% 0.22/0.61  fof(f15,negated_conjecture,(
% 0.22/0.61    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.22/0.61    inference(negated_conjecture,[],[f14])).
% 0.22/0.61  fof(f14,conjecture,(
% 0.22/0.61    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).
% 0.22/0.61  fof(f113,plain,(
% 0.22/0.61    ~v3_ordinal1(sK1) | r2_hidden(sK0,sK1) | r1_tarski(sK1,sK0)),
% 0.22/0.61    inference(resolution,[],[f81,f96])).
% 0.22/0.61  fof(f96,plain,(
% 0.22/0.61    ~r1_ordinal1(sK1,sK0) | r1_tarski(sK1,sK0)),
% 0.22/0.61    inference(resolution,[],[f75,f42])).
% 0.22/0.61  fof(f75,plain,(
% 0.22/0.61    ( ! [X1] : (~v3_ordinal1(X1) | ~r1_ordinal1(X1,sK0) | r1_tarski(X1,sK0)) )),
% 0.22/0.61    inference(resolution,[],[f41,f45])).
% 0.22/0.61  fof(f45,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~v3_ordinal1(X0) | ~r1_ordinal1(X0,X1) | r1_tarski(X0,X1)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f31])).
% 0.22/0.61  fof(f31,plain,(
% 0.22/0.61    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.61    inference(nnf_transformation,[],[f18])).
% 0.22/0.61  fof(f18,plain,(
% 0.22/0.61    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.61    inference(flattening,[],[f17])).
% 0.22/0.61  fof(f17,plain,(
% 0.22/0.61    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.22/0.61    inference(ennf_transformation,[],[f9])).
% 0.22/0.61  fof(f9,axiom,(
% 0.22/0.61    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.22/0.61  fof(f41,plain,(
% 0.22/0.61    v3_ordinal1(sK0)),
% 0.22/0.61    inference(cnf_transformation,[],[f30])).
% 0.22/0.61  fof(f81,plain,(
% 0.22/0.61    ( ! [X7] : (r1_ordinal1(X7,sK0) | ~v3_ordinal1(X7) | r2_hidden(sK0,X7)) )),
% 0.22/0.61    inference(resolution,[],[f41,f48])).
% 0.22/0.61  fof(f48,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_ordinal1(X0,X1) | r2_hidden(X1,X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f22])).
% 0.22/0.61  fof(f22,plain,(
% 0.22/0.61    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.61    inference(flattening,[],[f21])).
% 0.22/0.61  fof(f21,plain,(
% 0.22/0.61    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.61    inference(ennf_transformation,[],[f11])).
% 0.22/0.61  fof(f11,axiom,(
% 0.22/0.61    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.22/0.61  fof(f107,plain,(
% 0.22/0.61    ~r1_tarski(sK1,sK0) | r2_hidden(sK1,sK0) | sK0 = sK1),
% 0.22/0.61    inference(resolution,[],[f106,f58])).
% 0.22/0.61  fof(f58,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.22/0.61    inference(cnf_transformation,[],[f35])).
% 0.22/0.61  fof(f35,plain,(
% 0.22/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.61    inference(flattening,[],[f34])).
% 0.22/0.61  fof(f34,plain,(
% 0.22/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.61    inference(nnf_transformation,[],[f3])).
% 0.22/0.61  fof(f3,axiom,(
% 0.22/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.61  fof(f106,plain,(
% 0.22/0.61    r1_tarski(sK0,sK1) | r2_hidden(sK1,sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f105,f42])).
% 0.22/0.61  fof(f105,plain,(
% 0.22/0.61    ~v3_ordinal1(sK1) | r2_hidden(sK1,sK0) | r1_tarski(sK0,sK1)),
% 0.22/0.61    inference(resolution,[],[f80,f93])).
% 0.22/0.61  fof(f93,plain,(
% 0.22/0.61    ~r1_ordinal1(sK0,sK1) | r1_tarski(sK0,sK1)),
% 0.22/0.61    inference(resolution,[],[f74,f42])).
% 0.22/0.61  fof(f74,plain,(
% 0.22/0.61    ( ! [X0] : (~v3_ordinal1(X0) | ~r1_ordinal1(sK0,X0) | r1_tarski(sK0,X0)) )),
% 0.22/0.61    inference(resolution,[],[f41,f45])).
% 0.22/0.61  fof(f80,plain,(
% 0.22/0.61    ( ! [X6] : (r1_ordinal1(sK0,X6) | ~v3_ordinal1(X6) | r2_hidden(X6,sK0)) )),
% 0.22/0.61    inference(resolution,[],[f41,f48])).
% 0.22/0.61  fof(f207,plain,(
% 0.22/0.61    ~r2_hidden(sK1,sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f205,f50])).
% 0.22/0.61  fof(f50,plain,(
% 0.22/0.61    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f33])).
% 0.22/0.61  fof(f33,plain,(
% 0.22/0.61    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.22/0.61    inference(flattening,[],[f32])).
% 0.22/0.61  fof(f32,plain,(
% 0.22/0.61    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.22/0.61    inference(nnf_transformation,[],[f10])).
% 0.22/0.61  fof(f10,axiom,(
% 0.22/0.61    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.22/0.61  fof(f205,plain,(
% 0.22/0.61    ~r2_hidden(sK1,k1_ordinal1(sK0)) | ~r2_hidden(sK1,sK0)),
% 0.22/0.61    inference(resolution,[],[f201,f55])).
% 0.22/0.61  fof(f201,plain,(
% 0.22/0.61    r2_hidden(sK0,sK1) | ~r2_hidden(sK1,k1_ordinal1(sK0))),
% 0.22/0.61    inference(resolution,[],[f190,f43])).
% 0.22/0.61  fof(f43,plain,(
% 0.22/0.61    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 0.22/0.61    inference(cnf_transformation,[],[f30])).
% 0.22/0.61  fof(f190,plain,(
% 0.22/0.61    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK1,k1_ordinal1(sK0))),
% 0.22/0.61    inference(resolution,[],[f150,f41])).
% 0.22/0.61  fof(f150,plain,(
% 0.22/0.61    ( ! [X2] : (~v3_ordinal1(X2) | ~r1_ordinal1(k1_ordinal1(X2),sK1) | ~r2_hidden(sK1,k1_ordinal1(X2))) )),
% 0.22/0.61    inference(resolution,[],[f121,f54])).
% 0.22/0.61  fof(f54,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f24])).
% 0.22/0.61  fof(f24,plain,(
% 0.22/0.61    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.61    inference(ennf_transformation,[],[f13])).
% 0.22/0.61  fof(f13,axiom,(
% 0.22/0.61    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.61  fof(f121,plain,(
% 0.22/0.61    ( ! [X0] : (r1_tarski(k1_ordinal1(X0),sK1) | ~r1_ordinal1(k1_ordinal1(X0),sK1) | ~v3_ordinal1(X0)) )),
% 0.22/0.61    inference(resolution,[],[f83,f52])).
% 0.22/0.61  fof(f52,plain,(
% 0.22/0.61    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f23])).
% 0.22/0.61  fof(f23,plain,(
% 0.22/0.61    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.22/0.61    inference(ennf_transformation,[],[f12])).
% 0.22/0.61  fof(f12,axiom,(
% 0.22/0.61    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.22/0.61  fof(f83,plain,(
% 0.22/0.61    ( ! [X1] : (~v3_ordinal1(X1) | ~r1_ordinal1(X1,sK1) | r1_tarski(X1,sK1)) )),
% 0.22/0.61    inference(resolution,[],[f42,f45])).
% 0.22/0.61  fof(f217,plain,(
% 0.22/0.61    sK0 = sK1 | ~r2_hidden(sK0,sK1)),
% 0.22/0.61    inference(resolution,[],[f210,f155])).
% 0.22/0.61  fof(f155,plain,(
% 0.22/0.61    r2_hidden(sK1,k1_ordinal1(sK0)) | ~r2_hidden(sK0,sK1)),
% 0.22/0.61    inference(subsumption_resolution,[],[f154,f41])).
% 0.22/0.61  fof(f154,plain,(
% 0.22/0.61    r2_hidden(sK1,k1_ordinal1(sK0)) | ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.22/0.61    inference(resolution,[],[f131,f52])).
% 0.22/0.61  fof(f131,plain,(
% 0.22/0.61    ~v3_ordinal1(k1_ordinal1(sK0)) | r2_hidden(sK1,k1_ordinal1(sK0)) | ~r2_hidden(sK0,sK1)),
% 0.22/0.61    inference(resolution,[],[f89,f44])).
% 0.22/0.61  fof(f44,plain,(
% 0.22/0.61    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 0.22/0.61    inference(cnf_transformation,[],[f30])).
% 0.22/0.61  fof(f89,plain,(
% 0.22/0.61    ( ! [X7] : (r1_ordinal1(X7,sK1) | ~v3_ordinal1(X7) | r2_hidden(sK1,X7)) )),
% 0.22/0.61    inference(resolution,[],[f42,f48])).
% 0.22/0.61  fof(f210,plain,(
% 0.22/0.61    ~r2_hidden(sK1,k1_ordinal1(sK0)) | sK0 = sK1),
% 0.22/0.61    inference(resolution,[],[f207,f49])).
% 0.22/0.61  fof(f49,plain,(
% 0.22/0.61    ( ! [X0,X1] : (r2_hidden(X0,X1) | X0 = X1 | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 0.22/0.61    inference(cnf_transformation,[],[f33])).
% 0.22/0.61  fof(f274,plain,(
% 0.22/0.61    r2_hidden(sK0,sK1)),
% 0.22/0.61    inference(subsumption_resolution,[],[f223,f172])).
% 0.22/0.61  fof(f172,plain,(
% 0.22/0.61    ~r1_ordinal1(k1_ordinal1(sK0),sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f170,f68])).
% 0.22/0.61  fof(f68,plain,(
% 0.22/0.61    ( ! [X1] : (r2_hidden(X1,k1_ordinal1(X1))) )),
% 0.22/0.61    inference(equality_resolution,[],[f51])).
% 0.22/0.61  fof(f51,plain,(
% 0.22/0.61    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 0.22/0.61    inference(cnf_transformation,[],[f33])).
% 0.22/0.61  % (6467)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.61  fof(f170,plain,(
% 0.22/0.61    ~r1_ordinal1(k1_ordinal1(sK0),sK0) | ~r2_hidden(sK0,k1_ordinal1(sK0))),
% 0.22/0.61    inference(resolution,[],[f144,f41])).
% 0.22/0.61  fof(f144,plain,(
% 0.22/0.61    ( ! [X2] : (~v3_ordinal1(X2) | ~r1_ordinal1(k1_ordinal1(X2),sK0) | ~r2_hidden(sK0,k1_ordinal1(X2))) )),
% 0.22/0.61    inference(resolution,[],[f94,f54])).
% 0.22/0.61  fof(f94,plain,(
% 0.22/0.61    ( ! [X0] : (r1_tarski(k1_ordinal1(X0),sK0) | ~r1_ordinal1(k1_ordinal1(X0),sK0) | ~v3_ordinal1(X0)) )),
% 0.22/0.61    inference(resolution,[],[f75,f52])).
% 0.22/0.61  fof(f223,plain,(
% 0.22/0.61    r1_ordinal1(k1_ordinal1(sK0),sK0) | r2_hidden(sK0,sK1)),
% 0.22/0.61    inference(backward_demodulation,[],[f43,f221])).
% 0.22/0.61  % SZS output end Proof for theBenchmark
% 0.22/0.61  % (6471)------------------------------
% 0.22/0.61  % (6471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.61  % (6471)Termination reason: Refutation
% 0.22/0.61  
% 0.22/0.61  % (6471)Memory used [KB]: 1791
% 0.22/0.61  % (6471)Time elapsed: 0.142 s
% 0.22/0.61  % (6471)------------------------------
% 0.22/0.61  % (6471)------------------------------
% 0.22/0.61  % (6452)Success in time 0.243 s
%------------------------------------------------------------------------------
