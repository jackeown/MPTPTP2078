%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   40 (  93 expanded)
%              Number of leaves         :    8 (  34 expanded)
%              Depth                    :   15
%              Number of atoms          :  152 ( 517 expanded)
%              Number of equality atoms :   17 (  83 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f71,plain,(
    $false ),
    inference(subsumption_resolution,[],[f70,f20])).

fof(f20,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK1 != sK2
    & r4_wellord1(sK0,k1_wellord2(sK2))
    & r4_wellord1(sK0,k1_wellord2(sK1))
    & v3_ordinal1(sK2)
    & v3_ordinal1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f17,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & r4_wellord1(X0,k1_wellord2(X2))
                & r4_wellord1(X0,k1_wellord2(X1))
                & v3_ordinal1(X2) )
            & v3_ordinal1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r4_wellord1(sK0,k1_wellord2(X2))
              & r4_wellord1(sK0,k1_wellord2(X1))
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( X1 != X2
            & r4_wellord1(sK0,k1_wellord2(X2))
            & r4_wellord1(sK0,k1_wellord2(X1))
            & v3_ordinal1(X2) )
        & v3_ordinal1(X1) )
   => ( ? [X2] :
          ( sK1 != X2
          & r4_wellord1(sK0,k1_wellord2(X2))
          & r4_wellord1(sK0,k1_wellord2(sK1))
          & v3_ordinal1(X2) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( sK1 != X2
        & r4_wellord1(sK0,k1_wellord2(X2))
        & r4_wellord1(sK0,k1_wellord2(sK1))
        & v3_ordinal1(X2) )
   => ( sK1 != sK2
      & r4_wellord1(sK0,k1_wellord2(sK2))
      & r4_wellord1(sK0,k1_wellord2(sK1))
      & v3_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r4_wellord1(X0,k1_wellord2(X2))
              & r4_wellord1(X0,k1_wellord2(X1))
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r4_wellord1(X0,k1_wellord2(X2))
              & r4_wellord1(X0,k1_wellord2(X1))
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ! [X2] :
                ( v3_ordinal1(X2)
               => ( ( r4_wellord1(X0,k1_wellord2(X2))
                    & r4_wellord1(X0,k1_wellord2(X1)) )
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ! [X2] :
              ( v3_ordinal1(X2)
             => ( ( r4_wellord1(X0,k1_wellord2(X2))
                  & r4_wellord1(X0,k1_wellord2(X1)) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_wellord2)).

fof(f70,plain,(
    ~ v3_ordinal1(sK1) ),
    inference(subsumption_resolution,[],[f69,f21])).

fof(f21,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f69,plain,
    ( ~ v3_ordinal1(sK2)
    | ~ v3_ordinal1(sK1) ),
    inference(subsumption_resolution,[],[f67,f24])).

fof(f24,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,
    ( sK1 = sK2
    | ~ v3_ordinal1(sK2)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f59,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
      | X0 = X1
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).

fof(f59,plain,(
    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK2)) ),
    inference(resolution,[],[f55,f23])).

fof(f23,plain,(
    r4_wellord1(sK0,k1_wellord2(sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f55,plain,(
    ! [X0] :
      ( ~ r4_wellord1(sK0,k1_wellord2(X0))
      | r4_wellord1(k1_wellord2(sK1),k1_wellord2(X0)) ) ),
    inference(resolution,[],[f52,f25])).

fof(f25,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ r4_wellord1(sK0,X0)
      | r4_wellord1(k1_wellord2(sK1),X0) ) ),
    inference(resolution,[],[f50,f33])).

fof(f33,plain,(
    r4_wellord1(k1_wellord2(sK1),sK0) ),
    inference(subsumption_resolution,[],[f31,f25])).

fof(f31,plain,
    ( ~ v1_relat_1(k1_wellord2(sK1))
    | r4_wellord1(k1_wellord2(sK1),sK0) ),
    inference(resolution,[],[f29,f22])).

fof(f22,plain,(
    r4_wellord1(sK0,k1_wellord2(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f29,plain,(
    ! [X0] :
      ( ~ r4_wellord1(sK0,X0)
      | ~ v1_relat_1(X0)
      | r4_wellord1(X0,sK0) ) ),
    inference(resolution,[],[f27,f19])).

fof(f19,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | r4_wellord1(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),sK0)
      | ~ v1_relat_1(X1)
      | ~ r4_wellord1(sK0,X1)
      | r4_wellord1(k1_wellord2(X0),X1) ) ),
    inference(resolution,[],[f40,f19])).

fof(f40,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(X2)
      | ~ r4_wellord1(k1_wellord2(X4),X2)
      | ~ v1_relat_1(X3)
      | ~ r4_wellord1(X2,X3)
      | r4_wellord1(k1_wellord2(X4),X3) ) ),
    inference(resolution,[],[f28,f25])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r4_wellord1(X1,X2)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | r4_wellord1(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_wellord1(X0,X2)
              | ~ r4_wellord1(X1,X2)
              | ~ r4_wellord1(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_wellord1(X0,X2)
              | ~ r4_wellord1(X1,X2)
              | ~ r4_wellord1(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( ( r4_wellord1(X1,X2)
                  & r4_wellord1(X0,X1) )
               => r4_wellord1(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_wellord1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:09:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (28633)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.50  % (28634)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.50  % (28625)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (28628)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (28625)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (28647)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.51  % (28627)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.19/0.51  % (28646)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.19/0.51  % (28626)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.19/0.51  % (28621)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.19/0.51  % (28623)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.19/0.51  % (28628)Refutation not found, incomplete strategy% (28628)------------------------------
% 1.19/0.51  % (28628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.52  % (28638)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.19/0.52  % (28640)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.19/0.52  % (28624)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.19/0.52  % (28628)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.52  
% 1.19/0.52  % (28628)Memory used [KB]: 10618
% 1.19/0.52  % (28628)Time elapsed: 0.102 s
% 1.19/0.52  % (28628)------------------------------
% 1.19/0.52  % (28628)------------------------------
% 1.19/0.52  % (28642)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.19/0.52  % (28643)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.19/0.52  % (28629)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.19/0.52  % SZS output start Proof for theBenchmark
% 1.19/0.52  fof(f71,plain,(
% 1.19/0.52    $false),
% 1.19/0.52    inference(subsumption_resolution,[],[f70,f20])).
% 1.19/0.52  fof(f20,plain,(
% 1.19/0.52    v3_ordinal1(sK1)),
% 1.19/0.52    inference(cnf_transformation,[],[f18])).
% 1.19/0.52  fof(f18,plain,(
% 1.19/0.52    ((sK1 != sK2 & r4_wellord1(sK0,k1_wellord2(sK2)) & r4_wellord1(sK0,k1_wellord2(sK1)) & v3_ordinal1(sK2)) & v3_ordinal1(sK1)) & v1_relat_1(sK0)),
% 1.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f17,f16,f15])).
% 1.19/0.52  fof(f15,plain,(
% 1.19/0.52    ? [X0] : (? [X1] : (? [X2] : (X1 != X2 & r4_wellord1(X0,k1_wellord2(X2)) & r4_wellord1(X0,k1_wellord2(X1)) & v3_ordinal1(X2)) & v3_ordinal1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (X1 != X2 & r4_wellord1(sK0,k1_wellord2(X2)) & r4_wellord1(sK0,k1_wellord2(X1)) & v3_ordinal1(X2)) & v3_ordinal1(X1)) & v1_relat_1(sK0))),
% 1.19/0.52    introduced(choice_axiom,[])).
% 1.19/0.52  fof(f16,plain,(
% 1.19/0.52    ? [X1] : (? [X2] : (X1 != X2 & r4_wellord1(sK0,k1_wellord2(X2)) & r4_wellord1(sK0,k1_wellord2(X1)) & v3_ordinal1(X2)) & v3_ordinal1(X1)) => (? [X2] : (sK1 != X2 & r4_wellord1(sK0,k1_wellord2(X2)) & r4_wellord1(sK0,k1_wellord2(sK1)) & v3_ordinal1(X2)) & v3_ordinal1(sK1))),
% 1.19/0.52    introduced(choice_axiom,[])).
% 1.19/0.52  fof(f17,plain,(
% 1.19/0.52    ? [X2] : (sK1 != X2 & r4_wellord1(sK0,k1_wellord2(X2)) & r4_wellord1(sK0,k1_wellord2(sK1)) & v3_ordinal1(X2)) => (sK1 != sK2 & r4_wellord1(sK0,k1_wellord2(sK2)) & r4_wellord1(sK0,k1_wellord2(sK1)) & v3_ordinal1(sK2))),
% 1.19/0.52    introduced(choice_axiom,[])).
% 1.19/0.52  fof(f8,plain,(
% 1.19/0.52    ? [X0] : (? [X1] : (? [X2] : (X1 != X2 & r4_wellord1(X0,k1_wellord2(X2)) & r4_wellord1(X0,k1_wellord2(X1)) & v3_ordinal1(X2)) & v3_ordinal1(X1)) & v1_relat_1(X0))),
% 1.19/0.52    inference(flattening,[],[f7])).
% 1.19/0.52  fof(f7,plain,(
% 1.19/0.52    ? [X0] : (? [X1] : (? [X2] : ((X1 != X2 & (r4_wellord1(X0,k1_wellord2(X2)) & r4_wellord1(X0,k1_wellord2(X1)))) & v3_ordinal1(X2)) & v3_ordinal1(X1)) & v1_relat_1(X0))),
% 1.19/0.52    inference(ennf_transformation,[],[f6])).
% 1.19/0.52  fof(f6,negated_conjecture,(
% 1.19/0.52    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v3_ordinal1(X1) => ! [X2] : (v3_ordinal1(X2) => ((r4_wellord1(X0,k1_wellord2(X2)) & r4_wellord1(X0,k1_wellord2(X1))) => X1 = X2))))),
% 1.19/0.52    inference(negated_conjecture,[],[f5])).
% 1.19/0.52  fof(f5,conjecture,(
% 1.19/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v3_ordinal1(X1) => ! [X2] : (v3_ordinal1(X2) => ((r4_wellord1(X0,k1_wellord2(X2)) & r4_wellord1(X0,k1_wellord2(X1))) => X1 = X2))))),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_wellord2)).
% 1.19/0.52  fof(f70,plain,(
% 1.19/0.52    ~v3_ordinal1(sK1)),
% 1.19/0.52    inference(subsumption_resolution,[],[f69,f21])).
% 1.19/0.52  fof(f21,plain,(
% 1.19/0.52    v3_ordinal1(sK2)),
% 1.19/0.52    inference(cnf_transformation,[],[f18])).
% 1.19/0.52  fof(f69,plain,(
% 1.19/0.52    ~v3_ordinal1(sK2) | ~v3_ordinal1(sK1)),
% 1.19/0.52    inference(subsumption_resolution,[],[f67,f24])).
% 1.19/0.52  fof(f24,plain,(
% 1.19/0.52    sK1 != sK2),
% 1.19/0.52    inference(cnf_transformation,[],[f18])).
% 1.19/0.52  fof(f67,plain,(
% 1.19/0.52    sK1 = sK2 | ~v3_ordinal1(sK2) | ~v3_ordinal1(sK1)),
% 1.19/0.52    inference(resolution,[],[f59,f26])).
% 1.19/0.52  fof(f26,plain,(
% 1.19/0.52    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) | X0 = X1 | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f10])).
% 1.19/0.52  fof(f10,plain,(
% 1.19/0.52    ! [X0] : (! [X1] : (X0 = X1 | ~r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.19/0.52    inference(flattening,[],[f9])).
% 1.19/0.52  fof(f9,plain,(
% 1.19/0.52    ! [X0] : (! [X1] : ((X0 = X1 | ~r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.19/0.52    inference(ennf_transformation,[],[f4])).
% 1.19/0.52  fof(f4,axiom,(
% 1.19/0.52    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).
% 1.19/0.52  fof(f59,plain,(
% 1.19/0.52    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK2))),
% 1.19/0.52    inference(resolution,[],[f55,f23])).
% 1.19/0.52  fof(f23,plain,(
% 1.19/0.52    r4_wellord1(sK0,k1_wellord2(sK2))),
% 1.19/0.52    inference(cnf_transformation,[],[f18])).
% 1.19/0.52  fof(f55,plain,(
% 1.19/0.52    ( ! [X0] : (~r4_wellord1(sK0,k1_wellord2(X0)) | r4_wellord1(k1_wellord2(sK1),k1_wellord2(X0))) )),
% 1.19/0.52    inference(resolution,[],[f52,f25])).
% 1.19/0.52  fof(f25,plain,(
% 1.19/0.52    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 1.19/0.52    inference(cnf_transformation,[],[f3])).
% 1.19/0.52  fof(f3,axiom,(
% 1.19/0.52    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 1.19/0.52  fof(f52,plain,(
% 1.19/0.52    ( ! [X0] : (~v1_relat_1(X0) | ~r4_wellord1(sK0,X0) | r4_wellord1(k1_wellord2(sK1),X0)) )),
% 1.19/0.52    inference(resolution,[],[f50,f33])).
% 1.19/0.52  fof(f33,plain,(
% 1.19/0.52    r4_wellord1(k1_wellord2(sK1),sK0)),
% 1.19/0.52    inference(subsumption_resolution,[],[f31,f25])).
% 1.19/0.52  fof(f31,plain,(
% 1.19/0.52    ~v1_relat_1(k1_wellord2(sK1)) | r4_wellord1(k1_wellord2(sK1),sK0)),
% 1.19/0.52    inference(resolution,[],[f29,f22])).
% 1.19/0.52  fof(f22,plain,(
% 1.19/0.52    r4_wellord1(sK0,k1_wellord2(sK1))),
% 1.19/0.52    inference(cnf_transformation,[],[f18])).
% 1.19/0.52  fof(f29,plain,(
% 1.19/0.52    ( ! [X0] : (~r4_wellord1(sK0,X0) | ~v1_relat_1(X0) | r4_wellord1(X0,sK0)) )),
% 1.19/0.52    inference(resolution,[],[f27,f19])).
% 1.19/0.52  fof(f19,plain,(
% 1.19/0.52    v1_relat_1(sK0)),
% 1.19/0.52    inference(cnf_transformation,[],[f18])).
% 1.19/0.52  fof(f27,plain,(
% 1.19/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | r4_wellord1(X1,X0)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f12])).
% 1.19/0.52  fof(f12,plain,(
% 1.19/0.52    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.19/0.52    inference(flattening,[],[f11])).
% 1.19/0.52  fof(f11,plain,(
% 1.19/0.52    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.19/0.52    inference(ennf_transformation,[],[f1])).
% 1.19/0.52  fof(f1,axiom,(
% 1.19/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).
% 1.19/0.52  fof(f50,plain,(
% 1.19/0.52    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),sK0) | ~v1_relat_1(X1) | ~r4_wellord1(sK0,X1) | r4_wellord1(k1_wellord2(X0),X1)) )),
% 1.19/0.52    inference(resolution,[],[f40,f19])).
% 1.19/0.52  fof(f40,plain,(
% 1.19/0.52    ( ! [X4,X2,X3] : (~v1_relat_1(X2) | ~r4_wellord1(k1_wellord2(X4),X2) | ~v1_relat_1(X3) | ~r4_wellord1(X2,X3) | r4_wellord1(k1_wellord2(X4),X3)) )),
% 1.19/0.52    inference(resolution,[],[f28,f25])).
% 1.19/0.52  fof(f28,plain,(
% 1.19/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~r4_wellord1(X1,X2) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | r4_wellord1(X0,X2)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f14])).
% 1.19/0.52  fof(f14,plain,(
% 1.19/0.52    ! [X0] : (! [X1] : (! [X2] : (r4_wellord1(X0,X2) | ~r4_wellord1(X1,X2) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.19/0.52    inference(flattening,[],[f13])).
% 1.19/0.52  fof(f13,plain,(
% 1.19/0.52    ! [X0] : (! [X1] : (! [X2] : ((r4_wellord1(X0,X2) | (~r4_wellord1(X1,X2) | ~r4_wellord1(X0,X1))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.19/0.52    inference(ennf_transformation,[],[f2])).
% 1.19/0.52  fof(f2,axiom,(
% 1.19/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ((r4_wellord1(X1,X2) & r4_wellord1(X0,X1)) => r4_wellord1(X0,X2)))))),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_wellord1)).
% 1.19/0.52  % SZS output end Proof for theBenchmark
% 1.19/0.52  % (28625)------------------------------
% 1.19/0.52  % (28625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.52  % (28625)Termination reason: Refutation
% 1.19/0.52  
% 1.19/0.52  % (28625)Memory used [KB]: 6140
% 1.19/0.52  % (28625)Time elapsed: 0.099 s
% 1.19/0.52  % (28625)------------------------------
% 1.19/0.52  % (28625)------------------------------
% 1.19/0.52  % (28630)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.19/0.52  % (28619)Success in time 0.163 s
%------------------------------------------------------------------------------
