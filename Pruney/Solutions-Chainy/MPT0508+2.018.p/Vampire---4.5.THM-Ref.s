%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 115 expanded)
%              Number of leaves         :    9 (  25 expanded)
%              Depth                    :   12
%              Number of atoms          :  146 ( 353 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f347,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f334,f342,f346])).

fof(f346,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f345])).

fof(f345,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f344,f24])).

fof(f24,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).

fof(f344,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_5 ),
    inference(resolution,[],[f333,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f333,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f331])).

fof(f331,plain,
    ( spl4_5
  <=> v1_relat_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f342,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f341])).

fof(f341,plain,
    ( $false
    | spl4_4 ),
    inference(subsumption_resolution,[],[f340,f24])).

fof(f340,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f337,f21])).

fof(f21,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f337,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ v1_relat_1(sK2)
    | spl4_4 ),
    inference(resolution,[],[f335,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f335,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k7_relat_1(sK2,sK0),X0)
        | ~ r1_tarski(X0,sK3) )
    | spl4_4 ),
    inference(resolution,[],[f329,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f329,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),sK3)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f327])).

fof(f327,plain,
    ( spl4_4
  <=> r1_tarski(k7_relat_1(sK2,sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f334,plain,
    ( ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f325,f331,f327])).

fof(f325,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ r1_tarski(k7_relat_1(sK2,sK0),sK3) ),
    inference(subsumption_resolution,[],[f315,f125])).

fof(f125,plain,(
    ! [X6] :
      ( r1_tarski(k7_relat_1(sK2,X6),k7_relat_1(sK2,X6))
      | ~ v1_relat_1(k7_relat_1(sK2,X6)) ) ),
    inference(superposition,[],[f26,f100])).

fof(f100,plain,(
    ! [X1] : k7_relat_1(sK2,X1) = k7_relat_1(k7_relat_1(sK2,X1),X1) ),
    inference(resolution,[],[f40,f24])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),X1) ) ),
    inference(subsumption_resolution,[],[f38,f25])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k7_relat_1(X0,X1))
      | k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f28,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f315,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ r1_tarski(k7_relat_1(sK2,sK0),sK3) ),
    inference(superposition,[],[f78,f298])).

fof(f298,plain,(
    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(resolution,[],[f291,f24])).

fof(f291,plain,(
    ! [X22] :
      ( ~ v1_relat_1(X22)
      | k7_relat_1(X22,sK0) = k7_relat_1(k7_relat_1(X22,sK0),sK1) ) ),
    inference(resolution,[],[f207,f22])).

fof(f22,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f207,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0)
      | k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),X2) ) ),
    inference(subsumption_resolution,[],[f200,f25])).

fof(f200,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f39,f27])).

fof(f39,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,X3)
      | ~ r1_tarski(k1_relat_1(X2),X4)
      | ~ v1_relat_1(X2)
      | k7_relat_1(X2,X3) = X2 ) ),
    inference(resolution,[],[f28,f30])).

fof(f78,plain,(
    ! [X3] :
      ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1))
      | ~ v1_relat_1(X3)
      | ~ r1_tarski(X3,sK3) ) ),
    inference(subsumption_resolution,[],[f73,f20])).

fof(f20,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f73,plain,(
    ! [X3] :
      ( ~ v1_relat_1(sK3)
      | ~ r1_tarski(X3,sK3)
      | ~ v1_relat_1(X3)
      | ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1)) ) ),
    inference(resolution,[],[f29,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k7_relat_1(sK3,sK1))
      | ~ r1_tarski(k7_relat_1(sK2,sK0),X0) ) ),
    inference(resolution,[],[f30,f23])).

fof(f23,plain,(
    ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:15:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.41  % (26755)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.41  % (26754)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.41  % (26753)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.42  % (26751)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.20/0.42  % (26756)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.43  % (26759)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.44  % (26752)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.20/0.44  % (26760)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.20/0.46  % (26758)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.46  % (26757)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.47  % (26750)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.47  % (26749)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.48  % (26749)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f347,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f334,f342,f346])).
% 0.20/0.48  fof(f346,plain,(
% 0.20/0.48    spl4_5),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f345])).
% 0.20/0.48  fof(f345,plain,(
% 0.20/0.48    $false | spl4_5),
% 0.20/0.48    inference(subsumption_resolution,[],[f344,f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    v1_relat_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.20/0.48    inference(flattening,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 0.20/0.48    inference(negated_conjecture,[],[f7])).
% 0.20/0.48  fof(f7,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).
% 0.20/0.48  fof(f344,plain,(
% 0.20/0.48    ~v1_relat_1(sK2) | spl4_5),
% 0.20/0.48    inference(resolution,[],[f333,f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.48  fof(f333,plain,(
% 0.20/0.48    ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl4_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f331])).
% 0.20/0.48  fof(f331,plain,(
% 0.20/0.48    spl4_5 <=> v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.48  fof(f342,plain,(
% 0.20/0.48    spl4_4),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f341])).
% 0.20/0.48  fof(f341,plain,(
% 0.20/0.48    $false | spl4_4),
% 0.20/0.48    inference(subsumption_resolution,[],[f340,f24])).
% 0.20/0.48  fof(f340,plain,(
% 0.20/0.48    ~v1_relat_1(sK2) | spl4_4),
% 0.20/0.48    inference(subsumption_resolution,[],[f337,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    r1_tarski(sK2,sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f337,plain,(
% 0.20/0.48    ~r1_tarski(sK2,sK3) | ~v1_relat_1(sK2) | spl4_4),
% 0.20/0.48    inference(resolution,[],[f335,f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 0.20/0.48  fof(f335,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_tarski(k7_relat_1(sK2,sK0),X0) | ~r1_tarski(X0,sK3)) ) | spl4_4),
% 0.20/0.48    inference(resolution,[],[f329,f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.48    inference(flattening,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.48  fof(f329,plain,(
% 0.20/0.48    ~r1_tarski(k7_relat_1(sK2,sK0),sK3) | spl4_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f327])).
% 0.20/0.48  fof(f327,plain,(
% 0.20/0.48    spl4_4 <=> r1_tarski(k7_relat_1(sK2,sK0),sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.48  fof(f334,plain,(
% 0.20/0.48    ~spl4_4 | ~spl4_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f325,f331,f327])).
% 0.20/0.48  fof(f325,plain,(
% 0.20/0.48    ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~r1_tarski(k7_relat_1(sK2,sK0),sK3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f315,f125])).
% 0.20/0.48  fof(f125,plain,(
% 0.20/0.48    ( ! [X6] : (r1_tarski(k7_relat_1(sK2,X6),k7_relat_1(sK2,X6)) | ~v1_relat_1(k7_relat_1(sK2,X6))) )),
% 0.20/0.48    inference(superposition,[],[f26,f100])).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    ( ! [X1] : (k7_relat_1(sK2,X1) = k7_relat_1(k7_relat_1(sK2,X1),X1)) )),
% 0.20/0.48    inference(resolution,[],[f40,f24])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),X1)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f38,f25])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(k7_relat_1(X0,X1)) | k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),X1) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(resolution,[],[f28,f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.20/0.48  fof(f315,plain,(
% 0.20/0.48    ~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK0)) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~r1_tarski(k7_relat_1(sK2,sK0),sK3)),
% 0.20/0.48    inference(superposition,[],[f78,f298])).
% 0.20/0.48  fof(f298,plain,(
% 0.20/0.48    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.20/0.48    inference(resolution,[],[f291,f24])).
% 0.20/0.48  fof(f291,plain,(
% 0.20/0.48    ( ! [X22] : (~v1_relat_1(X22) | k7_relat_1(X22,sK0) = k7_relat_1(k7_relat_1(X22,sK0),sK1)) )),
% 0.20/0.48    inference(resolution,[],[f207,f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    r1_tarski(sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f207,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~v1_relat_1(X0) | k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),X2)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f200,f25])).
% 0.20/0.48  fof(f200,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~v1_relat_1(k7_relat_1(X0,X1)) | k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),X2) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(resolution,[],[f39,f27])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ( ! [X4,X2,X3] : (~r1_tarski(X4,X3) | ~r1_tarski(k1_relat_1(X2),X4) | ~v1_relat_1(X2) | k7_relat_1(X2,X3) = X2) )),
% 0.20/0.48    inference(resolution,[],[f28,f30])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    ( ! [X3] : (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1)) | ~v1_relat_1(X3) | ~r1_tarski(X3,sK3)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f73,f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    v1_relat_1(sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    ( ! [X3] : (~v1_relat_1(sK3) | ~r1_tarski(X3,sK3) | ~v1_relat_1(X3) | ~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1))) )),
% 0.20/0.48    inference(resolution,[],[f29,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_tarski(X0,k7_relat_1(sK3,sK1)) | ~r1_tarski(k7_relat_1(sK2,sK0),X0)) )),
% 0.20/0.48    inference(resolution,[],[f30,f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~v1_relat_1(X2) | ~r1_tarski(X1,X2) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (26749)------------------------------
% 0.20/0.48  % (26749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (26749)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (26749)Memory used [KB]: 10746
% 0.20/0.48  % (26749)Time elapsed: 0.078 s
% 0.20/0.48  % (26749)------------------------------
% 0.20/0.48  % (26749)------------------------------
% 0.20/0.49  % (26748)Success in time 0.135 s
%------------------------------------------------------------------------------
