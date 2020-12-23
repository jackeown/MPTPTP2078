%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 164 expanded)
%              Number of leaves         :    9 (  36 expanded)
%              Depth                    :   21
%              Number of atoms          :  264 ( 704 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f72,plain,(
    $false ),
    inference(subsumption_resolution,[],[f30,f71])).

fof(f71,plain,(
    ! [X3] : v2_wellord1(k2_wellord1(sK1,X3)) ),
    inference(subsumption_resolution,[],[f70,f44])).

fof(f44,plain,(
    v1_relat_2(sK1) ),
    inference(subsumption_resolution,[],[f43,f28])).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ v2_wellord1(k2_wellord1(sK1,sK0))
    & v2_wellord1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( ~ v2_wellord1(k2_wellord1(X1,X0))
        & v2_wellord1(X1)
        & v1_relat_1(X1) )
   => ( ~ v2_wellord1(k2_wellord1(sK1,sK0))
      & v2_wellord1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ~ v2_wellord1(k2_wellord1(X1,X0))
      & v2_wellord1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ~ v2_wellord1(k2_wellord1(X1,X0))
      & v2_wellord1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( v2_wellord1(X1)
         => v2_wellord1(k2_wellord1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => v2_wellord1(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_wellord1)).

fof(f43,plain,
    ( v1_relat_2(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f31,f29])).

fof(f29,plain,(
    v2_wellord1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(f70,plain,(
    ! [X3] :
      ( v2_wellord1(k2_wellord1(sK1,X3))
      | ~ v1_relat_2(sK1) ) ),
    inference(subsumption_resolution,[],[f69,f46])).

fof(f46,plain,(
    v8_relat_2(sK1) ),
    inference(subsumption_resolution,[],[f45,f28])).

fof(f45,plain,
    ( v8_relat_2(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f32,f29])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f69,plain,(
    ! [X3] :
      ( v2_wellord1(k2_wellord1(sK1,X3))
      | ~ v8_relat_2(sK1)
      | ~ v1_relat_2(sK1) ) ),
    inference(subsumption_resolution,[],[f68,f48])).

fof(f48,plain,(
    v4_relat_2(sK1) ),
    inference(subsumption_resolution,[],[f47,f28])).

fof(f47,plain,
    ( v4_relat_2(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f33,f29])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | v4_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,(
    ! [X3] :
      ( v2_wellord1(k2_wellord1(sK1,X3))
      | ~ v4_relat_2(sK1)
      | ~ v8_relat_2(sK1)
      | ~ v1_relat_2(sK1) ) ),
    inference(subsumption_resolution,[],[f67,f50])).

fof(f50,plain,(
    v6_relat_2(sK1) ),
    inference(subsumption_resolution,[],[f49,f28])).

fof(f49,plain,
    ( v6_relat_2(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f34,f29])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f67,plain,(
    ! [X3] :
      ( v2_wellord1(k2_wellord1(sK1,X3))
      | ~ v6_relat_2(sK1)
      | ~ v4_relat_2(sK1)
      | ~ v8_relat_2(sK1)
      | ~ v1_relat_2(sK1) ) ),
    inference(subsumption_resolution,[],[f65,f28])).

fof(f65,plain,(
    ! [X3] :
      ( v2_wellord1(k2_wellord1(sK1,X3))
      | ~ v1_relat_1(sK1)
      | ~ v6_relat_2(sK1)
      | ~ v4_relat_2(sK1)
      | ~ v8_relat_2(sK1)
      | ~ v1_relat_2(sK1) ) ),
    inference(resolution,[],[f63,f52])).

fof(f52,plain,(
    v1_wellord1(sK1) ),
    inference(subsumption_resolution,[],[f51,f28])).

fof(f51,plain,
    ( v1_wellord1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f35,f29])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | v1_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_wellord1(X0)
      | v2_wellord1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ v6_relat_2(X0)
      | ~ v4_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k2_wellord1(X0,X1))
      | ~ v1_wellord1(X0)
      | ~ v1_relat_1(X0)
      | ~ v6_relat_2(X0)
      | ~ v4_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f61,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_2(k2_wellord1(X1,X0))
      | ~ v1_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_2(k2_wellord1(X1,X0))
      | ~ v1_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_2(k2_wellord1(X1,X0))
      | ~ v1_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
       => v1_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_wellord1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_2(k2_wellord1(X0,X1))
      | v2_wellord1(k2_wellord1(X0,X1))
      | ~ v1_wellord1(X0)
      | ~ v1_relat_1(X0)
      | ~ v6_relat_2(X0)
      | ~ v4_relat_2(X0)
      | ~ v8_relat_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k2_wellord1(X0,X1))
      | ~ v1_relat_2(k2_wellord1(X0,X1))
      | ~ v1_wellord1(X0)
      | ~ v1_relat_1(X0)
      | ~ v6_relat_2(X0)
      | ~ v4_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f59,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v8_relat_2(k2_wellord1(X1,X0))
      | ~ v8_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

% (16949)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% (16950)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% (16956)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
fof(f23,plain,(
    ! [X0,X1] :
      ( v8_relat_2(k2_wellord1(X1,X0))
      | ~ v8_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v8_relat_2(k2_wellord1(X1,X0))
      | ~ v8_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v8_relat_2(X1)
       => v8_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_wellord1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v8_relat_2(k2_wellord1(X0,X1))
      | v2_wellord1(k2_wellord1(X0,X1))
      | ~ v1_relat_2(k2_wellord1(X0,X1))
      | ~ v1_wellord1(X0)
      | ~ v1_relat_1(X0)
      | ~ v6_relat_2(X0)
      | ~ v4_relat_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k2_wellord1(X0,X1))
      | ~ v8_relat_2(k2_wellord1(X0,X1))
      | ~ v1_relat_2(k2_wellord1(X0,X1))
      | ~ v1_wellord1(X0)
      | ~ v1_relat_1(X0)
      | ~ v6_relat_2(X0)
      | ~ v4_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f57,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v4_relat_2(k2_wellord1(X1,X0))
      | ~ v4_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v4_relat_2(k2_wellord1(X1,X0))
      | ~ v4_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v4_relat_2(k2_wellord1(X1,X0))
      | ~ v4_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_2(X1)
       => v4_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_wellord1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_2(k2_wellord1(X0,X1))
      | v2_wellord1(k2_wellord1(X0,X1))
      | ~ v8_relat_2(k2_wellord1(X0,X1))
      | ~ v1_relat_2(k2_wellord1(X0,X1))
      | ~ v1_wellord1(X0)
      | ~ v1_relat_1(X0)
      | ~ v6_relat_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k2_wellord1(X0,X1))
      | ~ v4_relat_2(k2_wellord1(X0,X1))
      | ~ v8_relat_2(k2_wellord1(X0,X1))
      | ~ v1_relat_2(k2_wellord1(X0,X1))
      | ~ v1_wellord1(X0)
      | ~ v1_relat_1(X0)
      | ~ v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f54,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v6_relat_2(k2_wellord1(X1,X0))
      | ~ v6_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v6_relat_2(k2_wellord1(X1,X0))
      | ~ v6_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v6_relat_2(k2_wellord1(X1,X0))
      | ~ v6_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v6_relat_2(X1)
       => v6_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_wellord1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v6_relat_2(k2_wellord1(X0,X1))
      | v2_wellord1(k2_wellord1(X0,X1))
      | ~ v4_relat_2(k2_wellord1(X0,X1))
      | ~ v8_relat_2(k2_wellord1(X0,X1))
      | ~ v1_relat_2(k2_wellord1(X0,X1))
      | ~ v1_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f53,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k2_wellord1(X0,X1))
      | ~ v6_relat_2(k2_wellord1(X0,X1))
      | ~ v4_relat_2(k2_wellord1(X0,X1))
      | ~ v8_relat_2(k2_wellord1(X0,X1))
      | ~ v1_relat_2(k2_wellord1(X0,X1))
      | ~ v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f36,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_wellord1(k2_wellord1(X1,X0))
      | ~ v1_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_wellord1(k2_wellord1(X1,X0))
      | ~ v1_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_wellord1(k2_wellord1(X1,X0))
      | ~ v1_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v1_wellord1(X1)
       => v1_wellord1(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_wellord1)).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_wellord1(X0)
      | v2_wellord1(X0)
      | ~ v6_relat_2(X0)
      | ~ v4_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f30,plain,(
    ~ v2_wellord1(k2_wellord1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:10:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (16948)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.22/0.49  % (16957)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.22/0.49  % (16958)WARNING: option uwaf not known.
% 0.22/0.49  % (16958)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.22/0.49  % (16958)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(subsumption_resolution,[],[f30,f71])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    ( ! [X3] : (v2_wellord1(k2_wellord1(sK1,X3))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f70,f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    v1_relat_2(sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f43,f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    v1_relat_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ~v2_wellord1(k2_wellord1(sK1,sK0)) & v2_wellord1(sK1) & v1_relat_1(sK1)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ? [X0,X1] : (~v2_wellord1(k2_wellord1(X1,X0)) & v2_wellord1(X1) & v1_relat_1(X1)) => (~v2_wellord1(k2_wellord1(sK1,sK0)) & v2_wellord1(sK1) & v1_relat_1(sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X0,X1] : (~v2_wellord1(k2_wellord1(X1,X0)) & v2_wellord1(X1) & v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ? [X0,X1] : ((~v2_wellord1(k2_wellord1(X1,X0)) & v2_wellord1(X1)) & v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1] : (v1_relat_1(X1) => (v2_wellord1(X1) => v2_wellord1(k2_wellord1(X1,X0))))),
% 0.22/0.49    inference(negated_conjecture,[],[f8])).
% 0.22/0.49  fof(f8,conjecture,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v2_wellord1(X1) => v2_wellord1(k2_wellord1(X1,X0))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_wellord1)).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    v1_relat_2(sK1) | ~v1_relat_1(sK1)),
% 0.22/0.49    inference(resolution,[],[f31,f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    v2_wellord1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ( ! [X0] : (~v2_wellord1(X0) | v1_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0] : (((v2_wellord1(X0) | ~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0)) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0] : (((v2_wellord1(X0) | (~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0))) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0] : ((v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    ( ! [X3] : (v2_wellord1(k2_wellord1(sK1,X3)) | ~v1_relat_2(sK1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f69,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    v8_relat_2(sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f45,f28])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    v8_relat_2(sK1) | ~v1_relat_1(sK1)),
% 0.22/0.49    inference(resolution,[],[f32,f29])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X0] : (~v2_wellord1(X0) | v8_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    ( ! [X3] : (v2_wellord1(k2_wellord1(sK1,X3)) | ~v8_relat_2(sK1) | ~v1_relat_2(sK1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f68,f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    v4_relat_2(sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f47,f28])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    v4_relat_2(sK1) | ~v1_relat_1(sK1)),
% 0.22/0.49    inference(resolution,[],[f33,f29])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X0] : (~v2_wellord1(X0) | v4_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    ( ! [X3] : (v2_wellord1(k2_wellord1(sK1,X3)) | ~v4_relat_2(sK1) | ~v8_relat_2(sK1) | ~v1_relat_2(sK1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f67,f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    v6_relat_2(sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f49,f28])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    v6_relat_2(sK1) | ~v1_relat_1(sK1)),
% 0.22/0.49    inference(resolution,[],[f34,f29])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X0] : (~v2_wellord1(X0) | v6_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    ( ! [X3] : (v2_wellord1(k2_wellord1(sK1,X3)) | ~v6_relat_2(sK1) | ~v4_relat_2(sK1) | ~v8_relat_2(sK1) | ~v1_relat_2(sK1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f65,f28])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    ( ! [X3] : (v2_wellord1(k2_wellord1(sK1,X3)) | ~v1_relat_1(sK1) | ~v6_relat_2(sK1) | ~v4_relat_2(sK1) | ~v8_relat_2(sK1) | ~v1_relat_2(sK1)) )),
% 0.22/0.49    inference(resolution,[],[f63,f52])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    v1_wellord1(sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f51,f28])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    v1_wellord1(sK1) | ~v1_relat_1(sK1)),
% 0.22/0.49    inference(resolution,[],[f35,f29])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0] : (~v2_wellord1(X0) | v1_wellord1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_wellord1(X0) | v2_wellord1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0)) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f62])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_wellord1(k2_wellord1(X0,X1)) | ~v1_wellord1(X0) | ~v1_relat_1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(resolution,[],[f61,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_relat_2(k2_wellord1(X1,X0)) | ~v1_relat_2(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_2(k2_wellord1(X1,X0)) | ~v1_relat_2(X1) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0,X1] : ((v1_relat_2(k2_wellord1(X1,X0)) | ~v1_relat_2(X1)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v1_relat_2(X1) => v1_relat_2(k2_wellord1(X1,X0))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_wellord1)).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_relat_2(k2_wellord1(X0,X1)) | v2_wellord1(k2_wellord1(X0,X1)) | ~v1_wellord1(X0) | ~v1_relat_1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0)) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f60])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_wellord1(k2_wellord1(X0,X1)) | ~v1_relat_2(k2_wellord1(X0,X1)) | ~v1_wellord1(X0) | ~v1_relat_1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(resolution,[],[f59,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v8_relat_2(k2_wellord1(X1,X0)) | ~v8_relat_2(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  % (16949)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.22/0.49  % (16950)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.22/0.50  % (16956)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1] : (v8_relat_2(k2_wellord1(X1,X0)) | ~v8_relat_2(X1) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1] : ((v8_relat_2(k2_wellord1(X1,X0)) | ~v8_relat_2(X1)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v8_relat_2(X1) => v8_relat_2(k2_wellord1(X1,X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_wellord1)).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v8_relat_2(k2_wellord1(X0,X1)) | v2_wellord1(k2_wellord1(X0,X1)) | ~v1_relat_2(k2_wellord1(X0,X1)) | ~v1_wellord1(X0) | ~v1_relat_1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0)) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v2_wellord1(k2_wellord1(X0,X1)) | ~v8_relat_2(k2_wellord1(X0,X1)) | ~v1_relat_2(k2_wellord1(X0,X1)) | ~v1_wellord1(X0) | ~v1_relat_1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(resolution,[],[f57,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v4_relat_2(k2_wellord1(X1,X0)) | ~v4_relat_2(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1] : (v4_relat_2(k2_wellord1(X1,X0)) | ~v4_relat_2(X1) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1] : ((v4_relat_2(k2_wellord1(X1,X0)) | ~v4_relat_2(X1)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_2(X1) => v4_relat_2(k2_wellord1(X1,X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_wellord1)).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v4_relat_2(k2_wellord1(X0,X1)) | v2_wellord1(k2_wellord1(X0,X1)) | ~v8_relat_2(k2_wellord1(X0,X1)) | ~v1_relat_2(k2_wellord1(X0,X1)) | ~v1_wellord1(X0) | ~v1_relat_1(X0) | ~v6_relat_2(X0)) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f56])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v2_wellord1(k2_wellord1(X0,X1)) | ~v4_relat_2(k2_wellord1(X0,X1)) | ~v8_relat_2(k2_wellord1(X0,X1)) | ~v1_relat_2(k2_wellord1(X0,X1)) | ~v1_wellord1(X0) | ~v1_relat_1(X0) | ~v6_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(resolution,[],[f54,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v6_relat_2(k2_wellord1(X1,X0)) | ~v6_relat_2(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1] : (v6_relat_2(k2_wellord1(X1,X0)) | ~v6_relat_2(X1) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1] : ((v6_relat_2(k2_wellord1(X1,X0)) | ~v6_relat_2(X1)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v6_relat_2(X1) => v6_relat_2(k2_wellord1(X1,X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_wellord1)).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v6_relat_2(k2_wellord1(X0,X1)) | v2_wellord1(k2_wellord1(X0,X1)) | ~v4_relat_2(k2_wellord1(X0,X1)) | ~v8_relat_2(k2_wellord1(X0,X1)) | ~v1_relat_2(k2_wellord1(X0,X1)) | ~v1_wellord1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f53,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k2_wellord1(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v2_wellord1(k2_wellord1(X0,X1)) | ~v6_relat_2(k2_wellord1(X0,X1)) | ~v4_relat_2(k2_wellord1(X0,X1)) | ~v8_relat_2(k2_wellord1(X0,X1)) | ~v1_relat_2(k2_wellord1(X0,X1)) | ~v1_relat_1(k2_wellord1(X0,X1)) | ~v1_wellord1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(resolution,[],[f36,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_wellord1(k2_wellord1(X1,X0)) | ~v1_wellord1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1] : (v1_wellord1(k2_wellord1(X1,X0)) | ~v1_wellord1(X1) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1] : ((v1_wellord1(k2_wellord1(X1,X0)) | ~v1_wellord1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v1_wellord1(X1) => v1_wellord1(k2_wellord1(X1,X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_wellord1)).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_wellord1(X0) | v2_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ~v2_wellord1(k2_wellord1(sK1,sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (16958)------------------------------
% 0.22/0.50  % (16958)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (16958)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (16958)Memory used [KB]: 895
% 0.22/0.50  % (16958)Time elapsed: 0.069 s
% 0.22/0.50  % (16958)------------------------------
% 0.22/0.50  % (16958)------------------------------
% 0.22/0.51  % (16947)Success in time 0.143 s
%------------------------------------------------------------------------------
