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
% DateTime   : Thu Dec  3 12:59:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   35 (  46 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :   12
%              Number of atoms          :  105 ( 130 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f40,plain,(
    $false ),
    inference(subsumption_resolution,[],[f39,f23])).

fof(f23,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f39,plain,(
    ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(subsumption_resolution,[],[f38,f21])).

fof(f21,plain,(
    ! [X0] : v1_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_wellord2)).

fof(f38,plain,
    ( ~ v1_relat_2(k1_wellord2(sK0))
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(subsumption_resolution,[],[f37,f22])).

fof(f22,plain,(
    ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_wellord2)).

fof(f37,plain,
    ( ~ v8_relat_2(k1_wellord2(sK0))
    | ~ v1_relat_2(k1_wellord2(sK0))
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(subsumption_resolution,[],[f36,f20])).

fof(f20,plain,(
    ! [X0] : v4_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v4_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_wellord2)).

fof(f36,plain,
    ( ~ v4_relat_2(k1_wellord2(sK0))
    | ~ v8_relat_2(k1_wellord2(sK0))
    | ~ v1_relat_2(k1_wellord2(sK0))
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(subsumption_resolution,[],[f35,f32])).

fof(f32,plain,(
    v6_relat_2(k1_wellord2(sK0)) ),
    inference(resolution,[],[f30,f18])).

fof(f18,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ v2_wellord1(k1_wellord2(sK0))
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ~ v2_wellord1(k1_wellord2(X0))
        & v3_ordinal1(X0) )
   => ( ~ v2_wellord1(k1_wellord2(sK0))
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ~ v2_wellord1(k1_wellord2(X0))
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => v2_wellord1(k1_wellord2(X0)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

fof(f30,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v6_relat_2(k1_wellord2(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v6_relat_2(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v6_relat_2(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_wellord2)).

fof(f35,plain,
    ( ~ v6_relat_2(k1_wellord2(sK0))
    | ~ v4_relat_2(k1_wellord2(sK0))
    | ~ v8_relat_2(k1_wellord2(sK0))
    | ~ v1_relat_2(k1_wellord2(sK0))
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(subsumption_resolution,[],[f34,f19])).

fof(f19,plain,(
    ~ v2_wellord1(k1_wellord2(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f34,plain,
    ( v2_wellord1(k1_wellord2(sK0))
    | ~ v6_relat_2(k1_wellord2(sK0))
    | ~ v4_relat_2(k1_wellord2(sK0))
    | ~ v8_relat_2(k1_wellord2(sK0))
    | ~ v1_relat_2(k1_wellord2(sK0))
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(resolution,[],[f33,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_wellord1(X0)
      | v2_wellord1(X0)
      | ~ v6_relat_2(X0)
      | ~ v4_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).

fof(f33,plain,(
    v1_wellord1(k1_wellord2(sK0)) ),
    inference(resolution,[],[f31,f18])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v1_wellord1(k1_wellord2(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

% (4864)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% (4849)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
fof(f13,plain,(
    ! [X0] :
      ( v1_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_wellord2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:56:26 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.21/0.43  % (4850)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.46  % (4856)WARNING: option uwaf not known.
% 0.21/0.46  % (4856)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.21/0.46  % (4856)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(subsumption_resolution,[],[f39,f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ~v1_relat_1(k1_wellord2(sK0))),
% 0.21/0.46    inference(subsumption_resolution,[],[f38,f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ( ! [X0] : (v1_relat_2(k1_wellord2(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0] : v1_relat_2(k1_wellord2(X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_wellord2)).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ~v1_relat_2(k1_wellord2(sK0)) | ~v1_relat_1(k1_wellord2(sK0))),
% 0.21/0.46    inference(subsumption_resolution,[],[f37,f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ( ! [X0] : (v8_relat_2(k1_wellord2(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0] : v8_relat_2(k1_wellord2(X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_wellord2)).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ~v8_relat_2(k1_wellord2(sK0)) | ~v1_relat_2(k1_wellord2(sK0)) | ~v1_relat_1(k1_wellord2(sK0))),
% 0.21/0.46    inference(subsumption_resolution,[],[f36,f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ( ! [X0] : (v4_relat_2(k1_wellord2(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0] : v4_relat_2(k1_wellord2(X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_wellord2)).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ~v4_relat_2(k1_wellord2(sK0)) | ~v8_relat_2(k1_wellord2(sK0)) | ~v1_relat_2(k1_wellord2(sK0)) | ~v1_relat_1(k1_wellord2(sK0))),
% 0.21/0.46    inference(subsumption_resolution,[],[f35,f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    v6_relat_2(k1_wellord2(sK0))),
% 0.21/0.46    inference(resolution,[],[f30,f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    v3_ordinal1(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ~v2_wellord1(k1_wellord2(sK0)) & v3_ordinal1(sK0)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ? [X0] : (~v2_wellord1(k1_wellord2(X0)) & v3_ordinal1(X0)) => (~v2_wellord1(k1_wellord2(sK0)) & v3_ordinal1(sK0))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ? [X0] : (~v2_wellord1(k1_wellord2(X0)) & v3_ordinal1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,negated_conjecture,(
% 0.21/0.46    ~! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 0.21/0.46    inference(negated_conjecture,[],[f8])).
% 0.21/0.46  fof(f8,conjecture,(
% 0.21/0.46    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ( ! [X0] : (~v3_ordinal1(X0) | v6_relat_2(k1_wellord2(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0] : (v6_relat_2(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0] : (v3_ordinal1(X0) => v6_relat_2(k1_wellord2(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_wellord2)).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ~v6_relat_2(k1_wellord2(sK0)) | ~v4_relat_2(k1_wellord2(sK0)) | ~v8_relat_2(k1_wellord2(sK0)) | ~v1_relat_2(k1_wellord2(sK0)) | ~v1_relat_1(k1_wellord2(sK0))),
% 0.21/0.46    inference(subsumption_resolution,[],[f34,f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ~v2_wellord1(k1_wellord2(sK0))),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    v2_wellord1(k1_wellord2(sK0)) | ~v6_relat_2(k1_wellord2(sK0)) | ~v4_relat_2(k1_wellord2(sK0)) | ~v8_relat_2(k1_wellord2(sK0)) | ~v1_relat_2(k1_wellord2(sK0)) | ~v1_relat_1(k1_wellord2(sK0))),
% 0.21/0.46    inference(resolution,[],[f33,f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_wellord1(X0) | v2_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0] : (((v2_wellord1(X0) | ~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0)) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(flattening,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0] : (((v2_wellord1(X0) | (~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0))) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(nnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0] : ((v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    v1_wellord1(k1_wellord2(sK0))),
% 0.21/0.46    inference(resolution,[],[f31,f18])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ( ! [X0] : (~v3_ordinal1(X0) | v1_wellord1(k1_wellord2(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  % (4864)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (4849)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (v1_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : (v3_ordinal1(X0) => v1_wellord1(k1_wellord2(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_wellord2)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (4856)------------------------------
% 0.21/0.48  % (4856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (4856)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (4856)Memory used [KB]: 895
% 0.21/0.48  % (4856)Time elapsed: 0.047 s
% 0.21/0.48  % (4856)------------------------------
% 0.21/0.48  % (4856)------------------------------
% 0.21/0.48  % (4845)Success in time 0.103 s
%------------------------------------------------------------------------------
