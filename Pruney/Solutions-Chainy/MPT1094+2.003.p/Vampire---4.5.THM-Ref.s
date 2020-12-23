%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:26 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 100 expanded)
%              Number of leaves         :   10 (  21 expanded)
%              Depth                    :   13
%              Number of atoms          :  188 ( 422 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f60,plain,(
    $false ),
    inference(subsumption_resolution,[],[f59,f29])).

fof(f29,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ~ v1_finset_1(sK0)
      | ~ v1_finset_1(k1_relat_1(sK0)) )
    & ( v1_finset_1(sK0)
      | v1_finset_1(k1_relat_1(sK0)) )
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ( ~ v1_finset_1(X0)
          | ~ v1_finset_1(k1_relat_1(X0)) )
        & ( v1_finset_1(X0)
          | v1_finset_1(k1_relat_1(X0)) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ v1_finset_1(sK0)
        | ~ v1_finset_1(k1_relat_1(sK0)) )
      & ( v1_finset_1(sK0)
        | v1_finset_1(k1_relat_1(sK0)) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(X0)
        | ~ v1_finset_1(k1_relat_1(X0)) )
      & ( v1_finset_1(X0)
        | v1_finset_1(k1_relat_1(X0)) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(X0)
        | ~ v1_finset_1(k1_relat_1(X0)) )
      & ( v1_finset_1(X0)
        | v1_finset_1(k1_relat_1(X0)) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ( v1_finset_1(k1_relat_1(X0))
      <~> v1_finset_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ( v1_finset_1(k1_relat_1(X0))
      <~> v1_finset_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v1_finset_1(k1_relat_1(X0))
        <=> v1_finset_1(X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_finset_1(k1_relat_1(X0))
      <=> v1_finset_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_finset_1)).

fof(f59,plain,(
    ~ v1_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f58,f51])).

fof(f51,plain,(
    ~ v1_finset_1(sK0) ),
    inference(subsumption_resolution,[],[f50,f28])).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,
    ( ~ v1_finset_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f49,f29])).

fof(f49,plain,
    ( ~ v1_finset_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(duplicate_literal_removal,[],[f48])).

fof(f48,plain,
    ( ~ v1_finset_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_finset_1(sK0) ),
    inference(resolution,[],[f47,f31])).

fof(f31,plain,
    ( ~ v1_finset_1(k1_relat_1(sK0))
    | ~ v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    ! [X0] :
      ( v1_finset_1(k1_relat_1(X0))
      | ~ v1_finset_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f46,f36])).

fof(f36,plain,(
    ! [X0,X1] : v1_relat_1(k7_funct_3(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_funct_1(k7_funct_3(X0,X1))
      & v1_relat_1(k7_funct_3(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_funct_3)).

fof(f46,plain,(
    ! [X0] :
      ( v1_finset_1(k1_relat_1(X0))
      | ~ v1_finset_1(X0)
      | ~ v1_relat_1(k7_funct_3(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f45,f37])).

fof(f37,plain,(
    ! [X0,X1] : v1_funct_1(k7_funct_3(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0] :
      ( v1_finset_1(k1_relat_1(X0))
      | ~ v1_finset_1(X0)
      | ~ v1_funct_1(k7_funct_3(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(k7_funct_3(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f38,f41])).

fof(f41,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k9_relat_1(k7_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f33,f35])).

fof(f35,plain,(
    ! [X0,X1] : k7_funct_3(X0,X1) = k9_funct_3(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k7_funct_3(X0,X1) = k9_funct_3(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_funct_3)).

fof(f33,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_funct_3)).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v1_finset_1(k9_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_finset_1)).

fof(f58,plain,
    ( v1_finset_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f57,f28])).

fof(f57,plain,
    ( ~ v1_relat_1(sK0)
    | v1_finset_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(duplicate_literal_removal,[],[f54])).

fof(f54,plain,
    ( ~ v1_relat_1(sK0)
    | v1_finset_1(sK0)
    | ~ v1_funct_1(sK0)
    | v1_finset_1(sK0) ),
    inference(resolution,[],[f53,f30])).

fof(f30,plain,
    ( v1_finset_1(k1_relat_1(sK0))
    | v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_finset_1(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_finset_1(X0)
      | ~ v1_funct_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( v1_finset_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_finset_1(k1_relat_1(X0))
      | ~ v1_finset_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f44,f34])).

fof(f34,plain,(
    ! [X0] :
      ( v1_finset_1(k2_relat_1(X0))
      | ~ v1_finset_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v1_finset_1(k2_relat_1(X0))
      | ~ v1_finset_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v1_finset_1(k2_relat_1(X0))
      | ~ v1_finset_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_finset_1(k1_relat_1(X0))
       => v1_finset_1(k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_finset_1)).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_finset_1(k2_relat_1(X0))
      | v1_finset_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_finset_1(k1_relat_1(X0)) ) ),
    inference(resolution,[],[f43,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_zfmisc_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_zfmisc_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_zfmisc_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_finset_1(X0) )
     => v1_finset_1(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_finset_1)).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_finset_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0)
      | v1_finset_1(X0) ) ),
    inference(resolution,[],[f32,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_finset_1(X1)
      | v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & r1_tarski(X0,X1) )
     => v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_finset_1)).

fof(f32,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:48:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.45  % (2403)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.45  % (2408)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.45  % (2406)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.45  % (2406)Refutation found. Thanks to Tanya!
% 0.19/0.45  % SZS status Theorem for theBenchmark
% 0.19/0.45  % (2418)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.46  % (2411)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.46  % (2414)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.19/0.46  % (2407)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.46  % SZS output start Proof for theBenchmark
% 0.19/0.46  fof(f60,plain,(
% 0.19/0.46    $false),
% 0.19/0.46    inference(subsumption_resolution,[],[f59,f29])).
% 0.19/0.46  fof(f29,plain,(
% 0.19/0.46    v1_funct_1(sK0)),
% 0.19/0.46    inference(cnf_transformation,[],[f27])).
% 0.19/0.46  fof(f27,plain,(
% 0.19/0.46    (~v1_finset_1(sK0) | ~v1_finset_1(k1_relat_1(sK0))) & (v1_finset_1(sK0) | v1_finset_1(k1_relat_1(sK0))) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.19/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 0.19/0.46  fof(f26,plain,(
% 0.19/0.46    ? [X0] : ((~v1_finset_1(X0) | ~v1_finset_1(k1_relat_1(X0))) & (v1_finset_1(X0) | v1_finset_1(k1_relat_1(X0))) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~v1_finset_1(sK0) | ~v1_finset_1(k1_relat_1(sK0))) & (v1_finset_1(sK0) | v1_finset_1(k1_relat_1(sK0))) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f25,plain,(
% 0.19/0.46    ? [X0] : ((~v1_finset_1(X0) | ~v1_finset_1(k1_relat_1(X0))) & (v1_finset_1(X0) | v1_finset_1(k1_relat_1(X0))) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.19/0.46    inference(flattening,[],[f24])).
% 0.19/0.46  fof(f24,plain,(
% 0.19/0.46    ? [X0] : (((~v1_finset_1(X0) | ~v1_finset_1(k1_relat_1(X0))) & (v1_finset_1(X0) | v1_finset_1(k1_relat_1(X0)))) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.19/0.46    inference(nnf_transformation,[],[f12])).
% 0.19/0.46  fof(f12,plain,(
% 0.19/0.46    ? [X0] : ((v1_finset_1(k1_relat_1(X0)) <~> v1_finset_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.19/0.46    inference(flattening,[],[f11])).
% 0.19/0.46  fof(f11,plain,(
% 0.19/0.46    ? [X0] : ((v1_finset_1(k1_relat_1(X0)) <~> v1_finset_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.19/0.46    inference(ennf_transformation,[],[f10])).
% 0.19/0.46  fof(f10,negated_conjecture,(
% 0.19/0.46    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_finset_1(k1_relat_1(X0)) <=> v1_finset_1(X0)))),
% 0.19/0.46    inference(negated_conjecture,[],[f9])).
% 0.19/0.46  fof(f9,conjecture,(
% 0.19/0.46    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_finset_1(k1_relat_1(X0)) <=> v1_finset_1(X0)))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_finset_1)).
% 0.19/0.46  fof(f59,plain,(
% 0.19/0.46    ~v1_funct_1(sK0)),
% 0.19/0.46    inference(subsumption_resolution,[],[f58,f51])).
% 0.19/0.46  fof(f51,plain,(
% 0.19/0.46    ~v1_finset_1(sK0)),
% 0.19/0.46    inference(subsumption_resolution,[],[f50,f28])).
% 0.19/0.46  fof(f28,plain,(
% 0.19/0.46    v1_relat_1(sK0)),
% 0.19/0.46    inference(cnf_transformation,[],[f27])).
% 0.19/0.46  fof(f50,plain,(
% 0.19/0.46    ~v1_finset_1(sK0) | ~v1_relat_1(sK0)),
% 0.19/0.46    inference(subsumption_resolution,[],[f49,f29])).
% 0.19/0.46  fof(f49,plain,(
% 0.19/0.46    ~v1_finset_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.19/0.46    inference(duplicate_literal_removal,[],[f48])).
% 0.19/0.46  fof(f48,plain,(
% 0.19/0.46    ~v1_finset_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_finset_1(sK0)),
% 0.19/0.46    inference(resolution,[],[f47,f31])).
% 0.19/0.46  fof(f31,plain,(
% 0.19/0.46    ~v1_finset_1(k1_relat_1(sK0)) | ~v1_finset_1(sK0)),
% 0.19/0.46    inference(cnf_transformation,[],[f27])).
% 0.19/0.46  fof(f47,plain,(
% 0.19/0.46    ( ! [X0] : (v1_finset_1(k1_relat_1(X0)) | ~v1_finset_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f46,f36])).
% 0.19/0.46  fof(f36,plain,(
% 0.19/0.46    ( ! [X0,X1] : (v1_relat_1(k7_funct_3(X0,X1))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f2])).
% 0.19/0.46  fof(f2,axiom,(
% 0.19/0.46    ! [X0,X1] : (v1_funct_1(k7_funct_3(X0,X1)) & v1_relat_1(k7_funct_3(X0,X1)))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_funct_3)).
% 0.19/0.46  fof(f46,plain,(
% 0.19/0.46    ( ! [X0] : (v1_finset_1(k1_relat_1(X0)) | ~v1_finset_1(X0) | ~v1_relat_1(k7_funct_3(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f45,f37])).
% 0.19/0.46  fof(f37,plain,(
% 0.19/0.46    ( ! [X0,X1] : (v1_funct_1(k7_funct_3(X0,X1))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f2])).
% 0.19/0.46  fof(f45,plain,(
% 0.19/0.46    ( ! [X0] : (v1_finset_1(k1_relat_1(X0)) | ~v1_finset_1(X0) | ~v1_funct_1(k7_funct_3(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(k7_funct_3(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.46    inference(superposition,[],[f38,f41])).
% 0.19/0.46  fof(f41,plain,(
% 0.19/0.46    ( ! [X0] : (k1_relat_1(X0) = k9_relat_1(k7_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.46    inference(forward_demodulation,[],[f33,f35])).
% 0.19/0.46  fof(f35,plain,(
% 0.19/0.46    ( ! [X0,X1] : (k7_funct_3(X0,X1) = k9_funct_3(X0,X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f5])).
% 0.19/0.46  fof(f5,axiom,(
% 0.19/0.46    ! [X0,X1] : k7_funct_3(X0,X1) = k9_funct_3(X0,X1)),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_funct_3)).
% 0.19/0.46  fof(f33,plain,(
% 0.19/0.46    ( ! [X0] : (k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f15])).
% 0.19/0.46  fof(f15,plain,(
% 0.19/0.46    ! [X0] : (k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.46    inference(flattening,[],[f14])).
% 0.19/0.46  fof(f14,plain,(
% 0.19/0.46    ! [X0] : (k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.46    inference(ennf_transformation,[],[f6])).
% 0.19/0.46  fof(f6,axiom,(
% 0.19/0.46    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_funct_3)).
% 0.19/0.46  fof(f38,plain,(
% 0.19/0.46    ( ! [X0,X1] : (v1_finset_1(k9_relat_1(X0,X1)) | ~v1_finset_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f19])).
% 0.19/0.46  fof(f19,plain,(
% 0.19/0.46    ! [X0,X1] : (v1_finset_1(k9_relat_1(X0,X1)) | ~v1_finset_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.46    inference(flattening,[],[f18])).
% 0.19/0.46  fof(f18,plain,(
% 0.19/0.46    ! [X0,X1] : (v1_finset_1(k9_relat_1(X0,X1)) | (~v1_finset_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.46    inference(ennf_transformation,[],[f3])).
% 0.19/0.46  fof(f3,axiom,(
% 0.19/0.46    ! [X0,X1] : ((v1_finset_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => v1_finset_1(k9_relat_1(X0,X1)))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_finset_1)).
% 0.19/0.46  fof(f58,plain,(
% 0.19/0.46    v1_finset_1(sK0) | ~v1_funct_1(sK0)),
% 0.19/0.46    inference(subsumption_resolution,[],[f57,f28])).
% 0.19/0.46  fof(f57,plain,(
% 0.19/0.46    ~v1_relat_1(sK0) | v1_finset_1(sK0) | ~v1_funct_1(sK0)),
% 0.19/0.46    inference(duplicate_literal_removal,[],[f54])).
% 0.19/0.46  fof(f54,plain,(
% 0.19/0.46    ~v1_relat_1(sK0) | v1_finset_1(sK0) | ~v1_funct_1(sK0) | v1_finset_1(sK0)),
% 0.19/0.46    inference(resolution,[],[f53,f30])).
% 0.19/0.46  fof(f30,plain,(
% 0.19/0.46    v1_finset_1(k1_relat_1(sK0)) | v1_finset_1(sK0)),
% 0.19/0.46    inference(cnf_transformation,[],[f27])).
% 0.19/0.46  fof(f53,plain,(
% 0.19/0.46    ( ! [X0] : (~v1_finset_1(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_finset_1(X0) | ~v1_funct_1(X0)) )),
% 0.19/0.46    inference(duplicate_literal_removal,[],[f52])).
% 0.19/0.46  fof(f52,plain,(
% 0.19/0.46    ( ! [X0] : (v1_finset_1(X0) | ~v1_relat_1(X0) | ~v1_finset_1(k1_relat_1(X0)) | ~v1_finset_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.46    inference(resolution,[],[f44,f34])).
% 0.19/0.46  fof(f34,plain,(
% 0.19/0.46    ( ! [X0] : (v1_finset_1(k2_relat_1(X0)) | ~v1_finset_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f17])).
% 0.19/0.46  fof(f17,plain,(
% 0.19/0.46    ! [X0] : (v1_finset_1(k2_relat_1(X0)) | ~v1_finset_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.46    inference(flattening,[],[f16])).
% 0.19/0.46  fof(f16,plain,(
% 0.19/0.46    ! [X0] : ((v1_finset_1(k2_relat_1(X0)) | ~v1_finset_1(k1_relat_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.46    inference(ennf_transformation,[],[f8])).
% 0.19/0.46  fof(f8,axiom,(
% 0.19/0.46    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_finset_1(k1_relat_1(X0)) => v1_finset_1(k2_relat_1(X0))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_finset_1)).
% 0.19/0.46  fof(f44,plain,(
% 0.19/0.46    ( ! [X0] : (~v1_finset_1(k2_relat_1(X0)) | v1_finset_1(X0) | ~v1_relat_1(X0) | ~v1_finset_1(k1_relat_1(X0))) )),
% 0.19/0.46    inference(resolution,[],[f43,f39])).
% 0.19/0.46  fof(f39,plain,(
% 0.19/0.46    ( ! [X0,X1] : (v1_finset_1(k2_zfmisc_1(X0,X1)) | ~v1_finset_1(X1) | ~v1_finset_1(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f21])).
% 0.19/0.46  fof(f21,plain,(
% 0.19/0.46    ! [X0,X1] : (v1_finset_1(k2_zfmisc_1(X0,X1)) | ~v1_finset_1(X1) | ~v1_finset_1(X0))),
% 0.19/0.46    inference(flattening,[],[f20])).
% 0.19/0.46  fof(f20,plain,(
% 0.19/0.46    ! [X0,X1] : (v1_finset_1(k2_zfmisc_1(X0,X1)) | (~v1_finset_1(X1) | ~v1_finset_1(X0)))),
% 0.19/0.46    inference(ennf_transformation,[],[f4])).
% 0.19/0.46  fof(f4,axiom,(
% 0.19/0.46    ! [X0,X1] : ((v1_finset_1(X1) & v1_finset_1(X0)) => v1_finset_1(k2_zfmisc_1(X0,X1)))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_finset_1)).
% 0.19/0.46  fof(f43,plain,(
% 0.19/0.46    ( ! [X0] : (~v1_finset_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0) | v1_finset_1(X0)) )),
% 0.19/0.46    inference(resolution,[],[f32,f40])).
% 0.19/0.46  fof(f40,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_finset_1(X1) | v1_finset_1(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f23])).
% 0.19/0.46  fof(f23,plain,(
% 0.19/0.46    ! [X0,X1] : (v1_finset_1(X0) | ~v1_finset_1(X1) | ~r1_tarski(X0,X1))),
% 0.19/0.46    inference(flattening,[],[f22])).
% 0.19/0.46  fof(f22,plain,(
% 0.19/0.46    ! [X0,X1] : (v1_finset_1(X0) | (~v1_finset_1(X1) | ~r1_tarski(X0,X1)))),
% 0.19/0.46    inference(ennf_transformation,[],[f7])).
% 0.19/0.46  fof(f7,axiom,(
% 0.19/0.46    ! [X0,X1] : ((v1_finset_1(X1) & r1_tarski(X0,X1)) => v1_finset_1(X0))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_finset_1)).
% 0.19/0.46  fof(f32,plain,(
% 0.19/0.46    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f13])).
% 0.19/0.46  fof(f13,plain,(
% 0.19/0.46    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.46    inference(ennf_transformation,[],[f1])).
% 0.19/0.46  fof(f1,axiom,(
% 0.19/0.46    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 0.19/0.46  % SZS output end Proof for theBenchmark
% 0.19/0.46  % (2406)------------------------------
% 0.19/0.46  % (2406)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (2406)Termination reason: Refutation
% 0.19/0.46  
% 0.19/0.46  % (2406)Memory used [KB]: 1663
% 0.19/0.46  % (2406)Time elapsed: 0.045 s
% 0.19/0.46  % (2406)------------------------------
% 0.19/0.46  % (2406)------------------------------
% 0.19/0.46  % (2410)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.46  % (2416)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.46  % (2402)Success in time 0.117 s
%------------------------------------------------------------------------------
