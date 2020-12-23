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
% DateTime   : Thu Dec  3 12:53:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   35 (  63 expanded)
%              Number of leaves         :    7 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :   93 ( 183 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f41,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f37,f40])).

fof(f40,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f39])).

fof(f39,plain,
    ( $false
    | spl2_2 ),
    inference(subsumption_resolution,[],[f38,f15])).

fof(f15,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_tarski(k1_relat_1(k8_relat_1(sK0,sK1)),k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f13])).

% (11783)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
fof(f13,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k1_relat_1(k8_relat_1(sK0,sK1)),k1_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_funct_1)).

fof(f38,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_2 ),
    inference(resolution,[],[f32,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

fof(f32,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK1),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl2_2
  <=> r1_tarski(k8_relat_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f37,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f36])).

fof(f36,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f35,f15])).

fof(f35,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_1 ),
    inference(subsumption_resolution,[],[f34,f16])).

fof(f16,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f34,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl2_1 ),
    inference(resolution,[],[f28,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_funct_1)).

fof(f28,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl2_1
  <=> v1_relat_1(k8_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f33,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f24,f30,f26])).

fof(f24,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK1),sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f23,f15])).

fof(f23,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK1),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f18,f17])).

fof(f17,plain,(
    ~ r1_tarski(k1_relat_1(k8_relat_1(sK0,sK1)),k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:15:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (11764)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.21/0.49  % (11775)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.21/0.49  % (11763)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.50  % (11770)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.50  % (11763)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f33,f37,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    spl2_2),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    $false | spl2_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f38,f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    v1_relat_1(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ~r1_tarski(k1_relat_1(k8_relat_1(sK0,sK1)),k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f13])).
% 0.21/0.50  % (11783)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0,X1] : (~r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k1_relat_1(k8_relat_1(sK0,sK1)),k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f7,plain,(
% 0.21/0.50    ? [X0,X1] : (~r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f6])).
% 0.21/0.50  fof(f6,plain,(
% 0.21/0.50    ? [X0,X1] : (~r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)))),
% 0.21/0.50    inference(negated_conjecture,[],[f4])).
% 0.21/0.50  fof(f4,conjecture,(
% 0.21/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_funct_1)).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ~v1_relat_1(sK1) | spl2_2),
% 0.21/0.50    inference(resolution,[],[f32,f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ~r1_tarski(k8_relat_1(sK0,sK1),sK1) | spl2_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    spl2_2 <=> r1_tarski(k8_relat_1(sK0,sK1),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    spl2_1),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    $false | spl2_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f35,f15])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ~v1_relat_1(sK1) | spl2_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f34,f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    v1_funct_1(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl2_1),
% 0.21/0.50    inference(resolution,[],[f28,f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1] : ((v1_funct_1(k8_relat_1(X0,X1)) & v1_relat_1(k8_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0,X1] : ((v1_funct_1(k8_relat_1(X0,X1)) & v1_relat_1(k8_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v1_funct_1(k8_relat_1(X0,X1)) & v1_relat_1(k8_relat_1(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_funct_1)).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ~v1_relat_1(k8_relat_1(sK0,sK1)) | spl2_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    spl2_1 <=> v1_relat_1(k8_relat_1(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ~spl2_1 | ~spl2_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f24,f30,f26])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ~r1_tarski(k8_relat_1(sK0,sK1),sK1) | ~v1_relat_1(k8_relat_1(sK0,sK1))),
% 0.21/0.50    inference(subsumption_resolution,[],[f23,f15])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ~r1_tarski(k8_relat_1(sK0,sK1),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(k8_relat_1(sK0,sK1))),
% 0.21/0.50    inference(resolution,[],[f18,f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ~r1_tarski(k1_relat_1(k8_relat_1(sK0,sK1)),k1_relat_1(sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f8])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (11763)------------------------------
% 0.21/0.50  % (11763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (11763)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (11763)Memory used [KB]: 5373
% 0.21/0.50  % (11763)Time elapsed: 0.072 s
% 0.21/0.50  % (11763)------------------------------
% 0.21/0.50  % (11763)------------------------------
% 0.21/0.50  % (11768)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.51  % (11762)Success in time 0.143 s
%------------------------------------------------------------------------------
