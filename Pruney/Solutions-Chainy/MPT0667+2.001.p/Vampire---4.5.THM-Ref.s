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
% DateTime   : Thu Dec  3 12:53:20 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   44 (  60 expanded)
%              Number of leaves         :   10 (  17 expanded)
%              Depth                    :   14
%              Number of atoms          :  133 ( 189 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f53,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f32,f37,f42,f52])).

fof(f52,plain,
    ( spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f51])).

fof(f51,plain,
    ( $false
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f50,f31])).

fof(f31,plain,
    ( v2_funct_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl2_2
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f50,plain,
    ( ~ v2_funct_1(sK1)
    | spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f49,f36])).

fof(f36,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl2_3
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f49,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | spl2_1
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f48,f41])).

fof(f41,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl2_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f48,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | spl2_1 ),
    inference(resolution,[],[f47,f26])).

fof(f26,plain,
    ( ~ v2_funct_1(k7_relat_1(sK1,sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl2_1
  <=> v2_funct_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f46,f18])).

fof(f18,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f45,f17])).

% (30054)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
fof(f17,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k6_relat_1(X0))
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f44,f20])).

fof(f20,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k7_relat_1(X1,X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k6_relat_1(X0))
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k7_relat_1(X1,X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k6_relat_1(X0))
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f21,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f21,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => v2_funct_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_funct_1)).

fof(f42,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f13,f39])).

fof(f13,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ v2_funct_1(k7_relat_1(X1,X0))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ v2_funct_1(k7_relat_1(X1,X0))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => v2_funct_1(k7_relat_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => v2_funct_1(k7_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_funct_1)).

fof(f37,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f14,f34])).

fof(f14,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f32,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f15,f29])).

fof(f15,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f27,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f16,f24])).

fof(f16,plain,(
    ~ v2_funct_1(k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:20:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.42  % (30052)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.15/0.42  % (30055)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.15/0.42  % (30052)Refutation found. Thanks to Tanya!
% 0.15/0.42  % SZS status Theorem for theBenchmark
% 0.15/0.42  % SZS output start Proof for theBenchmark
% 0.15/0.42  fof(f53,plain,(
% 0.15/0.42    $false),
% 0.15/0.42    inference(avatar_sat_refutation,[],[f27,f32,f37,f42,f52])).
% 0.15/0.42  fof(f52,plain,(
% 0.15/0.42    spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4),
% 0.15/0.42    inference(avatar_contradiction_clause,[],[f51])).
% 0.15/0.42  fof(f51,plain,(
% 0.15/0.42    $false | (spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4)),
% 0.15/0.42    inference(subsumption_resolution,[],[f50,f31])).
% 0.15/0.42  fof(f31,plain,(
% 0.15/0.42    v2_funct_1(sK1) | ~spl2_2),
% 0.15/0.42    inference(avatar_component_clause,[],[f29])).
% 0.15/0.42  fof(f29,plain,(
% 0.15/0.42    spl2_2 <=> v2_funct_1(sK1)),
% 0.15/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.15/0.42  fof(f50,plain,(
% 0.15/0.42    ~v2_funct_1(sK1) | (spl2_1 | ~spl2_3 | ~spl2_4)),
% 0.15/0.42    inference(subsumption_resolution,[],[f49,f36])).
% 0.15/0.42  fof(f36,plain,(
% 0.15/0.42    v1_funct_1(sK1) | ~spl2_3),
% 0.15/0.42    inference(avatar_component_clause,[],[f34])).
% 0.15/0.42  fof(f34,plain,(
% 0.15/0.42    spl2_3 <=> v1_funct_1(sK1)),
% 0.15/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.15/0.42  fof(f49,plain,(
% 0.15/0.42    ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | (spl2_1 | ~spl2_4)),
% 0.15/0.42    inference(subsumption_resolution,[],[f48,f41])).
% 0.15/0.42  fof(f41,plain,(
% 0.15/0.42    v1_relat_1(sK1) | ~spl2_4),
% 0.15/0.42    inference(avatar_component_clause,[],[f39])).
% 0.15/0.42  fof(f39,plain,(
% 0.15/0.42    spl2_4 <=> v1_relat_1(sK1)),
% 0.15/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.15/0.42  fof(f48,plain,(
% 0.15/0.42    ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | spl2_1),
% 0.15/0.42    inference(resolution,[],[f47,f26])).
% 0.15/0.42  fof(f26,plain,(
% 0.15/0.42    ~v2_funct_1(k7_relat_1(sK1,sK0)) | spl2_1),
% 0.15/0.42    inference(avatar_component_clause,[],[f24])).
% 0.15/0.42  fof(f24,plain,(
% 0.15/0.42    spl2_1 <=> v2_funct_1(k7_relat_1(sK1,sK0))),
% 0.15/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.15/0.42  fof(f47,plain,(
% 0.15/0.42    ( ! [X0,X1] : (v2_funct_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X1)) )),
% 0.15/0.42    inference(subsumption_resolution,[],[f46,f18])).
% 0.15/0.42  fof(f18,plain,(
% 0.15/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.15/0.42    inference(cnf_transformation,[],[f1])).
% 0.15/0.42  fof(f1,axiom,(
% 0.15/0.42    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.15/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.15/0.42  fof(f46,plain,(
% 0.15/0.42    ( ! [X0,X1] : (v2_funct_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.15/0.42    inference(subsumption_resolution,[],[f45,f17])).
% 0.15/0.42  % (30054)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.15/0.42  fof(f17,plain,(
% 0.15/0.42    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.15/0.42    inference(cnf_transformation,[],[f5])).
% 0.15/0.42  fof(f5,axiom,(
% 0.15/0.42    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 0.15/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).
% 0.15/0.42  fof(f45,plain,(
% 0.15/0.42    ( ! [X0,X1] : (v2_funct_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k6_relat_1(X0)) | ~v2_funct_1(X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.15/0.42    inference(subsumption_resolution,[],[f44,f20])).
% 0.15/0.42  fof(f20,plain,(
% 0.15/0.42    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.15/0.42    inference(cnf_transformation,[],[f3])).
% 0.15/0.42  fof(f3,axiom,(
% 0.15/0.42    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.15/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.15/0.42  fof(f44,plain,(
% 0.15/0.42    ( ! [X0,X1] : (v2_funct_1(k7_relat_1(X1,X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k6_relat_1(X0)) | ~v2_funct_1(X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.15/0.42    inference(duplicate_literal_removal,[],[f43])).
% 0.15/0.42  fof(f43,plain,(
% 0.15/0.42    ( ! [X0,X1] : (v2_funct_1(k7_relat_1(X1,X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k6_relat_1(X0)) | ~v2_funct_1(X1) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.15/0.42    inference(superposition,[],[f21,f22])).
% 0.15/0.42  fof(f22,plain,(
% 0.15/0.42    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.15/0.42    inference(cnf_transformation,[],[f12])).
% 0.15/0.42  fof(f12,plain,(
% 0.15/0.42    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.15/0.42    inference(ennf_transformation,[],[f2])).
% 0.15/0.42  fof(f2,axiom,(
% 0.15/0.42    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.15/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.15/0.42  fof(f21,plain,(
% 0.15/0.42    ( ! [X0,X1] : (v2_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | ~v2_funct_1(X1) | ~v1_relat_1(X0)) )),
% 0.15/0.42    inference(cnf_transformation,[],[f11])).
% 0.15/0.42  fof(f11,plain,(
% 0.15/0.42    ! [X0] : (! [X1] : (v2_funct_1(k5_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.15/0.42    inference(flattening,[],[f10])).
% 0.15/0.42  fof(f10,plain,(
% 0.15/0.42    ! [X0] : (! [X1] : ((v2_funct_1(k5_relat_1(X0,X1)) | (~v2_funct_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.15/0.42    inference(ennf_transformation,[],[f4])).
% 0.15/0.42  fof(f4,axiom,(
% 0.15/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => v2_funct_1(k5_relat_1(X0,X1)))))),
% 0.15/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_funct_1)).
% 0.15/0.42  fof(f42,plain,(
% 0.15/0.42    spl2_4),
% 0.15/0.42    inference(avatar_split_clause,[],[f13,f39])).
% 0.15/0.42  fof(f13,plain,(
% 0.15/0.42    v1_relat_1(sK1)),
% 0.15/0.42    inference(cnf_transformation,[],[f9])).
% 0.15/0.42  fof(f9,plain,(
% 0.15/0.42    ? [X0,X1] : (~v2_funct_1(k7_relat_1(X1,X0)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.15/0.42    inference(flattening,[],[f8])).
% 0.15/0.42  fof(f8,plain,(
% 0.15/0.42    ? [X0,X1] : ((~v2_funct_1(k7_relat_1(X1,X0)) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.15/0.42    inference(ennf_transformation,[],[f7])).
% 0.15/0.42  fof(f7,negated_conjecture,(
% 0.15/0.42    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => v2_funct_1(k7_relat_1(X1,X0))))),
% 0.15/0.42    inference(negated_conjecture,[],[f6])).
% 0.15/0.42  fof(f6,conjecture,(
% 0.15/0.42    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => v2_funct_1(k7_relat_1(X1,X0))))),
% 0.15/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_funct_1)).
% 0.15/0.42  fof(f37,plain,(
% 0.15/0.42    spl2_3),
% 0.15/0.42    inference(avatar_split_clause,[],[f14,f34])).
% 0.15/0.42  fof(f14,plain,(
% 0.15/0.42    v1_funct_1(sK1)),
% 0.15/0.42    inference(cnf_transformation,[],[f9])).
% 0.15/0.42  fof(f32,plain,(
% 0.15/0.42    spl2_2),
% 0.15/0.42    inference(avatar_split_clause,[],[f15,f29])).
% 0.15/0.42  fof(f15,plain,(
% 0.15/0.42    v2_funct_1(sK1)),
% 0.15/0.42    inference(cnf_transformation,[],[f9])).
% 0.15/0.42  fof(f27,plain,(
% 0.15/0.42    ~spl2_1),
% 0.15/0.42    inference(avatar_split_clause,[],[f16,f24])).
% 0.15/0.42  fof(f16,plain,(
% 0.15/0.42    ~v2_funct_1(k7_relat_1(sK1,sK0))),
% 0.15/0.42    inference(cnf_transformation,[],[f9])).
% 0.15/0.42  % SZS output end Proof for theBenchmark
% 0.15/0.42  % (30052)------------------------------
% 0.15/0.42  % (30052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.42  % (30052)Termination reason: Refutation
% 0.15/0.42  
% 0.15/0.42  % (30052)Memory used [KB]: 10490
% 0.15/0.42  % (30052)Time elapsed: 0.005 s
% 0.15/0.42  % (30052)------------------------------
% 0.15/0.42  % (30052)------------------------------
% 0.15/0.42  % (30047)Success in time 0.061 s
%------------------------------------------------------------------------------
