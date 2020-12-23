%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 108 expanded)
%              Number of leaves         :   17 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :  224 ( 370 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f99,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f38,f43,f47,f55,f56,f60,f64,f70,f86,f98])).

fof(f98,plain,
    ( spl2_1
    | ~ spl2_12 ),
    inference(avatar_contradiction_clause,[],[f97])).

fof(f97,plain,
    ( $false
    | spl2_1
    | ~ spl2_12 ),
    inference(resolution,[],[f85,f27])).

fof(f27,plain,
    ( ~ v2_funct_1(k7_relat_1(sK1,sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl2_1
  <=> v2_funct_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f85,plain,
    ( ! [X0] : v2_funct_1(k7_relat_1(sK1,X0))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl2_12
  <=> ! [X0] : v2_funct_1(k7_relat_1(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f86,plain,
    ( spl2_12
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f82,f68,f58,f53,f49,f45,f40,f35,f30,f84])).

fof(f30,plain,
    ( spl2_2
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f35,plain,
    ( spl2_3
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f40,plain,
    ( spl2_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f45,plain,
    ( spl2_5
  <=> ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f49,plain,
    ( spl2_6
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f53,plain,
    ( spl2_7
  <=> ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f58,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( v2_funct_1(k5_relat_1(X0,X1))
        | ~ v2_funct_1(X1)
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f68,plain,
    ( spl2_10
  <=> ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f82,plain,
    ( ! [X0] : v2_funct_1(k7_relat_1(sK1,X0))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f81,f50])).

fof(f50,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f49])).

fof(f81,plain,
    ( ! [X0] :
        ( v2_funct_1(k7_relat_1(sK1,X0))
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f80,f46])).

fof(f46,plain,
    ( ! [X0] : v1_funct_1(k6_relat_1(X0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f80,plain,
    ( ! [X0] :
        ( v2_funct_1(k7_relat_1(sK1,X0))
        | ~ v1_funct_1(k6_relat_1(X0))
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f79,f42])).

fof(f42,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f79,plain,
    ( ! [X0] :
        ( v2_funct_1(k7_relat_1(sK1,X0))
        | ~ v1_relat_1(sK1)
        | ~ v1_funct_1(k6_relat_1(X0))
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f78,f37])).

fof(f37,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f78,plain,
    ( ! [X0] :
        ( v2_funct_1(k7_relat_1(sK1,X0))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | ~ v1_funct_1(k6_relat_1(X0))
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f77,f54])).

fof(f54,plain,
    ( ! [X0] : v2_funct_1(k6_relat_1(X0))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f53])).

fof(f77,plain,
    ( ! [X0] :
        ( v2_funct_1(k7_relat_1(sK1,X0))
        | ~ v2_funct_1(k6_relat_1(X0))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | ~ v1_funct_1(k6_relat_1(X0))
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl2_2
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f75,f32])).

fof(f32,plain,
    ( v2_funct_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f75,plain,
    ( ! [X0] :
        ( v2_funct_1(k7_relat_1(sK1,X0))
        | ~ v2_funct_1(sK1)
        | ~ v2_funct_1(k6_relat_1(X0))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | ~ v1_funct_1(k6_relat_1(X0))
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(superposition,[],[f59,f69])).

fof(f69,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f68])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( v2_funct_1(k5_relat_1(X0,X1))
        | ~ v2_funct_1(X1)
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f58])).

fof(f70,plain,
    ( spl2_10
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f65,f62,f40,f68])).

fof(f62,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f65,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(resolution,[],[f63,f42])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f62])).

fof(f64,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f23,f62])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f60,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f22,f58])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k5_relat_1(X0,X1))
      | ~ v2_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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

fof(f56,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f20,f49])).

fof(f20,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f55,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f21,f53])).

fof(f21,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f47,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f19,f45])).

fof(f19,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f43,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f14,f40])).

fof(f14,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ v2_funct_1(k7_relat_1(sK1,sK0))
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( ~ v2_funct_1(k7_relat_1(X1,X0))
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ v2_funct_1(k7_relat_1(sK1,sK0))
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ v2_funct_1(k7_relat_1(X1,X0))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ v2_funct_1(k7_relat_1(X1,X0))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => v2_funct_1(k7_relat_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => v2_funct_1(k7_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_funct_1)).

fof(f38,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f15,f35])).

fof(f15,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f33,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f16,f30])).

fof(f16,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f28,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f17,f25])).

fof(f17,plain,(
    ~ v2_funct_1(k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:27:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.44  % (26494)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.44  % (26494)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f99,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f28,f33,f38,f43,f47,f55,f56,f60,f64,f70,f86,f98])).
% 0.22/0.44  fof(f98,plain,(
% 0.22/0.44    spl2_1 | ~spl2_12),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f97])).
% 0.22/0.44  fof(f97,plain,(
% 0.22/0.44    $false | (spl2_1 | ~spl2_12)),
% 0.22/0.44    inference(resolution,[],[f85,f27])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    ~v2_funct_1(k7_relat_1(sK1,sK0)) | spl2_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f25])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    spl2_1 <=> v2_funct_1(k7_relat_1(sK1,sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.44  fof(f85,plain,(
% 0.22/0.44    ( ! [X0] : (v2_funct_1(k7_relat_1(sK1,X0))) ) | ~spl2_12),
% 0.22/0.44    inference(avatar_component_clause,[],[f84])).
% 0.22/0.44  fof(f84,plain,(
% 0.22/0.44    spl2_12 <=> ! [X0] : v2_funct_1(k7_relat_1(sK1,X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.44  fof(f86,plain,(
% 0.22/0.44    spl2_12 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_7 | ~spl2_8 | ~spl2_10),
% 0.22/0.44    inference(avatar_split_clause,[],[f82,f68,f58,f53,f49,f45,f40,f35,f30,f84])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    spl2_2 <=> v2_funct_1(sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    spl2_3 <=> v1_funct_1(sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    spl2_4 <=> v1_relat_1(sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.44  fof(f45,plain,(
% 0.22/0.44    spl2_5 <=> ! [X0] : v1_funct_1(k6_relat_1(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.44  fof(f49,plain,(
% 0.22/0.44    spl2_6 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.44  fof(f53,plain,(
% 0.22/0.44    spl2_7 <=> ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.44  fof(f58,plain,(
% 0.22/0.44    spl2_8 <=> ! [X1,X0] : (v2_funct_1(k5_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.44  fof(f68,plain,(
% 0.22/0.44    spl2_10 <=> ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.44  fof(f82,plain,(
% 0.22/0.44    ( ! [X0] : (v2_funct_1(k7_relat_1(sK1,X0))) ) | (~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_7 | ~spl2_8 | ~spl2_10)),
% 0.22/0.44    inference(subsumption_resolution,[],[f81,f50])).
% 0.22/0.44  fof(f50,plain,(
% 0.22/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_6),
% 0.22/0.44    inference(avatar_component_clause,[],[f49])).
% 0.22/0.44  fof(f81,plain,(
% 0.22/0.44    ( ! [X0] : (v2_funct_1(k7_relat_1(sK1,X0)) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_7 | ~spl2_8 | ~spl2_10)),
% 0.22/0.44    inference(subsumption_resolution,[],[f80,f46])).
% 0.22/0.44  fof(f46,plain,(
% 0.22/0.44    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) ) | ~spl2_5),
% 0.22/0.44    inference(avatar_component_clause,[],[f45])).
% 0.22/0.44  fof(f80,plain,(
% 0.22/0.44    ( ! [X0] : (v2_funct_1(k7_relat_1(sK1,X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_7 | ~spl2_8 | ~spl2_10)),
% 0.22/0.44    inference(subsumption_resolution,[],[f79,f42])).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    v1_relat_1(sK1) | ~spl2_4),
% 0.22/0.44    inference(avatar_component_clause,[],[f40])).
% 0.22/0.44  fof(f79,plain,(
% 0.22/0.44    ( ! [X0] : (v2_funct_1(k7_relat_1(sK1,X0)) | ~v1_relat_1(sK1) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl2_2 | ~spl2_3 | ~spl2_7 | ~spl2_8 | ~spl2_10)),
% 0.22/0.44    inference(subsumption_resolution,[],[f78,f37])).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    v1_funct_1(sK1) | ~spl2_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f35])).
% 0.22/0.44  fof(f78,plain,(
% 0.22/0.44    ( ! [X0] : (v2_funct_1(k7_relat_1(sK1,X0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl2_2 | ~spl2_7 | ~spl2_8 | ~spl2_10)),
% 0.22/0.44    inference(subsumption_resolution,[],[f77,f54])).
% 0.22/0.44  fof(f54,plain,(
% 0.22/0.44    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) ) | ~spl2_7),
% 0.22/0.44    inference(avatar_component_clause,[],[f53])).
% 0.22/0.44  fof(f77,plain,(
% 0.22/0.44    ( ! [X0] : (v2_funct_1(k7_relat_1(sK1,X0)) | ~v2_funct_1(k6_relat_1(X0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl2_2 | ~spl2_8 | ~spl2_10)),
% 0.22/0.44    inference(subsumption_resolution,[],[f75,f32])).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    v2_funct_1(sK1) | ~spl2_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f30])).
% 0.22/0.44  fof(f75,plain,(
% 0.22/0.44    ( ! [X0] : (v2_funct_1(k7_relat_1(sK1,X0)) | ~v2_funct_1(sK1) | ~v2_funct_1(k6_relat_1(X0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl2_8 | ~spl2_10)),
% 0.22/0.44    inference(superposition,[],[f59,f69])).
% 0.22/0.44  fof(f69,plain,(
% 0.22/0.44    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)) ) | ~spl2_10),
% 0.22/0.44    inference(avatar_component_clause,[],[f68])).
% 0.22/0.44  fof(f59,plain,(
% 0.22/0.44    ( ! [X0,X1] : (v2_funct_1(k5_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl2_8),
% 0.22/0.44    inference(avatar_component_clause,[],[f58])).
% 0.22/0.44  fof(f70,plain,(
% 0.22/0.44    spl2_10 | ~spl2_4 | ~spl2_9),
% 0.22/0.44    inference(avatar_split_clause,[],[f65,f62,f40,f68])).
% 0.22/0.44  fof(f62,plain,(
% 0.22/0.44    spl2_9 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.44  fof(f65,plain,(
% 0.22/0.44    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)) ) | (~spl2_4 | ~spl2_9)),
% 0.22/0.44    inference(resolution,[],[f63,f42])).
% 0.22/0.44  fof(f63,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_9),
% 0.22/0.44    inference(avatar_component_clause,[],[f62])).
% 0.22/0.44  fof(f64,plain,(
% 0.22/0.44    spl2_9),
% 0.22/0.44    inference(avatar_split_clause,[],[f23,f62])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.22/0.44  fof(f60,plain,(
% 0.22/0.44    spl2_8),
% 0.22/0.44    inference(avatar_split_clause,[],[f22,f58])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ( ! [X0,X1] : (v2_funct_1(k5_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (v2_funct_1(k5_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(flattening,[],[f9])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : ((v2_funct_1(k5_relat_1(X0,X1)) | (~v2_funct_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => v2_funct_1(k5_relat_1(X0,X1)))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_funct_1)).
% 0.22/0.44  fof(f56,plain,(
% 0.22/0.44    spl2_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f20,f49])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.22/0.44  fof(f55,plain,(
% 0.22/0.44    spl2_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f21,f53])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f3])).
% 0.22/0.44  fof(f47,plain,(
% 0.22/0.44    spl2_5),
% 0.22/0.44    inference(avatar_split_clause,[],[f19,f45])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.44  fof(f43,plain,(
% 0.22/0.44    spl2_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f14,f40])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    v1_relat_1(sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ~v2_funct_1(k7_relat_1(sK1,sK0)) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ? [X0,X1] : (~v2_funct_1(k7_relat_1(X1,X0)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (~v2_funct_1(k7_relat_1(sK1,sK0)) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f8,plain,(
% 0.22/0.44    ? [X0,X1] : (~v2_funct_1(k7_relat_1(X1,X0)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.44    inference(flattening,[],[f7])).
% 0.22/0.44  fof(f7,plain,(
% 0.22/0.44    ? [X0,X1] : ((~v2_funct_1(k7_relat_1(X1,X0)) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.22/0.44    inference(ennf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => v2_funct_1(k7_relat_1(X1,X0))))),
% 0.22/0.44    inference(negated_conjecture,[],[f5])).
% 0.22/0.44  fof(f5,conjecture,(
% 0.22/0.44    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => v2_funct_1(k7_relat_1(X1,X0))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_funct_1)).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    spl2_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f15,f35])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    v1_funct_1(sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    spl2_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f16,f30])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    v2_funct_1(sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    ~spl2_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f17,f25])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ~v2_funct_1(k7_relat_1(sK1,sK0))),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (26494)------------------------------
% 0.22/0.44  % (26494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (26494)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (26494)Memory used [KB]: 10618
% 0.22/0.44  % (26494)Time elapsed: 0.006 s
% 0.22/0.44  % (26494)------------------------------
% 0.22/0.44  % (26494)------------------------------
% 0.22/0.44  % (26497)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.45  % (26488)Success in time 0.082 s
%------------------------------------------------------------------------------
