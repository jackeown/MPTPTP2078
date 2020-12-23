%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 113 expanded)
%              Number of leaves         :   12 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  197 ( 374 expanded)
%              Number of equality atoms :   26 (  28 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f101,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f67,f71,f73,f84,f98,f100])).

fof(f100,plain,(
    spl1_11 ),
    inference(avatar_contradiction_clause,[],[f99])).

fof(f99,plain,
    ( $false
    | spl1_11 ),
    inference(resolution,[],[f97,f22])).

fof(f22,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

fof(f97,plain,
    ( ~ v2_funct_1(k6_relat_1(k2_relat_1(sK0)))
    | spl1_11 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl1_11
  <=> v2_funct_1(k6_relat_1(k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f98,plain,
    ( ~ spl1_6
    | ~ spl1_5
    | ~ spl1_11
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f94,f53,f96,f62,f65])).

fof(f65,plain,
    ( spl1_6
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f62,plain,
    ( spl1_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f53,plain,
    ( spl1_3
  <=> ! [X0] :
        ( k1_relat_1(X0) != k1_relat_1(sK0)
        | ~ v1_relat_1(X0)
        | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK0),X0))
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f94,plain,
    ( ~ v2_funct_1(k6_relat_1(k2_relat_1(sK0)))
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ spl1_3 ),
    inference(forward_demodulation,[],[f86,f42])).

fof(f42,plain,(
    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(global_subsumption,[],[f18,f19,f40])).

fof(f40,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(resolution,[],[f28,f20])).

fof(f20,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ~ v2_funct_1(k2_funct_1(X0))
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ~ v2_funct_1(k2_funct_1(X0))
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => v2_funct_1(k2_funct_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).

fof(f28,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f19,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f18,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f86,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ v1_funct_1(sK0)
    | ~ spl1_3 ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != k1_relat_1(sK0)
        | ~ v1_relat_1(X0)
        | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK0),X0))
        | ~ v1_funct_1(X0) )
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f84,plain,
    ( ~ spl1_5
    | ~ spl1_6
    | spl1_2 ),
    inference(avatar_split_clause,[],[f83,f50,f65,f62])).

fof(f50,plain,
    ( spl1_2
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f83,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_2 ),
    inference(resolution,[],[f51,f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f51,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f73,plain,(
    spl1_6 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | spl1_6 ),
    inference(resolution,[],[f66,f19])).

fof(f66,plain,
    ( ~ v1_funct_1(sK0)
    | spl1_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f71,plain,(
    spl1_5 ),
    inference(avatar_contradiction_clause,[],[f70])).

fof(f70,plain,
    ( $false
    | spl1_5 ),
    inference(resolution,[],[f63,f18])).

fof(f63,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_5 ),
    inference(avatar_component_clause,[],[f62])).

fof(f67,plain,
    ( ~ spl1_5
    | ~ spl1_6
    | spl1_1 ),
    inference(avatar_split_clause,[],[f60,f47,f65,f62])).

fof(f47,plain,
    ( spl1_1
  <=> v1_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f60,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_1 ),
    inference(resolution,[],[f48,f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f48,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f55,plain,
    ( ~ spl1_1
    | ~ spl1_2
    | spl1_3 ),
    inference(avatar_split_clause,[],[f45,f53,f50,f47])).

fof(f45,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != k1_relat_1(sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(k2_funct_1(sK0))
      | ~ v1_funct_1(k2_funct_1(sK0))
      | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK0),X0))
      | ~ v1_relat_1(X0) ) ),
    inference(global_subsumption,[],[f21,f43])).

fof(f43,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != k1_relat_1(sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(k2_funct_1(sK0))
      | ~ v1_funct_1(k2_funct_1(sK0))
      | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK0),X0))
      | ~ v1_relat_1(X0)
      | v2_funct_1(k2_funct_1(sK0)) ) ),
    inference(superposition,[],[f29,f36])).

fof(f36,plain,(
    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(global_subsumption,[],[f18,f19,f34])).

fof(f34,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f26,f20])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | v2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

fof(f21,plain,(
    ~ v2_funct_1(k2_funct_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:06:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (12601)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.48  % (12592)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.49  % (12609)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.49  % (12601)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f55,f67,f71,f73,f84,f98,f100])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    spl1_11),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f99])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    $false | spl1_11),
% 0.21/0.49    inference(resolution,[],[f97,f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ~v2_funct_1(k6_relat_1(k2_relat_1(sK0))) | spl1_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f96])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    spl1_11 <=> v2_funct_1(k6_relat_1(k2_relat_1(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ~spl1_6 | ~spl1_5 | ~spl1_11 | ~spl1_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f94,f53,f96,f62,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    spl1_6 <=> v1_funct_1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    spl1_5 <=> v1_relat_1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    spl1_3 <=> ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK0) | ~v1_relat_1(X0) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK0),X0)) | ~v1_funct_1(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ~v2_funct_1(k6_relat_1(k2_relat_1(sK0))) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~spl1_3),
% 0.21/0.49    inference(forward_demodulation,[],[f86,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))),
% 0.21/0.49    inference(global_subsumption,[],[f18,f19,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))),
% 0.21/0.49    inference(resolution,[],[f28,f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    v2_funct_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ? [X0] : (~v2_funct_1(k2_funct_1(X0)) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ? [X0] : ((~v2_funct_1(k2_funct_1(X0)) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 0.21/0.49    inference(negated_conjecture,[],[f6])).
% 0.21/0.49  fof(f6,conjecture,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    v1_funct_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    v1_relat_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    ~v1_relat_1(sK0) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK0),sK0)) | ~v1_funct_1(sK0) | ~spl1_3),
% 0.21/0.49    inference(equality_resolution,[],[f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK0) | ~v1_relat_1(X0) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK0),X0)) | ~v1_funct_1(X0)) ) | ~spl1_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f53])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ~spl1_5 | ~spl1_6 | spl1_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f83,f50,f65,f62])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    spl1_2 <=> v1_relat_1(k2_funct_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_2),
% 0.21/0.49    inference(resolution,[],[f51,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ~v1_relat_1(k2_funct_1(sK0)) | spl1_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f50])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    spl1_6),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    $false | spl1_6),
% 0.21/0.49    inference(resolution,[],[f66,f19])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ~v1_funct_1(sK0) | spl1_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f65])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    spl1_5),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f70])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    $false | spl1_5),
% 0.21/0.49    inference(resolution,[],[f63,f18])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ~v1_relat_1(sK0) | spl1_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f62])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ~spl1_5 | ~spl1_6 | spl1_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f60,f47,f65,f62])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    spl1_1 <=> v1_funct_1(k2_funct_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_1),
% 0.21/0.49    inference(resolution,[],[f48,f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ~v1_funct_1(k2_funct_1(sK0)) | spl1_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f47])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ~spl1_1 | ~spl1_2 | spl1_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f45,f53,f50,f47])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK0) | ~v1_funct_1(X0) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(k2_funct_1(sK0)) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK0),X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(global_subsumption,[],[f21,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK0) | ~v1_funct_1(X0) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(k2_funct_1(sK0)) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK0),X0)) | ~v1_relat_1(X0) | v2_funct_1(k2_funct_1(sK0))) )),
% 0.21/0.49    inference(superposition,[],[f29,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.21/0.49    inference(global_subsumption,[],[f18,f19,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.21/0.49    inference(resolution,[],[f26,f20])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X0) | v2_funct_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ~v2_funct_1(k2_funct_1(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (12601)------------------------------
% 0.21/0.49  % (12601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (12601)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (12601)Memory used [KB]: 10618
% 0.21/0.49  % (12601)Time elapsed: 0.066 s
% 0.21/0.49  % (12601)------------------------------
% 0.21/0.49  % (12601)------------------------------
% 0.21/0.49  % (12599)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.49  % (12585)Success in time 0.13 s
%------------------------------------------------------------------------------
