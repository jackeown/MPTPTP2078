%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 216 expanded)
%              Number of leaves         :   17 (  50 expanded)
%              Depth                    :   17
%              Number of atoms          :  256 ( 741 expanded)
%              Number of equality atoms :   83 ( 255 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f504,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f84,f92,f94,f159,f219,f245,f503])).

fof(f503,plain,(
    spl1_2 ),
    inference(avatar_contradiction_clause,[],[f502])).

fof(f502,plain,
    ( $false
    | spl1_2 ),
    inference(trivial_inequality_removal,[],[f493])).

fof(f493,plain,
    ( k2_relat_1(sK0) != k2_relat_1(sK0)
    | spl1_2 ),
    inference(superposition,[],[f46,f491])).

fof(f491,plain,(
    k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(forward_demodulation,[],[f490,f60])).

fof(f60,plain,(
    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(global_subsumption,[],[f26,f27,f59])).

fof(f59,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f38,f28])).

fof(f28,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
            & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

fof(f38,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f27,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f490,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(forward_demodulation,[],[f487,f112])).

fof(f112,plain,(
    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) ),
    inference(global_subsumption,[],[f26,f111])).

fof(f111,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(forward_demodulation,[],[f109,f62])).

fof(f62,plain,(
    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(global_subsumption,[],[f26,f27,f61])).

fof(f61,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f39,f28])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f109,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0))))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f54,f27])).

fof(f54,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | k2_funct_1(X1) = k5_relat_1(k2_funct_1(X1),k6_relat_1(k2_relat_1(k2_funct_1(X1))))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f33,f36])).

fof(f36,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f487,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0)))) ),
    inference(resolution,[],[f486,f26])).

fof(f486,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(X0)))) ) ),
    inference(global_subsumption,[],[f26,f480])).

fof(f480,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(X0))))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f479,f27])).

% (20045)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
fof(f479,plain,(
    ! [X4,X3] :
      ( ~ v1_funct_1(X4)
      | ~ v1_relat_1(X3)
      | k1_relat_1(k5_relat_1(k2_funct_1(X4),X3)) = k1_relat_1(k5_relat_1(k2_funct_1(X4),k6_relat_1(k1_relat_1(X3))))
      | ~ v1_relat_1(X4) ) ),
    inference(global_subsumption,[],[f326])).

fof(f326,plain,(
    ! [X4,X3] :
      ( ~ v1_relat_1(X3)
      | k1_relat_1(k5_relat_1(k2_funct_1(X4),X3)) = k1_relat_1(k5_relat_1(k2_funct_1(X4),k6_relat_1(k1_relat_1(X3))))
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f195,f36])).

fof(f195,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(k5_relat_1(X0,k6_relat_1(k1_relat_1(X1)))) ) ),
    inference(resolution,[],[f120,f29])).

fof(f29,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k6_relat_1(k1_relat_1(X0)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(k5_relat_1(X1,k6_relat_1(k1_relat_1(X0)))) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X1) != X0
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k6_relat_1(X0))
      | k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(k5_relat_1(X2,k6_relat_1(X0))) ) ),
    inference(superposition,[],[f34,f30])).

fof(f30,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
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
             => ( k1_relat_1(X0) = k1_relat_1(X1)
               => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).

fof(f46,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl1_2
  <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f245,plain,
    ( spl1_1
    | ~ spl1_13 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | spl1_1
    | ~ spl1_13 ),
    inference(trivial_inequality_removal,[],[f238])).

fof(f238,plain,
    ( k2_relat_1(sK0) != k2_relat_1(sK0)
    | spl1_1
    | ~ spl1_13 ),
    inference(superposition,[],[f43,f236])).

fof(f236,plain,
    ( k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ spl1_13 ),
    inference(forward_demodulation,[],[f235,f48])).

fof(f48,plain,(
    sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) ),
    inference(resolution,[],[f32,f26])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f235,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(k7_relat_1(sK0,k1_relat_1(sK0)))
    | ~ spl1_13 ),
    inference(forward_demodulation,[],[f232,f56])).

fof(f56,plain,(
    ! [X0] : k7_relat_1(sK0,X0) = k5_relat_1(k6_relat_1(X0),sK0) ),
    inference(resolution,[],[f40,f26])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

% (20046)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
fof(f232,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0))
    | ~ spl1_13 ),
    inference(resolution,[],[f156,f26])).

fof(f156,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) = k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),X0)) )
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl1_13
  <=> ! [X0] :
        ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) = k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f43,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl1_1
  <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f219,plain,
    ( ~ spl1_3
    | spl1_13
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f214,f152,f155,f70])).

fof(f70,plain,
    ( spl1_3
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f152,plain,
    ( spl1_12
  <=> v1_relat_1(k6_relat_1(k1_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f214,plain,(
    ! [X2] :
      ( ~ v1_relat_1(k6_relat_1(k1_relat_1(sK0)))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k2_funct_1(sK0))
      | k2_relat_1(k5_relat_1(k2_funct_1(sK0),X2)) = k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),X2)) ) ),
    inference(superposition,[],[f137,f62])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k6_relat_1(k2_relat_1(X0)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(X0)),X1)) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X1) != X0
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k6_relat_1(X0))
      | k2_relat_1(k5_relat_1(X1,X2)) = k2_relat_1(k5_relat_1(k6_relat_1(X0),X2)) ) ),
    inference(superposition,[],[f35,f31])).

fof(f31,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X0) != k2_relat_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k2_relat_1(X0) = k2_relat_1(X1)
               => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t199_relat_1)).

fof(f159,plain,(
    spl1_12 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | spl1_12 ),
    inference(resolution,[],[f153,f29])).

fof(f153,plain,
    ( ~ v1_relat_1(k6_relat_1(k1_relat_1(sK0)))
    | spl1_12 ),
    inference(avatar_component_clause,[],[f152])).

fof(f94,plain,(
    spl1_6 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl1_6 ),
    inference(resolution,[],[f83,f27])).

fof(f83,plain,
    ( ~ v1_funct_1(sK0)
    | spl1_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl1_6
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f92,plain,(
    spl1_5 ),
    inference(avatar_contradiction_clause,[],[f91])).

fof(f91,plain,
    ( $false
    | spl1_5 ),
    inference(resolution,[],[f80,f26])).

fof(f80,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl1_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f84,plain,
    ( ~ spl1_5
    | ~ spl1_6
    | spl1_3 ),
    inference(avatar_split_clause,[],[f77,f70,f82,f79])).

fof(f77,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_3 ),
    inference(resolution,[],[f71,f36])).

fof(f71,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | spl1_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f47,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f25,f45,f42])).

fof(f25,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:57:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.46  % (20048)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.47  % (20050)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.47  % (20038)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.48  % (20044)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.49  % (20043)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (20041)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.49  % (20043)Refutation not found, incomplete strategy% (20043)------------------------------
% 0.20/0.49  % (20043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (20043)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (20043)Memory used [KB]: 6140
% 0.20/0.49  % (20043)Time elapsed: 0.098 s
% 0.20/0.49  % (20043)------------------------------
% 0.20/0.49  % (20043)------------------------------
% 0.20/0.49  % (20037)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.50  % (20040)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.50  % (20057)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.50  % (20039)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.50  % (20042)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.50  % (20039)Refutation not found, incomplete strategy% (20039)------------------------------
% 0.20/0.50  % (20039)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (20039)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (20039)Memory used [KB]: 10490
% 0.20/0.50  % (20039)Time elapsed: 0.104 s
% 0.20/0.50  % (20039)------------------------------
% 0.20/0.50  % (20039)------------------------------
% 0.20/0.51  % (20056)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.51  % (20049)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.51  % (20058)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.51  % (20048)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f504,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f47,f84,f92,f94,f159,f219,f245,f503])).
% 0.20/0.51  fof(f503,plain,(
% 0.20/0.51    spl1_2),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f502])).
% 0.20/0.51  fof(f502,plain,(
% 0.20/0.51    $false | spl1_2),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f493])).
% 0.20/0.51  fof(f493,plain,(
% 0.20/0.51    k2_relat_1(sK0) != k2_relat_1(sK0) | spl1_2),
% 0.20/0.51    inference(superposition,[],[f46,f491])).
% 0.20/0.51  fof(f491,plain,(
% 0.20/0.51    k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.20/0.51    inference(forward_demodulation,[],[f490,f60])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.20/0.51    inference(global_subsumption,[],[f26,f27,f59])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.20/0.51    inference(resolution,[],[f38,f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    v2_funct_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ? [X0] : (((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 0.20/0.51    inference(negated_conjecture,[],[f10])).
% 0.20/0.51  fof(f10,conjecture,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    v1_funct_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    v1_relat_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f490,plain,(
% 0.20/0.51    k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k1_relat_1(k2_funct_1(sK0))),
% 0.20/0.51    inference(forward_demodulation,[],[f487,f112])).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0)))),
% 0.20/0.51    inference(global_subsumption,[],[f26,f111])).
% 0.20/0.51  fof(f111,plain,(
% 0.20/0.51    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) | ~v1_relat_1(sK0)),
% 0.20/0.51    inference(forward_demodulation,[],[f109,f62])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.20/0.51    inference(global_subsumption,[],[f26,f27,f61])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.20/0.51    inference(resolution,[],[f39,f28])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f109,plain,(
% 0.20/0.51    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) | ~v1_relat_1(sK0)),
% 0.20/0.51    inference(resolution,[],[f54,f27])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ( ! [X1] : (~v1_funct_1(X1) | k2_funct_1(X1) = k5_relat_1(k2_funct_1(X1),k6_relat_1(k2_relat_1(k2_funct_1(X1)))) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(resolution,[],[f33,f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 0.20/0.51  fof(f487,plain,(
% 0.20/0.51    k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))))),
% 0.20/0.51    inference(resolution,[],[f486,f26])).
% 0.20/0.51  fof(f486,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(X0))))) )),
% 0.20/0.51    inference(global_subsumption,[],[f26,f480])).
% 0.20/0.51  fof(f480,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(X0)))) | ~v1_relat_1(sK0)) )),
% 0.20/0.51    inference(resolution,[],[f479,f27])).
% 0.20/0.51  % (20045)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.51  fof(f479,plain,(
% 0.20/0.51    ( ! [X4,X3] : (~v1_funct_1(X4) | ~v1_relat_1(X3) | k1_relat_1(k5_relat_1(k2_funct_1(X4),X3)) = k1_relat_1(k5_relat_1(k2_funct_1(X4),k6_relat_1(k1_relat_1(X3)))) | ~v1_relat_1(X4)) )),
% 0.20/0.51    inference(global_subsumption,[],[f326])).
% 0.20/0.51  fof(f326,plain,(
% 0.20/0.51    ( ! [X4,X3] : (~v1_relat_1(X3) | k1_relat_1(k5_relat_1(k2_funct_1(X4),X3)) = k1_relat_1(k5_relat_1(k2_funct_1(X4),k6_relat_1(k1_relat_1(X3)))) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) )),
% 0.20/0.51    inference(resolution,[],[f195,f36])).
% 0.20/0.51  fof(f195,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(k5_relat_1(X0,k6_relat_1(k1_relat_1(X1))))) )),
% 0.20/0.51    inference(resolution,[],[f120,f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(k6_relat_1(k1_relat_1(X0))) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(k5_relat_1(X1,k6_relat_1(k1_relat_1(X0))))) )),
% 0.20/0.51    inference(equality_resolution,[],[f63])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k1_relat_1(X1) != X0 | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(k6_relat_1(X0)) | k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(k5_relat_1(X2,k6_relat_1(X0)))) )),
% 0.20/0.51    inference(superposition,[],[f34,f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k1_relat_1(X0) = k1_relat_1(X1) => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | spl1_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    spl1_2 <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.51  fof(f245,plain,(
% 0.20/0.51    spl1_1 | ~spl1_13),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f244])).
% 0.20/0.51  fof(f244,plain,(
% 0.20/0.51    $false | (spl1_1 | ~spl1_13)),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f238])).
% 0.20/0.51  fof(f238,plain,(
% 0.20/0.51    k2_relat_1(sK0) != k2_relat_1(sK0) | (spl1_1 | ~spl1_13)),
% 0.20/0.51    inference(superposition,[],[f43,f236])).
% 0.20/0.51  fof(f236,plain,(
% 0.20/0.51    k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | ~spl1_13),
% 0.20/0.51    inference(forward_demodulation,[],[f235,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    sK0 = k7_relat_1(sK0,k1_relat_1(sK0))),
% 0.20/0.51    inference(resolution,[],[f32,f26])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 0.20/0.51  fof(f235,plain,(
% 0.20/0.51    k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(k7_relat_1(sK0,k1_relat_1(sK0))) | ~spl1_13),
% 0.20/0.51    inference(forward_demodulation,[],[f232,f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ( ! [X0] : (k7_relat_1(sK0,X0) = k5_relat_1(k6_relat_1(X0),sK0)) )),
% 0.20/0.51    inference(resolution,[],[f40,f26])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.20/0.51  % (20046)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.51  fof(f232,plain,(
% 0.20/0.51    k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0)) | ~spl1_13),
% 0.20/0.51    inference(resolution,[],[f156,f26])).
% 0.20/0.51  fof(f156,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) = k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),X0))) ) | ~spl1_13),
% 0.20/0.51    inference(avatar_component_clause,[],[f155])).
% 0.20/0.51  fof(f155,plain,(
% 0.20/0.51    spl1_13 <=> ! [X0] : (k2_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) = k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),X0)) | ~v1_relat_1(X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | spl1_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    spl1_1 <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.51  fof(f219,plain,(
% 0.20/0.51    ~spl1_3 | spl1_13 | ~spl1_12),
% 0.20/0.51    inference(avatar_split_clause,[],[f214,f152,f155,f70])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    spl1_3 <=> v1_relat_1(k2_funct_1(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.20/0.51  fof(f152,plain,(
% 0.20/0.51    spl1_12 <=> v1_relat_1(k6_relat_1(k1_relat_1(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.20/0.51  fof(f214,plain,(
% 0.20/0.51    ( ! [X2] : (~v1_relat_1(k6_relat_1(k1_relat_1(sK0))) | ~v1_relat_1(X2) | ~v1_relat_1(k2_funct_1(sK0)) | k2_relat_1(k5_relat_1(k2_funct_1(sK0),X2)) = k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),X2))) )),
% 0.20/0.51    inference(superposition,[],[f137,f62])).
% 0.20/0.51  fof(f137,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(k6_relat_1(k2_relat_1(X0))) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(X0)),X1))) )),
% 0.20/0.51    inference(equality_resolution,[],[f85])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k2_relat_1(X1) != X0 | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(k6_relat_1(X0)) | k2_relat_1(k5_relat_1(X1,X2)) = k2_relat_1(k5_relat_1(k6_relat_1(X0),X2))) )),
% 0.20/0.51    inference(superposition,[],[f35,f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k2_relat_1(X0) = k2_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t199_relat_1)).
% 0.20/0.51  fof(f159,plain,(
% 0.20/0.51    spl1_12),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f158])).
% 0.20/0.51  fof(f158,plain,(
% 0.20/0.51    $false | spl1_12),
% 0.20/0.51    inference(resolution,[],[f153,f29])).
% 0.20/0.51  fof(f153,plain,(
% 0.20/0.51    ~v1_relat_1(k6_relat_1(k1_relat_1(sK0))) | spl1_12),
% 0.20/0.51    inference(avatar_component_clause,[],[f152])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    spl1_6),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f93])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    $false | spl1_6),
% 0.20/0.51    inference(resolution,[],[f83,f27])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    ~v1_funct_1(sK0) | spl1_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f82])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    spl1_6 <=> v1_funct_1(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    spl1_5),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f91])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    $false | spl1_5),
% 0.20/0.51    inference(resolution,[],[f80,f26])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    ~v1_relat_1(sK0) | spl1_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f79])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    spl1_5 <=> v1_relat_1(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    ~spl1_5 | ~spl1_6 | spl1_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f77,f70,f82,f79])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_3),
% 0.20/0.51    inference(resolution,[],[f71,f36])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    ~v1_relat_1(k2_funct_1(sK0)) | spl1_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f70])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ~spl1_1 | ~spl1_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f25,f45,f42])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (20048)------------------------------
% 0.20/0.51  % (20048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (20048)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (20048)Memory used [KB]: 11129
% 0.20/0.51  % (20048)Time elapsed: 0.098 s
% 0.20/0.51  % (20048)------------------------------
% 0.20/0.51  % (20048)------------------------------
% 0.20/0.51  % (20046)Refutation not found, incomplete strategy% (20046)------------------------------
% 0.20/0.51  % (20046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (20046)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (20046)Memory used [KB]: 10618
% 0.20/0.51  % (20046)Time elapsed: 0.121 s
% 0.20/0.51  % (20046)------------------------------
% 0.20/0.51  % (20046)------------------------------
% 0.20/0.51  % (20035)Success in time 0.162 s
%------------------------------------------------------------------------------
