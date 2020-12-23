%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 194 expanded)
%              Number of leaves         :   14 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :  268 ( 679 expanded)
%              Number of equality atoms :   65 ( 166 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f117,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f63,f67,f69,f75,f77,f80,f110,f116])).

fof(f116,plain,(
    ~ spl1_12 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | ~ spl1_12 ),
    inference(trivial_inequality_removal,[],[f112])).

fof(f112,plain,
    ( sK0 != sK0
    | ~ spl1_12 ),
    inference(superposition,[],[f23,f109])).

fof(f109,plain,
    ( sK0 = k2_funct_1(k2_funct_1(sK0))
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl1_12
  <=> sK0 = k2_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f23,plain,(
    sK0 != k2_funct_1(k2_funct_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( k2_funct_1(k2_funct_1(X0)) != X0
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( k2_funct_1(k2_funct_1(X0)) != X0
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f110,plain,
    ( ~ spl1_5
    | ~ spl1_6
    | spl1_12
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f106,f73,f108,f61,f58])).

% (6405)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f58,plain,
    ( spl1_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f61,plain,
    ( spl1_6
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f73,plain,
    ( spl1_7
  <=> ! [X0] :
        ( k1_relat_1(X0) != k1_relat_1(sK0)
        | k2_funct_1(k2_funct_1(sK0)) = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(k2_funct_1(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f106,plain,
    ( sK0 = k2_funct_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_7 ),
    inference(trivial_inequality_removal,[],[f105])).

fof(f105,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k2_relat_1(sK0))
    | sK0 = k2_funct_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) != k1_relat_1(sK0)
    | ~ spl1_7 ),
    inference(superposition,[],[f74,f39])).

fof(f39,plain,(
    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(global_subsumption,[],[f20,f21,f38])).

fof(f38,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(resolution,[],[f29,f22])).

fof(f22,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f21,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f20,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f74,plain,
    ( ! [X0] :
        ( k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(k2_funct_1(sK0),X0)
        | k2_funct_1(k2_funct_1(sK0)) = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) != k1_relat_1(sK0) )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f80,plain,
    ( ~ spl1_5
    | ~ spl1_6
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f79,f53,f61,f58])).

fof(f53,plain,
    ( spl1_4
  <=> ! [X0] :
        ( k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(k2_funct_1(sK0),X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f79,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(trivial_inequality_removal,[],[f78])).

fof(f78,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k2_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(superposition,[],[f54,f39])).

% (6408)Refutation not found, incomplete strategy% (6408)------------------------------
% (6408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6408)Termination reason: Refutation not found, incomplete strategy

fof(f54,plain,
    ( ! [X0] :
        ( k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(k2_funct_1(sK0),X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f77,plain,
    ( ~ spl1_5
    | ~ spl1_6
    | spl1_3 ),
    inference(avatar_split_clause,[],[f76,f50,f61,f58])).

% (6408)Memory used [KB]: 10490
% (6408)Time elapsed: 0.054 s
fof(f50,plain,
    ( spl1_3
  <=> v1_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

% (6408)------------------------------
% (6408)------------------------------
fof(f76,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_3 ),
    inference(resolution,[],[f51,f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f51,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | spl1_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f75,plain,
    ( ~ spl1_2
    | ~ spl1_1
    | ~ spl1_3
    | spl1_7 ),
    inference(avatar_split_clause,[],[f70,f73,f50,f44,f47])).

fof(f47,plain,
    ( spl1_2
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f44,plain,
    ( spl1_1
  <=> v2_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f70,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != k1_relat_1(sK0)
      | k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(k2_funct_1(sK0),X0)
      | ~ v1_funct_1(k2_funct_1(sK0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(k2_funct_1(sK0))
      | ~ v1_relat_1(k2_funct_1(sK0))
      | k2_funct_1(k2_funct_1(sK0)) = X0 ) ),
    inference(forward_demodulation,[],[f65,f35])).

fof(f35,plain,(
    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(global_subsumption,[],[f20,f21,f34])).

fof(f34,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f27,f22])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f65,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(k2_funct_1(sK0),X0)
      | ~ v1_funct_1(k2_funct_1(sK0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(k2_funct_1(sK0))
      | k1_relat_1(X0) != k2_relat_1(k2_funct_1(sK0))
      | ~ v1_relat_1(k2_funct_1(sK0))
      | k2_funct_1(k2_funct_1(sK0)) = X0 ) ),
    inference(superposition,[],[f31,f33])).

fof(f33,plain,(
    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(global_subsumption,[],[f20,f21,f32])).

fof(f32,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f26,f22])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

fof(f69,plain,(
    spl1_6 ),
    inference(avatar_contradiction_clause,[],[f68])).

fof(f68,plain,
    ( $false
    | spl1_6 ),
    inference(resolution,[],[f62,f21])).

fof(f62,plain,
    ( ~ v1_funct_1(sK0)
    | spl1_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f67,plain,(
    spl1_5 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | spl1_5 ),
    inference(resolution,[],[f59,f20])).

fof(f59,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f63,plain,
    ( ~ spl1_5
    | ~ spl1_6
    | spl1_2 ),
    inference(avatar_split_clause,[],[f56,f47,f61,f58])).

fof(f56,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_2 ),
    inference(resolution,[],[f48,f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f48,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f55,plain,
    ( spl1_1
    | ~ spl1_2
    | ~ spl1_3
    | spl1_4 ),
    inference(avatar_split_clause,[],[f41,f53,f50,f47,f44])).

fof(f41,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(k2_funct_1(sK0),X0)
      | ~ v1_funct_1(k2_funct_1(sK0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(k2_funct_1(sK0))
      | v2_funct_1(k2_funct_1(sK0)) ) ),
    inference(superposition,[],[f30,f33])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:10:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (6414)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.49  % (6406)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.50  % (6416)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.50  % (6415)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.51  % (6402)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.51  % (6410)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.51  % (6399)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.52  % (6412)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.52  % (6403)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.52  % (6408)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.53  % (6410)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f55,f63,f67,f69,f75,f77,f80,f110,f116])).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    ~spl1_12),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f115])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    $false | ~spl1_12),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f112])).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    sK0 != sK0 | ~spl1_12),
% 0.21/0.53    inference(superposition,[],[f23,f109])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    sK0 = k2_funct_1(k2_funct_1(sK0)) | ~spl1_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f108])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    spl1_12 <=> sK0 = k2_funct_1(k2_funct_1(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    sK0 != k2_funct_1(k2_funct_1(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    ? [X0] : (k2_funct_1(k2_funct_1(X0)) != X0 & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f8])).
% 0.21/0.53  fof(f8,plain,(
% 0.21/0.53    ? [X0] : ((k2_funct_1(k2_funct_1(X0)) != X0 & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.21/0.53    inference(negated_conjecture,[],[f6])).
% 0.21/0.53  fof(f6,conjecture,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    ~spl1_5 | ~spl1_6 | spl1_12 | ~spl1_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f106,f73,f108,f61,f58])).
% 0.21/0.53  % (6405)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    spl1_5 <=> v1_relat_1(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    spl1_6 <=> v1_funct_1(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    spl1_7 <=> ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK0) | k2_funct_1(k2_funct_1(sK0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(k2_funct_1(sK0),X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    sK0 = k2_funct_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_7),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f105])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k2_relat_1(sK0)) | sK0 = k2_funct_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k1_relat_1(sK0) != k1_relat_1(sK0) | ~spl1_7),
% 0.21/0.53    inference(superposition,[],[f74,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))),
% 0.21/0.53    inference(global_subsumption,[],[f20,f21,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))),
% 0.21/0.53    inference(resolution,[],[f29,f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    v2_funct_1(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    v1_funct_1(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    v1_relat_1(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X0] : (k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(k2_funct_1(sK0),X0) | k2_funct_1(k2_funct_1(sK0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) != k1_relat_1(sK0)) ) | ~spl1_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f73])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ~spl1_5 | ~spl1_6 | ~spl1_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f79,f53,f61,f58])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    spl1_4 <=> ! [X0] : (k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(k2_funct_1(sK0),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_4),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f78])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k2_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_4),
% 0.21/0.53    inference(superposition,[],[f54,f39])).
% 0.21/0.53  % (6408)Refutation not found, incomplete strategy% (6408)------------------------------
% 0.21/0.53  % (6408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (6408)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0] : (k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(k2_funct_1(sK0),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl1_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f53])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ~spl1_5 | ~spl1_6 | spl1_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f76,f50,f61,f58])).
% 0.21/0.53  % (6408)Memory used [KB]: 10490
% 0.21/0.53  % (6408)Time elapsed: 0.054 s
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    spl1_3 <=> v1_funct_1(k2_funct_1(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.53  % (6408)------------------------------
% 0.21/0.53  % (6408)------------------------------
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_3),
% 0.21/0.53    inference(resolution,[],[f51,f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ~v1_funct_1(k2_funct_1(sK0)) | spl1_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f50])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ~spl1_2 | ~spl1_1 | ~spl1_3 | spl1_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f70,f73,f50,f44,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    spl1_2 <=> v1_relat_1(k2_funct_1(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    spl1_1 <=> v2_funct_1(k2_funct_1(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK0) | k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(k2_funct_1(sK0),X0) | ~v1_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(k2_funct_1(sK0)) | k2_funct_1(k2_funct_1(sK0)) = X0) )),
% 0.21/0.53    inference(forward_demodulation,[],[f65,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.21/0.53    inference(global_subsumption,[],[f20,f21,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.21/0.53    inference(resolution,[],[f27,f22])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X0] : (k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(k2_funct_1(sK0),X0) | ~v1_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(k2_funct_1(sK0)) | k1_relat_1(X0) != k2_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(k2_funct_1(sK0)) | k2_funct_1(k2_funct_1(sK0)) = X0) )),
% 0.21/0.53    inference(superposition,[],[f31,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.21/0.53    inference(global_subsumption,[],[f20,f21,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.21/0.53    inference(resolution,[],[f26,f22])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X0) | k2_funct_1(X0) = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    spl1_6),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    $false | spl1_6),
% 0.21/0.53    inference(resolution,[],[f62,f21])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ~v1_funct_1(sK0) | spl1_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f61])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    spl1_5),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    $false | spl1_5),
% 0.21/0.53    inference(resolution,[],[f59,f20])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ~v1_relat_1(sK0) | spl1_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f58])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ~spl1_5 | ~spl1_6 | spl1_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f56,f47,f61,f58])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_2),
% 0.21/0.53    inference(resolution,[],[f48,f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ~v1_relat_1(k2_funct_1(sK0)) | spl1_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f47])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    spl1_1 | ~spl1_2 | ~spl1_3 | spl1_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f41,f53,f50,f47,f44])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0] : (k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(k2_funct_1(sK0),X0) | ~v1_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(k2_funct_1(sK0)) | v2_funct_1(k2_funct_1(sK0))) )),
% 0.21/0.53    inference(superposition,[],[f30,f33])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : ((v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (6410)------------------------------
% 0.21/0.53  % (6410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (6410)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (6410)Memory used [KB]: 10618
% 0.21/0.53  % (6410)Time elapsed: 0.104 s
% 0.21/0.53  % (6410)------------------------------
% 0.21/0.53  % (6410)------------------------------
% 0.21/0.53  % (6405)Refutation not found, incomplete strategy% (6405)------------------------------
% 0.21/0.53  % (6405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (6405)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (6405)Memory used [KB]: 6012
% 0.21/0.53  % (6405)Time elapsed: 0.095 s
% 0.21/0.53  % (6405)------------------------------
% 0.21/0.53  % (6405)------------------------------
% 0.21/0.53  % (6400)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.53  % (6407)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.53  % (6420)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.53  % (6397)Success in time 0.165 s
%------------------------------------------------------------------------------
