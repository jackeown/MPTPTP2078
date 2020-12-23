%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 157 expanded)
%              Number of leaves         :   19 (  73 expanded)
%              Depth                    :    7
%              Number of atoms          :  244 ( 456 expanded)
%              Number of equality atoms :   31 (  45 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f180,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f58,f64,f76,f96,f118,f123,f128,f142,f169])).

fof(f169,plain,
    ( ~ spl1_18
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_8
    | ~ spl1_14
    | ~ spl1_15
    | spl1_16 ),
    inference(avatar_split_clause,[],[f168,f125,f120,f115,f73,f49,f44,f139])).

fof(f139,plain,
    ( spl1_18
  <=> k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).

fof(f44,plain,
    ( spl1_3
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f49,plain,
    ( spl1_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f73,plain,
    ( spl1_8
  <=> k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f115,plain,
    ( spl1_14
  <=> v1_funct_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f120,plain,
    ( spl1_15
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).

fof(f125,plain,
    ( spl1_16
  <=> v2_funct_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).

fof(f168,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(k4_relat_1(sK0),sK0)
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_8
    | ~ spl1_14
    | ~ spl1_15
    | spl1_16 ),
    inference(forward_demodulation,[],[f153,f75])).

fof(f75,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f73])).

fof(f153,plain,
    ( k5_relat_1(k4_relat_1(sK0),sK0) != k6_relat_1(k1_relat_1(k4_relat_1(sK0)))
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_14
    | ~ spl1_15
    | spl1_16 ),
    inference(unit_resulting_resolution,[],[f51,f46,f127,f117,f122,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).

fof(f122,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_15 ),
    inference(avatar_component_clause,[],[f120])).

fof(f117,plain,
    ( v1_funct_1(k4_relat_1(sK0))
    | ~ spl1_14 ),
    inference(avatar_component_clause,[],[f115])).

fof(f127,plain,
    ( ~ v2_funct_1(k4_relat_1(sK0))
    | spl1_16 ),
    inference(avatar_component_clause,[],[f125])).

fof(f46,plain,
    ( v1_funct_1(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f51,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f142,plain,
    ( spl1_18
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_11 ),
    inference(avatar_split_clause,[],[f137,f92,f49,f44,f39,f139])).

fof(f39,plain,
    ( spl1_2
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f92,plain,
    ( spl1_11
  <=> k2_funct_1(sK0) = k4_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f137,plain,
    ( k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),sK0)
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_11 ),
    inference(forward_demodulation,[],[f136,f94])).

fof(f94,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f92])).

fof(f136,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(unit_resulting_resolution,[],[f51,f46,f41,f26])).

fof(f26,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
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
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f41,plain,
    ( v2_funct_1(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f128,plain,
    ( ~ spl1_16
    | spl1_1
    | ~ spl1_11 ),
    inference(avatar_split_clause,[],[f109,f92,f34,f125])).

fof(f34,plain,
    ( spl1_1
  <=> v2_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f109,plain,
    ( ~ v2_funct_1(k4_relat_1(sK0))
    | spl1_1
    | ~ spl1_11 ),
    inference(backward_demodulation,[],[f36,f94])).

fof(f36,plain,
    ( ~ v2_funct_1(k2_funct_1(sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f123,plain,
    ( spl1_15
    | ~ spl1_5
    | ~ spl1_11 ),
    inference(avatar_split_clause,[],[f108,f92,f55,f120])).

fof(f55,plain,
    ( spl1_5
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f108,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_5
    | ~ spl1_11 ),
    inference(backward_demodulation,[],[f57,f94])).

fof(f57,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f118,plain,
    ( spl1_14
    | ~ spl1_6
    | ~ spl1_11 ),
    inference(avatar_split_clause,[],[f107,f92,f61,f115])).

fof(f61,plain,
    ( spl1_6
  <=> v1_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f107,plain,
    ( v1_funct_1(k4_relat_1(sK0))
    | ~ spl1_6
    | ~ spl1_11 ),
    inference(backward_demodulation,[],[f63,f94])).

fof(f63,plain,
    ( v1_funct_1(k2_funct_1(sK0))
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f96,plain,
    ( ~ spl1_4
    | ~ spl1_3
    | spl1_11
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f90,f39,f92,f44,f49])).

fof(f90,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_2 ),
    inference(resolution,[],[f27,f41])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f76,plain,
    ( spl1_8
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f65,f49,f73])).

fof(f65,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))
    | ~ spl1_4 ),
    inference(unit_resulting_resolution,[],[f51,f31])).

fof(f31,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f64,plain,
    ( spl1_6
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f59,f49,f44,f61])).

fof(f59,plain,
    ( v1_funct_1(k2_funct_1(sK0))
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(unit_resulting_resolution,[],[f51,f46,f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f58,plain,
    ( spl1_5
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f53,f49,f44,f55])).

fof(f53,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(unit_resulting_resolution,[],[f51,f46,f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f52,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f21,f49])).

fof(f21,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ v2_funct_1(k2_funct_1(sK0))
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ~ v2_funct_1(k2_funct_1(X0))
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v2_funct_1(k2_funct_1(sK0))
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

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

fof(f47,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f22,f44])).

fof(f22,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f42,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f23,f39])).

fof(f23,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f37,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f24,f34])).

fof(f24,plain,(
    ~ v2_funct_1(k2_funct_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:13:26 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.22/0.49  % (19056)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.49  % (19057)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.51  % (19052)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.51  % (19058)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.51  % (19053)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.51  % (19062)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.51  % (19063)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.52  % (19062)Refutation not found, incomplete strategy% (19062)------------------------------
% 0.22/0.52  % (19062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (19062)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (19062)Memory used [KB]: 10490
% 0.22/0.52  % (19062)Time elapsed: 0.101 s
% 0.22/0.52  % (19062)------------------------------
% 0.22/0.52  % (19062)------------------------------
% 0.22/0.52  % (19072)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.52  % (19058)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (19066)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f180,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f58,f64,f76,f96,f118,f123,f128,f142,f169])).
% 0.22/0.52  fof(f169,plain,(
% 0.22/0.52    ~spl1_18 | ~spl1_3 | ~spl1_4 | ~spl1_8 | ~spl1_14 | ~spl1_15 | spl1_16),
% 0.22/0.52    inference(avatar_split_clause,[],[f168,f125,f120,f115,f73,f49,f44,f139])).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    spl1_18 <=> k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    spl1_3 <=> v1_funct_1(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    spl1_4 <=> v1_relat_1(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    spl1_8 <=> k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.22/0.52  fof(f115,plain,(
% 0.22/0.52    spl1_14 <=> v1_funct_1(k4_relat_1(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.22/0.52  fof(f120,plain,(
% 0.22/0.52    spl1_15 <=> v1_relat_1(k4_relat_1(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).
% 0.22/0.52  fof(f125,plain,(
% 0.22/0.52    spl1_16 <=> v2_funct_1(k4_relat_1(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).
% 0.22/0.52  fof(f168,plain,(
% 0.22/0.52    k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(k4_relat_1(sK0),sK0) | (~spl1_3 | ~spl1_4 | ~spl1_8 | ~spl1_14 | ~spl1_15 | spl1_16)),
% 0.22/0.52    inference(forward_demodulation,[],[f153,f75])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) | ~spl1_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f73])).
% 0.22/0.52  fof(f153,plain,(
% 0.22/0.52    k5_relat_1(k4_relat_1(sK0),sK0) != k6_relat_1(k1_relat_1(k4_relat_1(sK0))) | (~spl1_3 | ~spl1_4 | ~spl1_14 | ~spl1_15 | spl1_16)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f51,f46,f127,f117,f122,f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v2_funct_1(X0) | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0] : (v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0] : ((v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).
% 0.22/0.52  fof(f122,plain,(
% 0.22/0.52    v1_relat_1(k4_relat_1(sK0)) | ~spl1_15),
% 0.22/0.52    inference(avatar_component_clause,[],[f120])).
% 0.22/0.52  fof(f117,plain,(
% 0.22/0.52    v1_funct_1(k4_relat_1(sK0)) | ~spl1_14),
% 0.22/0.52    inference(avatar_component_clause,[],[f115])).
% 0.22/0.52  fof(f127,plain,(
% 0.22/0.52    ~v2_funct_1(k4_relat_1(sK0)) | spl1_16),
% 0.22/0.52    inference(avatar_component_clause,[],[f125])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    v1_funct_1(sK0) | ~spl1_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f44])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    v1_relat_1(sK0) | ~spl1_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f49])).
% 0.22/0.52  fof(f142,plain,(
% 0.22/0.52    spl1_18 | ~spl1_2 | ~spl1_3 | ~spl1_4 | ~spl1_11),
% 0.22/0.52    inference(avatar_split_clause,[],[f137,f92,f49,f44,f39,f139])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    spl1_2 <=> v2_funct_1(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    spl1_11 <=> k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.22/0.52  fof(f137,plain,(
% 0.22/0.52    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),sK0) | (~spl1_2 | ~spl1_3 | ~spl1_4 | ~spl1_11)),
% 0.22/0.52    inference(forward_demodulation,[],[f136,f94])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    k2_funct_1(sK0) = k4_relat_1(sK0) | ~spl1_11),
% 0.22/0.52    inference(avatar_component_clause,[],[f92])).
% 0.22/0.52  fof(f136,plain,(
% 0.22/0.52    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) | (~spl1_2 | ~spl1_3 | ~spl1_4)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f51,f46,f41,f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    v2_funct_1(sK0) | ~spl1_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f39])).
% 0.22/0.52  fof(f128,plain,(
% 0.22/0.52    ~spl1_16 | spl1_1 | ~spl1_11),
% 0.22/0.52    inference(avatar_split_clause,[],[f109,f92,f34,f125])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    spl1_1 <=> v2_funct_1(k2_funct_1(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    ~v2_funct_1(k4_relat_1(sK0)) | (spl1_1 | ~spl1_11)),
% 0.22/0.52    inference(backward_demodulation,[],[f36,f94])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ~v2_funct_1(k2_funct_1(sK0)) | spl1_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f34])).
% 0.22/0.52  fof(f123,plain,(
% 0.22/0.52    spl1_15 | ~spl1_5 | ~spl1_11),
% 0.22/0.52    inference(avatar_split_clause,[],[f108,f92,f55,f120])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    spl1_5 <=> v1_relat_1(k2_funct_1(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    v1_relat_1(k4_relat_1(sK0)) | (~spl1_5 | ~spl1_11)),
% 0.22/0.52    inference(backward_demodulation,[],[f57,f94])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    v1_relat_1(k2_funct_1(sK0)) | ~spl1_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f55])).
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    spl1_14 | ~spl1_6 | ~spl1_11),
% 0.22/0.52    inference(avatar_split_clause,[],[f107,f92,f61,f115])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    spl1_6 <=> v1_funct_1(k2_funct_1(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.52  fof(f107,plain,(
% 0.22/0.52    v1_funct_1(k4_relat_1(sK0)) | (~spl1_6 | ~spl1_11)),
% 0.22/0.52    inference(backward_demodulation,[],[f63,f94])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    v1_funct_1(k2_funct_1(sK0)) | ~spl1_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f61])).
% 0.22/0.52  fof(f96,plain,(
% 0.22/0.52    ~spl1_4 | ~spl1_3 | spl1_11 | ~spl1_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f90,f39,f92,f44,f49])).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    k2_funct_1(sK0) = k4_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_2),
% 0.22/0.52    inference(resolution,[],[f27,f41])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    spl1_8 | ~spl1_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f65,f49,f73])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) | ~spl1_4),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f51,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    spl1_6 | ~spl1_3 | ~spl1_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f59,f49,f44,f61])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    v1_funct_1(k2_funct_1(sK0)) | (~spl1_3 | ~spl1_4)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f51,f46,f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    spl1_5 | ~spl1_3 | ~spl1_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f53,f49,f44,f55])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    v1_relat_1(k2_funct_1(sK0)) | (~spl1_3 | ~spl1_4)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f51,f46,f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    spl1_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f21,f49])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    v1_relat_1(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ~v2_funct_1(k2_funct_1(sK0)) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ? [X0] : (~v2_funct_1(k2_funct_1(X0)) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (~v2_funct_1(k2_funct_1(sK0)) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ? [X0] : (~v2_funct_1(k2_funct_1(X0)) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f8])).
% 0.22/0.52  fof(f8,plain,(
% 0.22/0.52    ? [X0] : ((~v2_funct_1(k2_funct_1(X0)) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 0.22/0.52    inference(negated_conjecture,[],[f6])).
% 0.22/0.52  fof(f6,conjecture,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    spl1_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f22,f44])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    v1_funct_1(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    spl1_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f23,f39])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    v2_funct_1(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ~spl1_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f24,f34])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ~v2_funct_1(k2_funct_1(sK0))),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (19058)------------------------------
% 0.22/0.52  % (19058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (19058)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (19058)Memory used [KB]: 10618
% 0.22/0.52  % (19058)Time elapsed: 0.101 s
% 0.22/0.52  % (19058)------------------------------
% 0.22/0.52  % (19058)------------------------------
% 0.22/0.52  % (19059)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (19059)Refutation not found, incomplete strategy% (19059)------------------------------
% 0.22/0.52  % (19059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (19059)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (19059)Memory used [KB]: 6012
% 0.22/0.52  % (19059)Time elapsed: 0.069 s
% 0.22/0.52  % (19059)------------------------------
% 0.22/0.52  % (19059)------------------------------
% 0.22/0.52  % (19051)Success in time 0.161 s
%------------------------------------------------------------------------------
