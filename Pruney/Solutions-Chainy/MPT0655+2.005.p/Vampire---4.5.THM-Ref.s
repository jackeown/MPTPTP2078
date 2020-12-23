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
% DateTime   : Thu Dec  3 12:53:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 166 expanded)
%              Number of leaves         :   21 (  77 expanded)
%              Depth                    :    7
%              Number of atoms          :  266 ( 482 expanded)
%              Number of equality atoms :   30 (  45 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f212,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f51,f56,f62,f68,f75,f91,f100,f105,f110,f117,f170,f211])).

fof(f211,plain,(
    spl1_19 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | spl1_19 ),
    inference(unit_resulting_resolution,[],[f34,f169])).

fof(f169,plain,
    ( ~ v2_funct_1(k6_relat_1(k1_relat_1(sK0)))
    | spl1_19 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl1_19
  <=> v2_funct_1(k6_relat_1(k1_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).

fof(f34,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f170,plain,
    ( ~ spl1_19
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_7
    | ~ spl1_10
    | ~ spl1_11
    | spl1_12
    | ~ spl1_13 ),
    inference(avatar_split_clause,[],[f165,f114,f107,f102,f97,f72,f53,f48,f167])).

fof(f48,plain,
    ( spl1_3
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f53,plain,
    ( spl1_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f72,plain,
    ( spl1_7
  <=> k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f97,plain,
    ( spl1_10
  <=> v1_funct_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f102,plain,
    ( spl1_11
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f107,plain,
    ( spl1_12
  <=> v2_funct_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f114,plain,
    ( spl1_13
  <=> k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f165,plain,
    ( ~ v2_funct_1(k6_relat_1(k1_relat_1(sK0)))
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_7
    | ~ spl1_10
    | ~ spl1_11
    | spl1_12
    | ~ spl1_13 ),
    inference(forward_demodulation,[],[f164,f116])).

fof(f116,plain,
    ( k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k4_relat_1(sK0))
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f114])).

fof(f164,plain,
    ( ~ v2_funct_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_7
    | ~ spl1_10
    | ~ spl1_11
    | spl1_12 ),
    inference(unit_resulting_resolution,[],[f55,f50,f104,f99,f109,f74,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(k5_relat_1(X1,X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
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
         => ( ( k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

fof(f74,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f72])).

fof(f109,plain,
    ( ~ v2_funct_1(k4_relat_1(sK0))
    | spl1_12 ),
    inference(avatar_component_clause,[],[f107])).

fof(f99,plain,
    ( v1_funct_1(k4_relat_1(sK0))
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f97])).

fof(f104,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f102])).

fof(f50,plain,
    ( v1_funct_1(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f55,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f117,plain,
    ( spl1_13
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f112,f87,f53,f48,f43,f114])).

fof(f43,plain,
    ( spl1_2
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f87,plain,
    ( spl1_9
  <=> k2_funct_1(sK0) = k4_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f112,plain,
    ( k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k4_relat_1(sK0))
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_9 ),
    inference(forward_demodulation,[],[f111,f89])).

fof(f89,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f87])).

fof(f111,plain,
    ( k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0))
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(unit_resulting_resolution,[],[f55,f50,f45,f26])).

fof(f26,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f45,plain,
    ( v2_funct_1(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f110,plain,
    ( ~ spl1_12
    | spl1_1
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f95,f87,f38,f107])).

fof(f38,plain,
    ( spl1_1
  <=> v2_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f95,plain,
    ( ~ v2_funct_1(k4_relat_1(sK0))
    | spl1_1
    | ~ spl1_9 ),
    inference(backward_demodulation,[],[f40,f89])).

fof(f40,plain,
    ( ~ v2_funct_1(k2_funct_1(sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f105,plain,
    ( spl1_11
    | ~ spl1_5
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f94,f87,f59,f102])).

fof(f59,plain,
    ( spl1_5
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f94,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_5
    | ~ spl1_9 ),
    inference(backward_demodulation,[],[f61,f89])).

fof(f61,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f100,plain,
    ( spl1_10
    | ~ spl1_6
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f93,f87,f65,f97])).

fof(f65,plain,
    ( spl1_6
  <=> v1_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f93,plain,
    ( v1_funct_1(k4_relat_1(sK0))
    | ~ spl1_6
    | ~ spl1_9 ),
    inference(backward_demodulation,[],[f67,f89])).

fof(f67,plain,
    ( v1_funct_1(k2_funct_1(sK0))
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f91,plain,
    ( ~ spl1_4
    | ~ spl1_3
    | spl1_9
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f84,f43,f87,f48,f53])).

fof(f84,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_2 ),
    inference(resolution,[],[f28,f45])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
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

fof(f75,plain,
    ( spl1_7
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f69,f53,f72])).

fof(f69,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))
    | ~ spl1_4 ),
    inference(unit_resulting_resolution,[],[f55,f35])).

fof(f35,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f68,plain,
    ( spl1_6
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f63,f53,f48,f65])).

fof(f63,plain,
    ( v1_funct_1(k2_funct_1(sK0))
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(unit_resulting_resolution,[],[f55,f50,f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f62,plain,
    ( spl1_5
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f57,f53,f48,f59])).

fof(f57,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(unit_resulting_resolution,[],[f55,f50,f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f56,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f22,f53])).

fof(f22,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ v2_funct_1(k2_funct_1(sK0))
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f20])).

fof(f20,plain,
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

fof(f10,plain,(
    ? [X0] :
      ( ~ v2_funct_1(k2_funct_1(X0))
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ~ v2_funct_1(k2_funct_1(X0))
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => v2_funct_1(k2_funct_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).

fof(f51,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f23,f48])).

fof(f23,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f24,f43])).

fof(f24,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f41,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f25,f38])).

fof(f25,plain,(
    ~ v2_funct_1(k2_funct_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n004.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:53:53 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.22/0.50  % (26723)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.50  % (26724)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.50  % (26720)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.50  % (26722)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (26724)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (26719)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.51  % (26718)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.51  % (26736)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.51  % (26740)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.51  % (26721)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.51  % (26721)Refutation not found, incomplete strategy% (26721)------------------------------
% 0.22/0.51  % (26721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (26721)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (26721)Memory used [KB]: 10490
% 0.22/0.51  % (26721)Time elapsed: 0.093 s
% 0.22/0.51  % (26721)------------------------------
% 0.22/0.51  % (26721)------------------------------
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f212,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f41,f46,f51,f56,f62,f68,f75,f91,f100,f105,f110,f117,f170,f211])).
% 0.22/0.51  fof(f211,plain,(
% 0.22/0.51    spl1_19),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f208])).
% 0.22/0.51  fof(f208,plain,(
% 0.22/0.51    $false | spl1_19),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f34,f169])).
% 0.22/0.51  fof(f169,plain,(
% 0.22/0.51    ~v2_funct_1(k6_relat_1(k1_relat_1(sK0))) | spl1_19),
% 0.22/0.51    inference(avatar_component_clause,[],[f167])).
% 0.22/0.51  fof(f167,plain,(
% 0.22/0.51    spl1_19 <=> v2_funct_1(k6_relat_1(k1_relat_1(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.22/0.51  fof(f170,plain,(
% 0.22/0.51    ~spl1_19 | ~spl1_3 | ~spl1_4 | ~spl1_7 | ~spl1_10 | ~spl1_11 | spl1_12 | ~spl1_13),
% 0.22/0.51    inference(avatar_split_clause,[],[f165,f114,f107,f102,f97,f72,f53,f48,f167])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    spl1_3 <=> v1_funct_1(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    spl1_4 <=> v1_relat_1(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    spl1_7 <=> k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    spl1_10 <=> v1_funct_1(k4_relat_1(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    spl1_11 <=> v1_relat_1(k4_relat_1(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    spl1_12 <=> v2_funct_1(k4_relat_1(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    spl1_13 <=> k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k4_relat_1(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.22/0.51  fof(f165,plain,(
% 0.22/0.51    ~v2_funct_1(k6_relat_1(k1_relat_1(sK0))) | (~spl1_3 | ~spl1_4 | ~spl1_7 | ~spl1_10 | ~spl1_11 | spl1_12 | ~spl1_13)),
% 0.22/0.51    inference(forward_demodulation,[],[f164,f116])).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k4_relat_1(sK0)) | ~spl1_13),
% 0.22/0.51    inference(avatar_component_clause,[],[f114])).
% 0.22/0.51  fof(f164,plain,(
% 0.22/0.51    ~v2_funct_1(k5_relat_1(sK0,k4_relat_1(sK0))) | (~spl1_3 | ~spl1_4 | ~spl1_7 | ~spl1_10 | ~spl1_11 | spl1_12)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f55,f50,f104,f99,f109,f74,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v2_funct_1(k5_relat_1(X1,X0)) | k1_relat_1(X0) != k2_relat_1(X1) | v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) | ~spl1_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f72])).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    ~v2_funct_1(k4_relat_1(sK0)) | spl1_12),
% 0.22/0.51    inference(avatar_component_clause,[],[f107])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    v1_funct_1(k4_relat_1(sK0)) | ~spl1_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f97])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    v1_relat_1(k4_relat_1(sK0)) | ~spl1_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f102])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    v1_funct_1(sK0) | ~spl1_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f48])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    v1_relat_1(sK0) | ~spl1_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f53])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    spl1_13 | ~spl1_2 | ~spl1_3 | ~spl1_4 | ~spl1_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f112,f87,f53,f48,f43,f114])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    spl1_2 <=> v2_funct_1(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    spl1_9 <=> k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.22/0.51  fof(f112,plain,(
% 0.22/0.51    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k4_relat_1(sK0)) | (~spl1_2 | ~spl1_3 | ~spl1_4 | ~spl1_9)),
% 0.22/0.51    inference(forward_demodulation,[],[f111,f89])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    k2_funct_1(sK0) = k4_relat_1(sK0) | ~spl1_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f87])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) | (~spl1_2 | ~spl1_3 | ~spl1_4)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f55,f50,f45,f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    v2_funct_1(sK0) | ~spl1_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f43])).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    ~spl1_12 | spl1_1 | ~spl1_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f95,f87,f38,f107])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    spl1_1 <=> v2_funct_1(k2_funct_1(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    ~v2_funct_1(k4_relat_1(sK0)) | (spl1_1 | ~spl1_9)),
% 0.22/0.51    inference(backward_demodulation,[],[f40,f89])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ~v2_funct_1(k2_funct_1(sK0)) | spl1_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f38])).
% 0.22/0.51  fof(f105,plain,(
% 0.22/0.51    spl1_11 | ~spl1_5 | ~spl1_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f94,f87,f59,f102])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    spl1_5 <=> v1_relat_1(k2_funct_1(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    v1_relat_1(k4_relat_1(sK0)) | (~spl1_5 | ~spl1_9)),
% 0.22/0.51    inference(backward_demodulation,[],[f61,f89])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    v1_relat_1(k2_funct_1(sK0)) | ~spl1_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f59])).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    spl1_10 | ~spl1_6 | ~spl1_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f93,f87,f65,f97])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    spl1_6 <=> v1_funct_1(k2_funct_1(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    v1_funct_1(k4_relat_1(sK0)) | (~spl1_6 | ~spl1_9)),
% 0.22/0.51    inference(backward_demodulation,[],[f67,f89])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    v1_funct_1(k2_funct_1(sK0)) | ~spl1_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f65])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    ~spl1_4 | ~spl1_3 | spl1_9 | ~spl1_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f84,f43,f87,f48,f53])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    k2_funct_1(sK0) = k4_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_2),
% 0.22/0.51    inference(resolution,[],[f28,f45])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    spl1_7 | ~spl1_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f69,f53,f72])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) | ~spl1_4),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f55,f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    spl1_6 | ~spl1_3 | ~spl1_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f63,f53,f48,f65])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    v1_funct_1(k2_funct_1(sK0)) | (~spl1_3 | ~spl1_4)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f55,f50,f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    spl1_5 | ~spl1_3 | ~spl1_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f57,f53,f48,f59])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    v1_relat_1(k2_funct_1(sK0)) | (~spl1_3 | ~spl1_4)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f55,f50,f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    spl1_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f22,f53])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    v1_relat_1(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ~v2_funct_1(k2_funct_1(sK0)) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ? [X0] : (~v2_funct_1(k2_funct_1(X0)) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (~v2_funct_1(k2_funct_1(sK0)) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ? [X0] : (~v2_funct_1(k2_funct_1(X0)) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ? [X0] : ((~v2_funct_1(k2_funct_1(X0)) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 0.22/0.51    inference(negated_conjecture,[],[f7])).
% 0.22/0.51  fof(f7,conjecture,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    spl1_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f23,f48])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    v1_funct_1(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    spl1_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f24,f43])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    v2_funct_1(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ~spl1_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f25,f38])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ~v2_funct_1(k2_funct_1(sK0))),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (26724)------------------------------
% 0.22/0.51  % (26724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (26724)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (26724)Memory used [KB]: 10746
% 0.22/0.51  % (26724)Time elapsed: 0.089 s
% 0.22/0.51  % (26724)------------------------------
% 0.22/0.51  % (26724)------------------------------
% 0.22/0.51  % (26739)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.52  % (26717)Success in time 0.154 s
%------------------------------------------------------------------------------
