%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 160 expanded)
%              Number of leaves         :   12 (  46 expanded)
%              Depth                    :   13
%              Number of atoms          :  181 ( 663 expanded)
%              Number of equality atoms :   37 ( 199 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f90,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f57,f59,f72,f74,f89])).

fof(f89,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(resolution,[],[f87,f81])).

fof(f81,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f76,f33])).

fof(f33,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl3_1
  <=> o_0_0_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f76,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK1)))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f20,f38])).

fof(f38,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_2
  <=> o_0_0_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ v1_partfun1(k3_partfun1(sK2,sK0,sK1),sK0)
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ~ v1_partfun1(k3_partfun1(X2,X0,X1),X0)
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ~ v1_partfun1(k3_partfun1(sK2,sK0,sK1),sK0)
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ v1_partfun1(k3_partfun1(X2,X0,X1),X0)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ v1_partfun1(k3_partfun1(X2,X0,X1),X0)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => v1_partfun1(k3_partfun1(X2,X0,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => v1_partfun1(k3_partfun1(X2,X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_funct_2)).

fof(f87,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X0)))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(resolution,[],[f83,f78])).

fof(f78,plain,
    ( ~ v1_partfun1(sK2,o_0_0_xboole_0)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f43,f38])).

fof(f43,plain,(
    ~ v1_partfun1(sK2,sK0) ),
    inference(backward_demodulation,[],[f22,f42])).

fof(f42,plain,(
    sK2 = k3_partfun1(sK2,sK0,sK1) ),
    inference(resolution,[],[f40,f20])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK2 = k3_partfun1(sK2,X0,X1) ) ),
    inference(resolution,[],[f28,f18])).

fof(f18,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_partfun1(X2,X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k3_partfun1(X2,X0,X1) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_partfun1)).

fof(f22,plain,(
    ~ v1_partfun1(k3_partfun1(sK2,sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( v1_partfun1(X0,o_0_0_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1))) )
    | ~ spl3_3 ),
    inference(resolution,[],[f65,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f65,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f48,f61])).

fof(f61,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl3_3 ),
    inference(resolution,[],[f48,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f23,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f48,plain,
    ( v1_xboole_0(sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl3_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f74,plain,(
    ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f73])).

fof(f73,plain,
    ( $false
    | ~ spl3_5 ),
    inference(resolution,[],[f56,f43])).

fof(f56,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_5
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f72,plain,
    ( spl3_1
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | spl3_1
    | ~ spl3_3 ),
    inference(trivial_inequality_removal,[],[f70])).

fof(f70,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0
    | spl3_1
    | ~ spl3_3 ),
    inference(superposition,[],[f34,f61])).

fof(f34,plain,
    ( o_0_0_xboole_0 != sK1
    | spl3_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f59,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f58])).

fof(f58,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f52,f19])).

fof(f19,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f52,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_4
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f57,plain,
    ( spl3_3
    | ~ spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f44,f54,f50,f46])).

fof(f44,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f41,f20])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(sK2,X0)
      | ~ v1_funct_2(sK2,X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f26,f18])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f39,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f29,f36,f32])).

fof(f29,plain,
    ( o_0_0_xboole_0 = sK0
    | o_0_0_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f21,f23,f23])).

fof(f21,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:42:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (26819)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (26836)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.51  % (26811)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (26820)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (26827)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (26819)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f39,f57,f59,f72,f74,f89])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f88])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    $false | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 0.21/0.51    inference(resolution,[],[f87,f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) | (~spl3_1 | ~spl3_2)),
% 0.21/0.51    inference(backward_demodulation,[],[f76,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    o_0_0_xboole_0 = sK1 | ~spl3_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    spl3_1 <=> o_0_0_xboole_0 = sK1),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK1))) | ~spl3_2),
% 0.21/0.51    inference(backward_demodulation,[],[f20,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    o_0_0_xboole_0 = sK0 | ~spl3_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    spl3_2 <=> o_0_0_xboole_0 = sK0),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ~v1_partfun1(k3_partfun1(sK2,sK0,sK1),sK0) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (~v1_partfun1(k3_partfun1(X2,X0,X1),X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (~v1_partfun1(k3_partfun1(sK2,sK0,sK1),sK0) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (~v1_partfun1(k3_partfun1(X2,X0,X1),X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ? [X0,X1,X2] : ((~v1_partfun1(k3_partfun1(X2,X0,X1),X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => v1_partfun1(k3_partfun1(X2,X0,X1),X0)))),
% 0.21/0.51    inference(negated_conjecture,[],[f6])).
% 0.21/0.51  fof(f6,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => v1_partfun1(k3_partfun1(X2,X0,X1),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_funct_2)).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X0)))) ) | (~spl3_2 | ~spl3_3)),
% 0.21/0.51    inference(resolution,[],[f83,f78])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ~v1_partfun1(sK2,o_0_0_xboole_0) | ~spl3_2),
% 0.21/0.51    inference(backward_demodulation,[],[f43,f38])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ~v1_partfun1(sK2,sK0)),
% 0.21/0.51    inference(backward_demodulation,[],[f22,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    sK2 = k3_partfun1(sK2,sK0,sK1)),
% 0.21/0.51    inference(resolution,[],[f40,f20])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK2 = k3_partfun1(sK2,X0,X1)) )),
% 0.21/0.51    inference(resolution,[],[f28,f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    v1_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k3_partfun1(X2,X0,X1) = X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k3_partfun1(X2,X0,X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k3_partfun1(X2,X0,X1) = X2 | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k3_partfun1(X2,X0,X1) = X2)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_partfun1)).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ~v1_partfun1(k3_partfun1(sK2,sK0,sK1),sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_partfun1(X0,o_0_0_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1)))) ) | ~spl3_3),
% 0.21/0.51    inference(resolution,[],[f65,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(X2,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    v1_xboole_0(o_0_0_xboole_0) | ~spl3_3),
% 0.21/0.51    inference(backward_demodulation,[],[f48,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    o_0_0_xboole_0 = sK1 | ~spl3_3),
% 0.21/0.51    inference(resolution,[],[f48,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_xboole_0(X0) | o_0_0_xboole_0 = X0) )),
% 0.21/0.51    inference(definition_unfolding,[],[f24,f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    k1_xboole_0 = o_0_0_xboole_0),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    k1_xboole_0 = o_0_0_xboole_0),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    v1_xboole_0(sK1) | ~spl3_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    spl3_3 <=> v1_xboole_0(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ~spl3_5),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    $false | ~spl3_5),
% 0.21/0.51    inference(resolution,[],[f56,f43])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    v1_partfun1(sK2,sK0) | ~spl3_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    spl3_5 <=> v1_partfun1(sK2,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    spl3_1 | ~spl3_3),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    $false | (spl3_1 | ~spl3_3)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    o_0_0_xboole_0 != o_0_0_xboole_0 | (spl3_1 | ~spl3_3)),
% 0.21/0.51    inference(superposition,[],[f34,f61])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    o_0_0_xboole_0 != sK1 | spl3_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f32])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    spl3_4),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    $false | spl3_4),
% 0.21/0.51    inference(resolution,[],[f52,f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ~v1_funct_2(sK2,sK0,sK1) | spl3_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    spl3_4 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    spl3_3 | ~spl3_4 | spl3_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f44,f54,f50,f46])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    v1_partfun1(sK2,sK0) | ~v1_funct_2(sK2,sK0,sK1) | v1_xboole_0(sK1)),
% 0.21/0.51    inference(resolution,[],[f41,f20])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(sK2,X0) | ~v1_funct_2(sK2,X0,X1) | v1_xboole_0(X1)) )),
% 0.21/0.51    inference(resolution,[],[f26,f18])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ~spl3_1 | spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f29,f36,f32])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    o_0_0_xboole_0 = sK0 | o_0_0_xboole_0 != sK1),
% 0.21/0.51    inference(definition_unfolding,[],[f21,f23,f23])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (26819)------------------------------
% 0.21/0.51  % (26819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (26819)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (26819)Memory used [KB]: 6268
% 0.21/0.51  % (26819)Time elapsed: 0.103 s
% 0.21/0.51  % (26819)------------------------------
% 0.21/0.51  % (26819)------------------------------
% 0.21/0.51  % (26797)Success in time 0.16 s
%------------------------------------------------------------------------------
