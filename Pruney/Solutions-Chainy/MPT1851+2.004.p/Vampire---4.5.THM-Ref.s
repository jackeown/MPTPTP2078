%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 226 expanded)
%              Number of leaves         :   16 (  74 expanded)
%              Depth                    :   17
%              Number of atoms          :  182 ( 599 expanded)
%              Number of equality atoms :   66 ( 223 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f123,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f66,f78,f81,f122])).

fof(f122,plain,
    ( spl2_2
    | ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | spl2_2
    | ~ spl2_4 ),
    inference(trivial_inequality_removal,[],[f120])).

fof(f120,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(sK0)
    | spl2_2
    | ~ spl2_4 ),
    inference(superposition,[],[f94,f115])).

fof(f115,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(sK1)
    | ~ spl2_4 ),
    inference(trivial_inequality_removal,[],[f113])).

fof(f113,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = u1_pre_topc(sK1)
    | ~ spl2_4 ),
    inference(superposition,[],[f112,f93])).

fof(f93,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ spl2_4 ),
    inference(backward_demodulation,[],[f23,f91])).

fof(f91,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl2_4 ),
    inference(trivial_inequality_removal,[],[f89])).

fof(f89,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl2_4 ),
    inference(superposition,[],[f88,f23])).

fof(f88,plain,
    ( ! [X10,X9] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X9,X10)
        | u1_struct_0(sK0) = X9 )
    | ~ spl2_4 ),
    inference(resolution,[],[f79,f82])).

fof(f82,plain,
    ( r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_4 ),
    inference(superposition,[],[f48,f77])).

fof(f77,plain,
    ( u1_pre_topc(sK0) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,u1_struct_0(sK0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl2_4
  <=> u1_pre_topc(sK0) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f48,plain,(
    ! [X0] : r1_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0),k1_zfmisc_1(X0)) ),
    inference(superposition,[],[f45,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f30,f38,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f45,plain,(
    ! [X0] : r1_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(superposition,[],[f27,f40])).

fof(f40,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f26,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f32,f38])).

fof(f32,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f27,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f6])).

% (15718)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f6,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X1,k1_zfmisc_1(X0))
      | X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) ) ),
    inference(resolution,[],[f33,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f23,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ v2_tdlat_3(sK1)
    & v2_tdlat_3(sK0)
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tdlat_3(X1)
            & v2_tdlat_3(X0)
            & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(sK0)
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ~ v2_tdlat_3(X1)
        & v2_tdlat_3(sK0)
        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        & l1_pre_topc(X1) )
   => ( ~ v2_tdlat_3(sK1)
      & v2_tdlat_3(sK0)
      & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v2_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v2_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v2_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v2_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tex_2)).

fof(f112,plain,
    ( ! [X10,X9] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X10,X9)
        | u1_pre_topc(sK0) = X9 )
    | ~ spl2_4 ),
    inference(resolution,[],[f108,f82])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X1,k1_zfmisc_1(X0))
      | X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) ) ),
    inference(resolution,[],[f34,f36])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f94,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(sK1)
    | spl2_2
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f92,f77])).

fof(f92,plain,
    ( u1_pre_topc(sK1) != k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,u1_struct_0(sK0))
    | spl2_2
    | ~ spl2_4 ),
    inference(backward_demodulation,[],[f63,f91])).

fof(f63,plain,
    ( u1_pre_topc(sK1) != k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,u1_struct_0(sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl2_2
  <=> u1_pre_topc(sK1) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f81,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f80])).

fof(f80,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f73,f21])).

fof(f21,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f73,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl2_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f78,plain,
    ( ~ spl2_3
    | spl2_4 ),
    inference(avatar_split_clause,[],[f67,f75,f71])).

fof(f67,plain,
    ( u1_pre_topc(sK0) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f42,f24])).

fof(f24,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v2_tdlat_3(X0)
      | u1_pre_topc(X0) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f28,f38])).

fof(f28,plain,(
    ! [X0] :
      ( u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0))
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( ( v2_tdlat_3(X0)
          | u1_pre_topc(X0) != k2_tarski(k1_xboole_0,u1_struct_0(X0)) )
        & ( u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0))
          | ~ v2_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tdlat_3)).

fof(f66,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | spl2_1 ),
    inference(resolution,[],[f59,f22])).

fof(f22,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f59,plain,
    ( ~ l1_pre_topc(sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl2_1
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f64,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f55,f61,f57])).

fof(f55,plain,
    ( u1_pre_topc(sK1) != k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f41,f25])).

fof(f25,plain,(
    ~ v2_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0] :
      ( v2_tdlat_3(X0)
      | u1_pre_topc(X0) != k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f29,f38])).

fof(f29,plain,(
    ! [X0] :
      ( v2_tdlat_3(X0)
      | u1_pre_topc(X0) != k2_tarski(k1_xboole_0,u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:35:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (15723)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (15715)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (15731)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (15723)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (15739)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f64,f66,f78,f81,f122])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    spl2_2 | ~spl2_4),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f121])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    $false | (spl2_2 | ~spl2_4)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f120])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    u1_pre_topc(sK0) != u1_pre_topc(sK0) | (spl2_2 | ~spl2_4)),
% 0.21/0.52    inference(superposition,[],[f94,f115])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    u1_pre_topc(sK0) = u1_pre_topc(sK1) | ~spl2_4),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f113])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_pre_topc(sK0) = u1_pre_topc(sK1) | ~spl2_4),
% 0.21/0.52    inference(superposition,[],[f112,f93])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) | ~spl2_4),
% 0.21/0.52    inference(backward_demodulation,[],[f23,f91])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    u1_struct_0(sK0) = u1_struct_0(sK1) | ~spl2_4),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f89])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_struct_0(sK0) = u1_struct_0(sK1) | ~spl2_4),
% 0.21/0.52    inference(superposition,[],[f88,f23])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    ( ! [X10,X9] : (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X9,X10) | u1_struct_0(sK0) = X9) ) | ~spl2_4),
% 0.21/0.52    inference(resolution,[],[f79,f82])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_4),
% 0.21/0.52    inference(superposition,[],[f48,f77])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    u1_pre_topc(sK0) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,u1_struct_0(sK0)) | ~spl2_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    spl2_4 <=> u1_pre_topc(sK0) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,u1_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0),k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(superposition,[],[f45,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f30,f38,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f31,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(superposition,[],[f27,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f26,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f32,f38])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  % (15718)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r1_tarski(X1,k1_zfmisc_1(X0)) | X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) )),
% 0.21/0.52    inference(resolution,[],[f33,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    (~v2_tdlat_3(sK1) & v2_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & l1_pre_topc(sK1)) & l1_pre_topc(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f17,f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (~v2_tdlat_3(X1) & v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (~v2_tdlat_3(X1) & v2_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & l1_pre_topc(X1)) & l1_pre_topc(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X1] : (~v2_tdlat_3(X1) & v2_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & l1_pre_topc(X1)) => (~v2_tdlat_3(sK1) & v2_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & l1_pre_topc(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (~v2_tdlat_3(X1) & v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((~v2_tdlat_3(X1) & (v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tdlat_3(X1))))),
% 0.21/0.52    inference(negated_conjecture,[],[f10])).
% 0.21/0.52  fof(f10,conjecture,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tdlat_3(X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tex_2)).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    ( ! [X10,X9] : (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X10,X9) | u1_pre_topc(sK0) = X9) ) | ~spl2_4),
% 0.21/0.52    inference(resolution,[],[f108,f82])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r1_tarski(X1,k1_zfmisc_1(X0)) | X1 = X3 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) )),
% 0.21/0.52    inference(resolution,[],[f34,f36])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X1 = X3) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    u1_pre_topc(sK0) != u1_pre_topc(sK1) | (spl2_2 | ~spl2_4)),
% 0.21/0.52    inference(forward_demodulation,[],[f92,f77])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    u1_pre_topc(sK1) != k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,u1_struct_0(sK0)) | (spl2_2 | ~spl2_4)),
% 0.21/0.52    inference(backward_demodulation,[],[f63,f91])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    u1_pre_topc(sK1) != k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) | spl2_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    spl2_2 <=> u1_pre_topc(sK1) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,u1_struct_0(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    spl2_3),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f80])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    $false | spl2_3),
% 0.21/0.52    inference(resolution,[],[f73,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    l1_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | spl2_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    spl2_3 <=> l1_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ~spl2_3 | spl2_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f67,f75,f71])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    u1_pre_topc(sK0) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(resolution,[],[f42,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    v2_tdlat_3(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0] : (~v2_tdlat_3(X0) | u1_pre_topc(X0) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f28,f38])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0] : (u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0)) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (((v2_tdlat_3(X0) | u1_pre_topc(X0) != k2_tarski(k1_xboole_0,u1_struct_0(X0))) & (u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0)) | ~v2_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0] : ((v2_tdlat_3(X0) <=> u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) <=> u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tdlat_3)).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    spl2_1),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    $false | spl2_1),
% 0.21/0.52    inference(resolution,[],[f59,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    l1_pre_topc(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ~l1_pre_topc(sK1) | spl2_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    spl2_1 <=> l1_pre_topc(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ~spl2_1 | ~spl2_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f55,f61,f57])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    u1_pre_topc(sK1) != k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) | ~l1_pre_topc(sK1)),
% 0.21/0.52    inference(resolution,[],[f41,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ~v2_tdlat_3(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0] : (v2_tdlat_3(X0) | u1_pre_topc(X0) != k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f29,f38])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0] : (v2_tdlat_3(X0) | u1_pre_topc(X0) != k2_tarski(k1_xboole_0,u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (15723)------------------------------
% 0.21/0.52  % (15723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15723)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (15723)Memory used [KB]: 6268
% 0.21/0.52  % (15723)Time elapsed: 0.107 s
% 0.21/0.52  % (15723)------------------------------
% 0.21/0.52  % (15723)------------------------------
% 0.21/0.52  % (15713)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (15727)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (15714)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (15710)Success in time 0.165 s
%------------------------------------------------------------------------------
