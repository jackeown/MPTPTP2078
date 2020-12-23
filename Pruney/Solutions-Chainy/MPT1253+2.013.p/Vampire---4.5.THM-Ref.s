%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 146 expanded)
%              Number of leaves         :   21 (  63 expanded)
%              Depth                    :    9
%              Number of atoms          :  220 ( 400 expanded)
%              Number of equality atoms :   35 (  50 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f891,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f114,f119,f124,f224,f227,f229,f606,f638,f889,f890])).

fof(f890,plain,
    ( spl3_76
    | ~ spl3_54 ),
    inference(avatar_split_clause,[],[f884,f632,f886])).

fof(f886,plain,
    ( spl3_76
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).

fof(f632,plain,
    ( spl3_54
  <=> sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f884,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl3_54 ),
    inference(superposition,[],[f94,f634])).

fof(f634,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl3_54 ),
    inference(avatar_component_clause,[],[f632])).

fof(f94,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f68,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f68,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f889,plain,
    ( ~ spl3_76
    | spl3_1
    | ~ spl3_54 ),
    inference(avatar_split_clause,[],[f879,f632,f106,f886])).

fof(f106,plain,
    ( spl3_1
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f879,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl3_1
    | ~ spl3_54 ),
    inference(superposition,[],[f368,f634])).

fof(f368,plain,
    ( ! [X0] : ~ r1_tarski(k3_tarski(k2_tarski(X0,k2_tops_1(sK0,sK1))),sK1)
    | spl3_1 ),
    inference(superposition,[],[f133,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f133,plain,
    ( ! [X0] : ~ r1_tarski(k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),X0)),sK1)
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f108,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k3_tarski(k2_tarski(X0,X1)),X2) ) ),
    inference(definition_unfolding,[],[f90,f75])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f108,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f106])).

fof(f638,plain,
    ( spl3_54
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_53 ),
    inference(avatar_split_clause,[],[f637,f603,f221,f116,f632])).

fof(f116,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

% (13953)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f221,plain,
    ( spl3_16
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f603,plain,
    ( spl3_53
  <=> sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f637,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f622,f605])).

fof(f605,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_53 ),
    inference(avatar_component_clause,[],[f603])).

fof(f622,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl3_3
    | ~ spl3_16 ),
    inference(resolution,[],[f172,f223])).

fof(f223,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f221])).

fof(f172,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0)) )
    | ~ spl3_3 ),
    inference(resolution,[],[f118,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f92,f75])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f118,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f116])).

fof(f606,plain,
    ( spl3_53
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f601,f216,f211,f603])).

fof(f211,plain,
    ( spl3_14
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

% (13931)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f216,plain,
    ( spl3_15
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

% (13943)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f601,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f213,f218])).

fof(f218,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f216])).

fof(f213,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f211])).

fof(f229,plain,
    ( spl3_14
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f228,f121,f116,f211])).

fof(f121,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f228,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f170,f123])).

fof(f123,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f121])).

fof(f170,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f118,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f227,plain,
    ( spl3_15
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f226,f121,f116,f111,f216])).

fof(f111,plain,
    ( spl3_2
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f226,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f225,f123])).

fof(f225,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f169,f113])).

fof(f113,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f169,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f118,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f224,plain,
    ( spl3_16
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f156,f121,f116,f221])).

fof(f156,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f123,f118,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f124,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f59,f121])).

fof(f59,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f52,f51])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(sK0,X1),X1)
          & v4_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_tops_1(sK0,X1),X1)
        & v4_pre_topc(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
      & v4_pre_topc(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(f119,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f60,f116])).

fof(f60,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f114,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f61,f111])).

fof(f61,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f109,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f62,f106])).

fof(f62,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (13946)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (13938)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.50  % (13933)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.50  % (13946)Refutation not found, incomplete strategy% (13946)------------------------------
% 0.20/0.50  % (13946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (13930)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (13946)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (13946)Memory used [KB]: 10746
% 0.20/0.51  % (13946)Time elapsed: 0.058 s
% 0.20/0.51  % (13946)------------------------------
% 0.20/0.51  % (13946)------------------------------
% 0.20/0.51  % (13949)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.51  % (13926)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (13928)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (13937)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (13941)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (13925)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (13944)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (13941)Refutation not found, incomplete strategy% (13941)------------------------------
% 0.20/0.53  % (13941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (13936)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (13941)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (13941)Memory used [KB]: 10618
% 0.20/0.53  % (13941)Time elapsed: 0.122 s
% 0.20/0.53  % (13941)------------------------------
% 0.20/0.53  % (13941)------------------------------
% 0.20/0.53  % (13927)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (13924)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (13948)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (13929)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (13940)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (13934)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (13952)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (13947)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (13951)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (13932)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.55  % (13950)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (13949)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f891,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f109,f114,f119,f124,f224,f227,f229,f606,f638,f889,f890])).
% 0.20/0.55  fof(f890,plain,(
% 0.20/0.55    spl3_76 | ~spl3_54),
% 0.20/0.55    inference(avatar_split_clause,[],[f884,f632,f886])).
% 0.20/0.55  fof(f886,plain,(
% 0.20/0.55    spl3_76 <=> r1_tarski(sK1,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).
% 0.20/0.55  fof(f632,plain,(
% 0.20/0.55    spl3_54 <=> sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 0.20/0.55  fof(f884,plain,(
% 0.20/0.55    r1_tarski(sK1,sK1) | ~spl3_54),
% 0.20/0.55    inference(superposition,[],[f94,f634])).
% 0.20/0.55  fof(f634,plain,(
% 0.20/0.55    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl3_54),
% 0.20/0.55    inference(avatar_component_clause,[],[f632])).
% 0.20/0.55  fof(f94,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f68,f75])).
% 0.20/0.55  fof(f75,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f14])).
% 0.20/0.55  fof(f14,axiom,(
% 0.20/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.55  fof(f68,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,axiom,(
% 0.20/0.55    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.55  fof(f889,plain,(
% 0.20/0.55    ~spl3_76 | spl3_1 | ~spl3_54),
% 0.20/0.55    inference(avatar_split_clause,[],[f879,f632,f106,f886])).
% 0.20/0.55  fof(f106,plain,(
% 0.20/0.55    spl3_1 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.55  fof(f879,plain,(
% 0.20/0.55    ~r1_tarski(sK1,sK1) | (spl3_1 | ~spl3_54)),
% 0.20/0.55    inference(superposition,[],[f368,f634])).
% 0.20/0.55  fof(f368,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(k3_tarski(k2_tarski(X0,k2_tops_1(sK0,sK1))),sK1)) ) | spl3_1),
% 0.20/0.55    inference(superposition,[],[f133,f72])).
% 0.20/0.55  fof(f72,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,axiom,(
% 0.20/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.55  fof(f133,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),X0)),sK1)) ) | spl3_1),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f108,f102])).
% 0.20/0.55  fof(f102,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k3_tarski(k2_tarski(X0,X1)),X2)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f90,f75])).
% 0.20/0.55  fof(f90,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f47])).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.20/0.55    inference(ennf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.20/0.55  fof(f108,plain,(
% 0.20/0.55    ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | spl3_1),
% 0.20/0.55    inference(avatar_component_clause,[],[f106])).
% 0.20/0.55  fof(f638,plain,(
% 0.20/0.55    spl3_54 | ~spl3_3 | ~spl3_16 | ~spl3_53),
% 0.20/0.55    inference(avatar_split_clause,[],[f637,f603,f221,f116,f632])).
% 0.20/0.55  fof(f116,plain,(
% 0.20/0.55    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.55  % (13953)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.55  fof(f221,plain,(
% 0.20/0.55    spl3_16 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.55  fof(f603,plain,(
% 0.20/0.55    spl3_53 <=> sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 0.20/0.55  fof(f637,plain,(
% 0.20/0.55    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl3_3 | ~spl3_16 | ~spl3_53)),
% 0.20/0.55    inference(forward_demodulation,[],[f622,f605])).
% 0.20/0.55  fof(f605,plain,(
% 0.20/0.55    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl3_53),
% 0.20/0.55    inference(avatar_component_clause,[],[f603])).
% 0.20/0.55  fof(f622,plain,(
% 0.20/0.55    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl3_3 | ~spl3_16)),
% 0.20/0.55    inference(resolution,[],[f172,f223])).
% 0.20/0.55  fof(f223,plain,(
% 0.20/0.55    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_16),
% 0.20/0.55    inference(avatar_component_clause,[],[f221])).
% 0.20/0.55  fof(f172,plain,(
% 0.20/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))) ) | ~spl3_3),
% 0.20/0.55    inference(resolution,[],[f118,f104])).
% 0.20/0.55  fof(f104,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f92,f75])).
% 0.20/0.55  fof(f92,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f50])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.55    inference(flattening,[],[f49])).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.20/0.55    inference(ennf_transformation,[],[f19])).
% 0.20/0.55  fof(f19,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.20/0.55  fof(f118,plain,(
% 0.20/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 0.20/0.55    inference(avatar_component_clause,[],[f116])).
% 0.20/0.55  fof(f606,plain,(
% 0.20/0.55    spl3_53 | ~spl3_14 | ~spl3_15),
% 0.20/0.55    inference(avatar_split_clause,[],[f601,f216,f211,f603])).
% 0.20/0.55  fof(f211,plain,(
% 0.20/0.55    spl3_14 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.55  % (13931)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.55  fof(f216,plain,(
% 0.20/0.55    spl3_15 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.55  % (13943)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  fof(f601,plain,(
% 0.20/0.55    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl3_14 | ~spl3_15)),
% 0.20/0.55    inference(forward_demodulation,[],[f213,f218])).
% 0.20/0.55  fof(f218,plain,(
% 0.20/0.55    sK1 = k2_pre_topc(sK0,sK1) | ~spl3_15),
% 0.20/0.55    inference(avatar_component_clause,[],[f216])).
% 0.20/0.55  fof(f213,plain,(
% 0.20/0.55    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl3_14),
% 0.20/0.55    inference(avatar_component_clause,[],[f211])).
% 0.20/0.55  fof(f229,plain,(
% 0.20/0.55    spl3_14 | ~spl3_3 | ~spl3_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f228,f121,f116,f211])).
% 0.20/0.55  fof(f121,plain,(
% 0.20/0.55    spl3_4 <=> l1_pre_topc(sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.55  fof(f228,plain,(
% 0.20/0.55    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl3_3 | ~spl3_4)),
% 0.20/0.55    inference(subsumption_resolution,[],[f170,f123])).
% 0.20/0.55  fof(f123,plain,(
% 0.20/0.55    l1_pre_topc(sK0) | ~spl3_4),
% 0.20/0.55    inference(avatar_component_clause,[],[f121])).
% 0.20/0.55  fof(f170,plain,(
% 0.20/0.55    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl3_3),
% 0.20/0.55    inference(resolution,[],[f118,f65])).
% 0.20/0.55  fof(f65,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f34])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f27])).
% 0.20/0.55  fof(f27,axiom,(
% 0.20/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 0.20/0.55  fof(f227,plain,(
% 0.20/0.55    spl3_15 | ~spl3_2 | ~spl3_3 | ~spl3_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f226,f121,f116,f111,f216])).
% 0.20/0.55  fof(f111,plain,(
% 0.20/0.55    spl3_2 <=> v4_pre_topc(sK1,sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.55  fof(f226,plain,(
% 0.20/0.55    sK1 = k2_pre_topc(sK0,sK1) | (~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.20/0.55    inference(subsumption_resolution,[],[f225,f123])).
% 0.20/0.55  fof(f225,plain,(
% 0.20/0.55    sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl3_2 | ~spl3_3)),
% 0.20/0.55    inference(subsumption_resolution,[],[f169,f113])).
% 0.20/0.55  fof(f113,plain,(
% 0.20/0.55    v4_pre_topc(sK1,sK0) | ~spl3_2),
% 0.20/0.55    inference(avatar_component_clause,[],[f111])).
% 0.20/0.55  fof(f169,plain,(
% 0.20/0.55    sK1 = k2_pre_topc(sK0,sK1) | ~v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~spl3_3),
% 0.20/0.55    inference(resolution,[],[f118,f66])).
% 0.20/0.55  fof(f66,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f36])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(flattening,[],[f35])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f30])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1)))),
% 0.20/0.55    inference(pure_predicate_removal,[],[f24])).
% 0.20/0.55  fof(f24,axiom,(
% 0.20/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.20/0.55  fof(f224,plain,(
% 0.20/0.55    spl3_16 | ~spl3_3 | ~spl3_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f156,f121,f116,f221])).
% 0.20/0.55  fof(f156,plain,(
% 0.20/0.55    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_3 | ~spl3_4)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f123,f118,f82])).
% 0.20/0.55  fof(f82,plain,(
% 0.20/0.55    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f43])).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(flattening,[],[f42])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f25])).
% 0.20/0.55  fof(f25,axiom,(
% 0.20/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.20/0.55  fof(f124,plain,(
% 0.20/0.55    spl3_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f59,f121])).
% 0.20/0.55  fof(f59,plain,(
% 0.20/0.55    l1_pre_topc(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f53])).
% 0.20/0.55  fof(f53,plain,(
% 0.20/0.55    (~r1_tarski(k2_tops_1(sK0,sK1),sK1) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f52,f51])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),X1) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f52,plain,(
% 0.20/0.55    ? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),X1) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k2_tops_1(sK0,sK1),sK1) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.55    inference(flattening,[],[f31])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : ((~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f29])).
% 0.20/0.55  fof(f29,negated_conjecture,(
% 0.20/0.55    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 0.20/0.55    inference(negated_conjecture,[],[f28])).
% 0.20/0.55  fof(f28,conjecture,(
% 0.20/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).
% 0.20/0.55  fof(f119,plain,(
% 0.20/0.55    spl3_3),
% 0.20/0.55    inference(avatar_split_clause,[],[f60,f116])).
% 0.20/0.55  fof(f60,plain,(
% 0.20/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.55    inference(cnf_transformation,[],[f53])).
% 0.20/0.55  fof(f114,plain,(
% 0.20/0.55    spl3_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f61,f111])).
% 0.20/0.55  fof(f61,plain,(
% 0.20/0.55    v4_pre_topc(sK1,sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f53])).
% 0.20/0.55  fof(f109,plain,(
% 0.20/0.55    ~spl3_1),
% 0.20/0.55    inference(avatar_split_clause,[],[f62,f106])).
% 0.20/0.55  fof(f62,plain,(
% 0.20/0.55    ~r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f53])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (13949)------------------------------
% 0.20/0.55  % (13949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (13949)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (13949)Memory used [KB]: 6780
% 0.20/0.55  % (13949)Time elapsed: 0.142 s
% 0.20/0.55  % (13949)------------------------------
% 0.20/0.55  % (13949)------------------------------
% 0.20/0.55  % (13942)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (13923)Success in time 0.195 s
%------------------------------------------------------------------------------
