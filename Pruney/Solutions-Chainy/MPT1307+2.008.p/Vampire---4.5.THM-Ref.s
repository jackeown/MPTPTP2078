%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   60 (  97 expanded)
%              Number of leaves         :   14 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :  174 ( 298 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f85,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f31,f36,f41,f55,f60,f66,f71,f77,f80])).

fof(f80,plain,
    ( spl3_6
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | spl3_6
    | ~ spl3_10 ),
    inference(resolution,[],[f76,f54])).

fof(f54,plain,
    ( ~ v2_tops_2(k4_xboole_0(sK1,sK2),sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl3_6
  <=> v2_tops_2(k4_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f76,plain,
    ( ! [X0] : v2_tops_2(k4_xboole_0(sK1,X0),sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl3_10
  <=> ! [X0] : v2_tops_2(k4_xboole_0(sK1,X0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f77,plain,
    ( spl3_10
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f73,f69,f28,f75])).

fof(f28,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f69,plain,
    ( spl3_9
  <=> ! [X0] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(k4_xboole_0(sK1,X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f73,plain,
    ( ! [X0] : v2_tops_2(k4_xboole_0(sK1,X0),sK0)
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f72,f30])).

fof(f30,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f72,plain,
    ( ! [X0] :
        ( v2_tops_2(k4_xboole_0(sK1,X0),sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl3_9 ),
    inference(resolution,[],[f70,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f20,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f70,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(k4_xboole_0(sK1,X0),sK0) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f71,plain,
    ( spl3_9
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f67,f64,f69])).

fof(f64,plain,
    ( spl3_8
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f67,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(k4_xboole_0(sK1,X0),sK0) )
    | ~ spl3_8 ),
    inference(resolution,[],[f65,f19])).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f65,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f64])).

fof(f66,plain,
    ( spl3_8
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f62,f58,f38,f28,f64])).

fof(f38,plain,
    ( spl3_4
  <=> v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f58,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X0,X1)
        | ~ v2_tops_2(X1,sK0)
        | v2_tops_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f62,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0) )
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f61,f30])).

fof(f61,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0) )
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(resolution,[],[f59,f40])).

fof(f40,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( ~ v2_tops_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f60,plain,
    ( spl3_7
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f56,f23,f58])).

fof(f23,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X0,X1)
        | ~ v2_tops_2(X1,sK0)
        | v2_tops_2(X0,sK0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f18,f25])).

fof(f25,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r1_tarski(X1,X2)
      | ~ v2_tops_2(X2,X0)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tops_2(X1,X0)
              | ~ v2_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tops_2(X1,X0)
              | ~ v2_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v2_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v2_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tops_2)).

fof(f55,plain,
    ( ~ spl3_6
    | ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f50,f33,f28,f52])).

fof(f33,plain,
    ( spl3_3
  <=> v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f50,plain,
    ( ~ v2_tops_2(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl3_2
    | spl3_3 ),
    inference(subsumption_resolution,[],[f47,f30])).

fof(f47,plain,
    ( ~ v2_tops_2(k4_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl3_3 ),
    inference(superposition,[],[f35,f21])).

fof(f35,plain,
    ( ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f41,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f14,f38])).

fof(f14,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v2_tops_2(X1,X0)
                 => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v2_tops_2(X1,X0)
               => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tops_2)).

fof(f36,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f15,f33])).

fof(f15,plain,(
    ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f31,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f16,f28])).

fof(f16,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f8])).

fof(f26,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f17,f23])).

fof(f17,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:08:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.41  % (26459)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.41  % (26459)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f85,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(avatar_sat_refutation,[],[f26,f31,f36,f41,f55,f60,f66,f71,f77,f80])).
% 0.20/0.41  fof(f80,plain,(
% 0.20/0.41    spl3_6 | ~spl3_10),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f78])).
% 0.20/0.41  fof(f78,plain,(
% 0.20/0.41    $false | (spl3_6 | ~spl3_10)),
% 0.20/0.41    inference(resolution,[],[f76,f54])).
% 0.20/0.41  fof(f54,plain,(
% 0.20/0.41    ~v2_tops_2(k4_xboole_0(sK1,sK2),sK0) | spl3_6),
% 0.20/0.41    inference(avatar_component_clause,[],[f52])).
% 0.20/0.41  fof(f52,plain,(
% 0.20/0.41    spl3_6 <=> v2_tops_2(k4_xboole_0(sK1,sK2),sK0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.41  fof(f76,plain,(
% 0.20/0.41    ( ! [X0] : (v2_tops_2(k4_xboole_0(sK1,X0),sK0)) ) | ~spl3_10),
% 0.20/0.41    inference(avatar_component_clause,[],[f75])).
% 0.20/0.41  fof(f75,plain,(
% 0.20/0.41    spl3_10 <=> ! [X0] : v2_tops_2(k4_xboole_0(sK1,X0),sK0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.41  fof(f77,plain,(
% 0.20/0.41    spl3_10 | ~spl3_2 | ~spl3_9),
% 0.20/0.41    inference(avatar_split_clause,[],[f73,f69,f28,f75])).
% 0.20/0.41  fof(f28,plain,(
% 0.20/0.41    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.41  fof(f69,plain,(
% 0.20/0.41    spl3_9 <=> ! [X0] : (~m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(k4_xboole_0(sK1,X0),sK0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.41  fof(f73,plain,(
% 0.20/0.41    ( ! [X0] : (v2_tops_2(k4_xboole_0(sK1,X0),sK0)) ) | (~spl3_2 | ~spl3_9)),
% 0.20/0.41    inference(subsumption_resolution,[],[f72,f30])).
% 0.20/0.41  fof(f30,plain,(
% 0.20/0.41    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_2),
% 0.20/0.41    inference(avatar_component_clause,[],[f28])).
% 0.20/0.41  fof(f72,plain,(
% 0.20/0.41    ( ! [X0] : (v2_tops_2(k4_xboole_0(sK1,X0),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl3_9),
% 0.20/0.41    inference(resolution,[],[f70,f49])).
% 0.20/0.41  fof(f49,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.41    inference(duplicate_literal_removal,[],[f48])).
% 0.20/0.41  fof(f48,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.41    inference(superposition,[],[f20,f21])).
% 0.20/0.41  fof(f21,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f12])).
% 0.20/0.41  fof(f12,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.41    inference(ennf_transformation,[],[f3])).
% 0.20/0.41  fof(f3,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.20/0.41  fof(f20,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f11])).
% 0.20/0.41  fof(f11,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.41    inference(ennf_transformation,[],[f2])).
% 0.20/0.41  fof(f2,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).
% 0.20/0.41  fof(f70,plain,(
% 0.20/0.41    ( ! [X0] : (~m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(k4_xboole_0(sK1,X0),sK0)) ) | ~spl3_9),
% 0.20/0.41    inference(avatar_component_clause,[],[f69])).
% 0.20/0.41  fof(f71,plain,(
% 0.20/0.41    spl3_9 | ~spl3_8),
% 0.20/0.41    inference(avatar_split_clause,[],[f67,f64,f69])).
% 0.20/0.41  fof(f64,plain,(
% 0.20/0.41    spl3_8 <=> ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.41  fof(f67,plain,(
% 0.20/0.41    ( ! [X0] : (~m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(k4_xboole_0(sK1,X0),sK0)) ) | ~spl3_8),
% 0.20/0.41    inference(resolution,[],[f65,f19])).
% 0.20/0.41  fof(f19,plain,(
% 0.20/0.41    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.41  fof(f65,plain,(
% 0.20/0.41    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0)) ) | ~spl3_8),
% 0.20/0.41    inference(avatar_component_clause,[],[f64])).
% 0.20/0.41  fof(f66,plain,(
% 0.20/0.41    spl3_8 | ~spl3_2 | ~spl3_4 | ~spl3_7),
% 0.20/0.41    inference(avatar_split_clause,[],[f62,f58,f38,f28,f64])).
% 0.20/0.41  fof(f38,plain,(
% 0.20/0.41    spl3_4 <=> v2_tops_2(sK1,sK0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.41  fof(f58,plain,(
% 0.20/0.41    spl3_7 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X0,X1) | ~v2_tops_2(X1,sK0) | v2_tops_2(X0,sK0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.41  fof(f62,plain,(
% 0.20/0.41    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0)) ) | (~spl3_2 | ~spl3_4 | ~spl3_7)),
% 0.20/0.41    inference(subsumption_resolution,[],[f61,f30])).
% 0.20/0.41  fof(f61,plain,(
% 0.20/0.41    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0)) ) | (~spl3_4 | ~spl3_7)),
% 0.20/0.41    inference(resolution,[],[f59,f40])).
% 0.20/0.41  fof(f40,plain,(
% 0.20/0.41    v2_tops_2(sK1,sK0) | ~spl3_4),
% 0.20/0.41    inference(avatar_component_clause,[],[f38])).
% 0.20/0.41  fof(f59,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~v2_tops_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0)) ) | ~spl3_7),
% 0.20/0.41    inference(avatar_component_clause,[],[f58])).
% 0.20/0.41  fof(f60,plain,(
% 0.20/0.41    spl3_7 | ~spl3_1),
% 0.20/0.41    inference(avatar_split_clause,[],[f56,f23,f58])).
% 0.20/0.41  fof(f23,plain,(
% 0.20/0.41    spl3_1 <=> l1_pre_topc(sK0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.41  fof(f56,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X0,X1) | ~v2_tops_2(X1,sK0) | v2_tops_2(X0,sK0)) ) | ~spl3_1),
% 0.20/0.41    inference(resolution,[],[f18,f25])).
% 0.20/0.41  fof(f25,plain,(
% 0.20/0.41    l1_pre_topc(sK0) | ~spl3_1),
% 0.20/0.41    inference(avatar_component_clause,[],[f23])).
% 0.20/0.41  fof(f18,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X1,X2) | ~v2_tops_2(X2,X0) | v2_tops_2(X1,X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f10])).
% 0.20/0.41  fof(f10,plain,(
% 0.20/0.41    ! [X0] : (! [X1] : (! [X2] : (v2_tops_2(X1,X0) | ~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.41    inference(flattening,[],[f9])).
% 0.20/0.41  fof(f9,plain,(
% 0.20/0.41    ! [X0] : (! [X1] : (! [X2] : ((v2_tops_2(X1,X0) | (~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.41    inference(ennf_transformation,[],[f4])).
% 0.20/0.41  fof(f4,axiom,(
% 0.20/0.41    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v2_tops_2(X2,X0) & r1_tarski(X1,X2)) => v2_tops_2(X1,X0)))))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tops_2)).
% 0.20/0.41  fof(f55,plain,(
% 0.20/0.41    ~spl3_6 | ~spl3_2 | spl3_3),
% 0.20/0.41    inference(avatar_split_clause,[],[f50,f33,f28,f52])).
% 0.20/0.41  fof(f33,plain,(
% 0.20/0.41    spl3_3 <=> v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.41  fof(f50,plain,(
% 0.20/0.41    ~v2_tops_2(k4_xboole_0(sK1,sK2),sK0) | (~spl3_2 | spl3_3)),
% 0.20/0.41    inference(subsumption_resolution,[],[f47,f30])).
% 0.20/0.41  fof(f47,plain,(
% 0.20/0.41    ~v2_tops_2(k4_xboole_0(sK1,sK2),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl3_3),
% 0.20/0.41    inference(superposition,[],[f35,f21])).
% 0.20/0.41  fof(f35,plain,(
% 0.20/0.41    ~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) | spl3_3),
% 0.20/0.41    inference(avatar_component_clause,[],[f33])).
% 0.20/0.41  fof(f41,plain,(
% 0.20/0.41    spl3_4),
% 0.20/0.41    inference(avatar_split_clause,[],[f14,f38])).
% 0.20/0.41  fof(f14,plain,(
% 0.20/0.41    v2_tops_2(sK1,sK0)),
% 0.20/0.41    inference(cnf_transformation,[],[f8])).
% 0.20/0.41  fof(f8,plain,(
% 0.20/0.41    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.20/0.41    inference(flattening,[],[f7])).
% 0.20/0.41  fof(f7,plain,(
% 0.20/0.41    ? [X0] : (? [X1] : (? [X2] : ((~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.20/0.41    inference(ennf_transformation,[],[f6])).
% 0.20/0.41  fof(f6,negated_conjecture,(
% 0.20/0.41    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.20/0.41    inference(negated_conjecture,[],[f5])).
% 0.20/0.41  fof(f5,conjecture,(
% 0.20/0.41    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tops_2)).
% 0.20/0.41  fof(f36,plain,(
% 0.20/0.41    ~spl3_3),
% 0.20/0.41    inference(avatar_split_clause,[],[f15,f33])).
% 0.20/0.41  fof(f15,plain,(
% 0.20/0.41    ~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.20/0.41    inference(cnf_transformation,[],[f8])).
% 0.20/0.41  fof(f31,plain,(
% 0.20/0.41    spl3_2),
% 0.20/0.41    inference(avatar_split_clause,[],[f16,f28])).
% 0.20/0.41  fof(f16,plain,(
% 0.20/0.41    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.41    inference(cnf_transformation,[],[f8])).
% 0.20/0.41  fof(f26,plain,(
% 0.20/0.41    spl3_1),
% 0.20/0.41    inference(avatar_split_clause,[],[f17,f23])).
% 0.20/0.41  fof(f17,plain,(
% 0.20/0.41    l1_pre_topc(sK0)),
% 0.20/0.41    inference(cnf_transformation,[],[f8])).
% 0.20/0.41  % SZS output end Proof for theBenchmark
% 0.20/0.41  % (26459)------------------------------
% 0.20/0.41  % (26459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (26459)Termination reason: Refutation
% 0.20/0.41  
% 0.20/0.41  % (26459)Memory used [KB]: 10618
% 0.20/0.41  % (26459)Time elapsed: 0.006 s
% 0.20/0.41  % (26459)------------------------------
% 0.20/0.41  % (26459)------------------------------
% 0.20/0.41  % (26454)Success in time 0.055 s
%------------------------------------------------------------------------------
