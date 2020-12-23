%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:53 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 118 expanded)
%              Number of leaves         :   15 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :  249 ( 424 expanded)
%              Number of equality atoms :   29 (  52 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f103,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f36,f41,f46,f51,f60,f72,f83,f91,f93,f102])).

fof(f102,plain,
    ( ~ spl2_2
    | ~ spl2_3
    | spl2_5
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_12 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_3
    | spl2_5
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f100,f50])).

fof(f50,plain,
    ( k1_xboole_0 != sK1
    | spl2_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl2_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f100,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f99,f67])).

fof(f67,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl2_7
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f99,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f98,f40])).

fof(f40,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl2_3
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f98,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_12 ),
    inference(resolution,[],[f94,f59])).

fof(f59,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl2_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | k1_tops_1(sK0,X0) = X0 )
    | ~ spl2_2
    | ~ spl2_12 ),
    inference(resolution,[],[f90,f35])).

fof(f35,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f90,plain,
    ( ! [X5,X3] :
        ( ~ l1_pre_topc(X3)
        | k1_tops_1(X3,X5) = X5
        | ~ v3_pre_topc(X5,X3)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl2_12
  <=> ! [X3,X5] :
        ( ~ l1_pre_topc(X3)
        | k1_tops_1(X3,X5) = X5
        | ~ v3_pre_topc(X5,X3)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f93,plain,
    ( ~ spl2_6
    | ~ spl2_11 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(resolution,[],[f87,f59])).

fof(f87,plain,
    ( ! [X4] : ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl2_11
  <=> ! [X4] : ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f91,plain,
    ( spl2_11
    | spl2_12
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f84,f33,f28,f89,f86])).

fof(f28,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f84,plain,
    ( ! [X4,X5,X3] :
        ( ~ l1_pre_topc(X3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ v3_pre_topc(X5,X3)
        | k1_tops_1(X3,X5) = X5 )
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f53,f35])).

fof(f53,plain,
    ( ! [X4,X5,X3] :
        ( ~ l1_pre_topc(sK0)
        | ~ l1_pre_topc(X3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ v3_pre_topc(X5,X3)
        | k1_tops_1(X3,X5) = X5 )
    | ~ spl2_1 ),
    inference(resolution,[],[f30,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X3,X1)
      | k1_tops_1(X1,X3) = X3 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

fof(f30,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f83,plain,
    ( ~ spl2_2
    | ~ spl2_4
    | ~ spl2_6
    | spl2_8 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_6
    | spl2_8 ),
    inference(subsumption_resolution,[],[f81,f59])).

fof(f81,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_4
    | spl2_8 ),
    inference(subsumption_resolution,[],[f80,f45])).

fof(f45,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl2_4
  <=> v3_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f80,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | spl2_8 ),
    inference(resolution,[],[f71,f55])).

fof(f55,plain,
    ( ! [X1] :
        ( v2_tops_1(X1,sK0)
        | ~ v3_tops_1(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_2 ),
    inference(resolution,[],[f35,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tops_1(X1,X0)
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).

fof(f71,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl2_8 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl2_8
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f72,plain,
    ( spl2_7
    | ~ spl2_8
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f62,f57,f33,f69,f65])).

fof(f62,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(resolution,[],[f61,f59])).

fof(f61,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tops_1(X0,sK0)
        | k1_xboole_0 = k1_tops_1(sK0,X0) )
    | ~ spl2_2 ),
    inference(resolution,[],[f54,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f54,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tops_1(X0,sK0) )
    | ~ spl2_2 ),
    inference(resolution,[],[f35,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v2_tops_1(X1,X0)
        & l1_pre_topc(X0) )
     => v1_xboole_0(k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_tops_1)).

fof(f60,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f16,f57])).

fof(f16,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v3_tops_1(X1,X0)
                & v3_pre_topc(X1,X0) )
             => k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tops_1(X1,X0)
              & v3_pre_topc(X1,X0) )
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).

fof(f51,plain,(
    ~ spl2_5 ),
    inference(avatar_split_clause,[],[f19,f48])).

fof(f19,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f46,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f18,f43])).

fof(f18,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f41,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f17,f38])).

fof(f17,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f36,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f21,f33])).

fof(f21,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f31,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f20,f28])).

fof(f20,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.10  % Command    : run_vampire %s %d
% 0.09/0.28  % Computer   : n022.cluster.edu
% 0.09/0.28  % Model      : x86_64 x86_64
% 0.09/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.28  % Memory     : 8042.1875MB
% 0.09/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.28  % CPULimit   : 60
% 0.09/0.28  % WCLimit    : 600
% 0.09/0.28  % DateTime   : Tue Dec  1 17:42:25 EST 2020
% 0.09/0.28  % CPUTime    : 
% 0.14/0.36  % (3807)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.14/0.38  % (3807)Refutation not found, incomplete strategy% (3807)------------------------------
% 0.14/0.38  % (3807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.14/0.38  % (3807)Termination reason: Refutation not found, incomplete strategy
% 0.14/0.38  
% 0.14/0.38  % (3807)Memory used [KB]: 10618
% 0.14/0.38  % (3807)Time elapsed: 0.050 s
% 0.14/0.38  % (3807)------------------------------
% 0.14/0.38  % (3807)------------------------------
% 0.14/0.38  % (3809)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.14/0.38  % (3813)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.14/0.40  % (3809)Refutation found. Thanks to Tanya!
% 0.14/0.40  % SZS status Theorem for theBenchmark
% 0.14/0.40  % SZS output start Proof for theBenchmark
% 0.14/0.40  fof(f103,plain,(
% 0.14/0.40    $false),
% 0.14/0.40    inference(avatar_sat_refutation,[],[f31,f36,f41,f46,f51,f60,f72,f83,f91,f93,f102])).
% 0.14/0.40  fof(f102,plain,(
% 0.14/0.40    ~spl2_2 | ~spl2_3 | spl2_5 | ~spl2_6 | ~spl2_7 | ~spl2_12),
% 0.14/0.40    inference(avatar_contradiction_clause,[],[f101])).
% 0.14/0.40  fof(f101,plain,(
% 0.14/0.40    $false | (~spl2_2 | ~spl2_3 | spl2_5 | ~spl2_6 | ~spl2_7 | ~spl2_12)),
% 0.14/0.40    inference(subsumption_resolution,[],[f100,f50])).
% 0.14/0.40  fof(f50,plain,(
% 0.14/0.40    k1_xboole_0 != sK1 | spl2_5),
% 0.14/0.40    inference(avatar_component_clause,[],[f48])).
% 0.14/0.40  fof(f48,plain,(
% 0.14/0.40    spl2_5 <=> k1_xboole_0 = sK1),
% 0.14/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.14/0.40  fof(f100,plain,(
% 0.14/0.40    k1_xboole_0 = sK1 | (~spl2_2 | ~spl2_3 | ~spl2_6 | ~spl2_7 | ~spl2_12)),
% 0.14/0.40    inference(forward_demodulation,[],[f99,f67])).
% 0.14/0.40  fof(f67,plain,(
% 0.14/0.40    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl2_7),
% 0.14/0.40    inference(avatar_component_clause,[],[f65])).
% 0.14/0.40  fof(f65,plain,(
% 0.14/0.40    spl2_7 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.14/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.14/0.40  fof(f99,plain,(
% 0.14/0.40    sK1 = k1_tops_1(sK0,sK1) | (~spl2_2 | ~spl2_3 | ~spl2_6 | ~spl2_12)),
% 0.14/0.40    inference(subsumption_resolution,[],[f98,f40])).
% 0.14/0.40  fof(f40,plain,(
% 0.14/0.40    v3_pre_topc(sK1,sK0) | ~spl2_3),
% 0.14/0.40    inference(avatar_component_clause,[],[f38])).
% 0.14/0.40  fof(f38,plain,(
% 0.14/0.40    spl2_3 <=> v3_pre_topc(sK1,sK0)),
% 0.14/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.14/0.40  fof(f98,plain,(
% 0.14/0.40    ~v3_pre_topc(sK1,sK0) | sK1 = k1_tops_1(sK0,sK1) | (~spl2_2 | ~spl2_6 | ~spl2_12)),
% 0.14/0.40    inference(resolution,[],[f94,f59])).
% 0.14/0.40  fof(f59,plain,(
% 0.14/0.40    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_6),
% 0.14/0.40    inference(avatar_component_clause,[],[f57])).
% 0.14/0.40  fof(f57,plain,(
% 0.14/0.40    spl2_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.14/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.14/0.40  fof(f94,plain,(
% 0.14/0.40    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | k1_tops_1(sK0,X0) = X0) ) | (~spl2_2 | ~spl2_12)),
% 0.14/0.40    inference(resolution,[],[f90,f35])).
% 0.14/0.40  fof(f35,plain,(
% 0.14/0.40    l1_pre_topc(sK0) | ~spl2_2),
% 0.14/0.40    inference(avatar_component_clause,[],[f33])).
% 0.14/0.40  fof(f33,plain,(
% 0.14/0.40    spl2_2 <=> l1_pre_topc(sK0)),
% 0.14/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.14/0.40  fof(f90,plain,(
% 0.14/0.40    ( ! [X5,X3] : (~l1_pre_topc(X3) | k1_tops_1(X3,X5) = X5 | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) ) | ~spl2_12),
% 0.14/0.40    inference(avatar_component_clause,[],[f89])).
% 0.14/0.40  fof(f89,plain,(
% 0.14/0.40    spl2_12 <=> ! [X3,X5] : (~l1_pre_topc(X3) | k1_tops_1(X3,X5) = X5 | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))))),
% 0.14/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.14/0.40  fof(f93,plain,(
% 0.14/0.40    ~spl2_6 | ~spl2_11),
% 0.14/0.40    inference(avatar_contradiction_clause,[],[f92])).
% 0.14/0.40  fof(f92,plain,(
% 0.14/0.40    $false | (~spl2_6 | ~spl2_11)),
% 0.14/0.40    inference(resolution,[],[f87,f59])).
% 0.14/0.40  fof(f87,plain,(
% 0.14/0.40    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_11),
% 0.14/0.40    inference(avatar_component_clause,[],[f86])).
% 0.14/0.40  fof(f86,plain,(
% 0.14/0.40    spl2_11 <=> ! [X4] : ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.14/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.14/0.40  fof(f91,plain,(
% 0.14/0.40    spl2_11 | spl2_12 | ~spl2_1 | ~spl2_2),
% 0.14/0.40    inference(avatar_split_clause,[],[f84,f33,f28,f89,f86])).
% 0.14/0.40  fof(f28,plain,(
% 0.14/0.40    spl2_1 <=> v2_pre_topc(sK0)),
% 0.14/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.14/0.40  fof(f84,plain,(
% 0.14/0.40    ( ! [X4,X5,X3] : (~l1_pre_topc(X3) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~v3_pre_topc(X5,X3) | k1_tops_1(X3,X5) = X5) ) | (~spl2_1 | ~spl2_2)),
% 0.14/0.40    inference(subsumption_resolution,[],[f53,f35])).
% 0.14/0.40  fof(f53,plain,(
% 0.14/0.40    ( ! [X4,X5,X3] : (~l1_pre_topc(sK0) | ~l1_pre_topc(X3) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~v3_pre_topc(X5,X3) | k1_tops_1(X3,X5) = X5) ) | ~spl2_1),
% 0.14/0.40    inference(resolution,[],[f30,f25])).
% 0.14/0.40  fof(f25,plain,(
% 0.14/0.40    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1) | k1_tops_1(X1,X3) = X3) )),
% 0.14/0.40    inference(cnf_transformation,[],[f13])).
% 0.14/0.40  fof(f13,plain,(
% 0.14/0.40    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.14/0.40    inference(flattening,[],[f12])).
% 0.14/0.40  fof(f12,plain,(
% 0.14/0.40    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.14/0.40    inference(ennf_transformation,[],[f3])).
% 0.14/0.40  fof(f3,axiom,(
% 0.14/0.40    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 0.14/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 0.14/0.40  fof(f30,plain,(
% 0.14/0.40    v2_pre_topc(sK0) | ~spl2_1),
% 0.14/0.40    inference(avatar_component_clause,[],[f28])).
% 0.14/0.40  fof(f83,plain,(
% 0.14/0.40    ~spl2_2 | ~spl2_4 | ~spl2_6 | spl2_8),
% 0.14/0.40    inference(avatar_contradiction_clause,[],[f82])).
% 0.14/0.40  fof(f82,plain,(
% 0.14/0.40    $false | (~spl2_2 | ~spl2_4 | ~spl2_6 | spl2_8)),
% 0.14/0.40    inference(subsumption_resolution,[],[f81,f59])).
% 0.14/0.40  fof(f81,plain,(
% 0.14/0.40    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_4 | spl2_8)),
% 0.14/0.40    inference(subsumption_resolution,[],[f80,f45])).
% 0.14/0.40  fof(f45,plain,(
% 0.14/0.40    v3_tops_1(sK1,sK0) | ~spl2_4),
% 0.14/0.40    inference(avatar_component_clause,[],[f43])).
% 0.14/0.40  fof(f43,plain,(
% 0.14/0.40    spl2_4 <=> v3_tops_1(sK1,sK0)),
% 0.14/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.14/0.40  fof(f80,plain,(
% 0.14/0.40    ~v3_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | spl2_8)),
% 0.14/0.40    inference(resolution,[],[f71,f55])).
% 0.14/0.40  fof(f55,plain,(
% 0.14/0.40    ( ! [X1] : (v2_tops_1(X1,sK0) | ~v3_tops_1(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_2),
% 0.14/0.40    inference(resolution,[],[f35,f23])).
% 0.14/0.40  fof(f23,plain,(
% 0.14/0.40    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tops_1(X1,X0) | v2_tops_1(X1,X0)) )),
% 0.14/0.40    inference(cnf_transformation,[],[f11])).
% 0.14/0.40  fof(f11,plain,(
% 0.14/0.40    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.14/0.40    inference(flattening,[],[f10])).
% 0.14/0.40  fof(f10,plain,(
% 0.14/0.40    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.14/0.40    inference(ennf_transformation,[],[f4])).
% 0.14/0.40  fof(f4,axiom,(
% 0.14/0.40    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 0.14/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).
% 0.14/0.40  fof(f71,plain,(
% 0.14/0.40    ~v2_tops_1(sK1,sK0) | spl2_8),
% 0.14/0.40    inference(avatar_component_clause,[],[f69])).
% 0.14/0.40  fof(f69,plain,(
% 0.14/0.40    spl2_8 <=> v2_tops_1(sK1,sK0)),
% 0.14/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.14/0.40  fof(f72,plain,(
% 0.14/0.40    spl2_7 | ~spl2_8 | ~spl2_2 | ~spl2_6),
% 0.14/0.40    inference(avatar_split_clause,[],[f62,f57,f33,f69,f65])).
% 0.14/0.40  fof(f62,plain,(
% 0.14/0.40    ~v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) | (~spl2_2 | ~spl2_6)),
% 0.14/0.40    inference(resolution,[],[f61,f59])).
% 0.14/0.40  fof(f61,plain,(
% 0.14/0.40    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(X0,sK0) | k1_xboole_0 = k1_tops_1(sK0,X0)) ) | ~spl2_2),
% 0.14/0.40    inference(resolution,[],[f54,f22])).
% 0.14/0.40  fof(f22,plain,(
% 0.14/0.40    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.14/0.40    inference(cnf_transformation,[],[f9])).
% 0.14/0.40  fof(f9,plain,(
% 0.14/0.40    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.14/0.40    inference(ennf_transformation,[],[f1])).
% 0.14/0.40  fof(f1,axiom,(
% 0.14/0.40    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.14/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.14/0.40  fof(f54,plain,(
% 0.14/0.40    ( ! [X0] : (v1_xboole_0(k1_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(X0,sK0)) ) | ~spl2_2),
% 0.14/0.40    inference(resolution,[],[f35,f26])).
% 0.14/0.40  fof(f26,plain,(
% 0.14/0.40    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(k1_tops_1(X0,X1))) )),
% 0.14/0.40    inference(cnf_transformation,[],[f15])).
% 0.14/0.40  fof(f15,plain,(
% 0.14/0.40    ! [X0,X1] : (v1_xboole_0(k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_1(X1,X0) | ~l1_pre_topc(X0))),
% 0.14/0.40    inference(flattening,[],[f14])).
% 0.14/0.40  fof(f14,plain,(
% 0.14/0.40    ! [X0,X1] : (v1_xboole_0(k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_1(X1,X0) | ~l1_pre_topc(X0)))),
% 0.14/0.40    inference(ennf_transformation,[],[f2])).
% 0.14/0.40  fof(f2,axiom,(
% 0.14/0.40    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_tops_1(X1,X0) & l1_pre_topc(X0)) => v1_xboole_0(k1_tops_1(X0,X1)))),
% 0.14/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_tops_1)).
% 0.14/0.40  fof(f60,plain,(
% 0.14/0.40    spl2_6),
% 0.14/0.40    inference(avatar_split_clause,[],[f16,f57])).
% 0.14/0.40  fof(f16,plain,(
% 0.14/0.40    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.14/0.40    inference(cnf_transformation,[],[f8])).
% 0.14/0.40  fof(f8,plain,(
% 0.14/0.40    ? [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.14/0.40    inference(flattening,[],[f7])).
% 0.14/0.40  fof(f7,plain,(
% 0.14/0.40    ? [X0] : (? [X1] : ((k1_xboole_0 != X1 & (v3_tops_1(X1,X0) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.14/0.40    inference(ennf_transformation,[],[f6])).
% 0.14/0.40  fof(f6,negated_conjecture,(
% 0.14/0.40    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 0.14/0.40    inference(negated_conjecture,[],[f5])).
% 0.14/0.40  fof(f5,conjecture,(
% 0.14/0.40    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 0.14/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).
% 0.14/0.40  fof(f51,plain,(
% 0.14/0.40    ~spl2_5),
% 0.14/0.40    inference(avatar_split_clause,[],[f19,f48])).
% 0.14/0.40  fof(f19,plain,(
% 0.14/0.40    k1_xboole_0 != sK1),
% 0.14/0.40    inference(cnf_transformation,[],[f8])).
% 0.14/0.40  fof(f46,plain,(
% 0.14/0.40    spl2_4),
% 0.14/0.40    inference(avatar_split_clause,[],[f18,f43])).
% 0.14/0.40  fof(f18,plain,(
% 0.14/0.40    v3_tops_1(sK1,sK0)),
% 0.14/0.40    inference(cnf_transformation,[],[f8])).
% 0.14/0.40  fof(f41,plain,(
% 0.14/0.40    spl2_3),
% 0.14/0.40    inference(avatar_split_clause,[],[f17,f38])).
% 0.14/0.40  fof(f17,plain,(
% 0.14/0.40    v3_pre_topc(sK1,sK0)),
% 0.14/0.40    inference(cnf_transformation,[],[f8])).
% 0.14/0.40  fof(f36,plain,(
% 0.14/0.40    spl2_2),
% 0.14/0.40    inference(avatar_split_clause,[],[f21,f33])).
% 0.14/0.40  fof(f21,plain,(
% 0.14/0.40    l1_pre_topc(sK0)),
% 0.14/0.40    inference(cnf_transformation,[],[f8])).
% 0.14/0.40  fof(f31,plain,(
% 0.14/0.40    spl2_1),
% 0.14/0.40    inference(avatar_split_clause,[],[f20,f28])).
% 0.14/0.40  fof(f20,plain,(
% 0.14/0.40    v2_pre_topc(sK0)),
% 0.14/0.40    inference(cnf_transformation,[],[f8])).
% 0.14/0.40  % SZS output end Proof for theBenchmark
% 0.14/0.40  % (3809)------------------------------
% 0.14/0.40  % (3809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.14/0.40  % (3809)Termination reason: Refutation
% 0.14/0.40  
% 0.14/0.40  % (3809)Memory used [KB]: 10618
% 0.14/0.40  % (3809)Time elapsed: 0.052 s
% 0.14/0.40  % (3809)------------------------------
% 0.14/0.40  % (3809)------------------------------
% 0.14/0.40  % (3805)Success in time 0.106 s
%------------------------------------------------------------------------------
