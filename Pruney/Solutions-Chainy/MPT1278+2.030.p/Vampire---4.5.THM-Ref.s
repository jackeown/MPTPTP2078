%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 123 expanded)
%              Number of leaves         :   17 (  56 expanded)
%              Depth                    :    7
%              Number of atoms          :  225 ( 537 expanded)
%              Number of equality atoms :   30 (  80 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f96,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f35,f39,f43,f47,f51,f65,f71,f73,f80,f90,f95])).

fof(f95,plain,
    ( ~ spl2_5
    | ~ spl2_4
    | ~ spl2_2
    | spl2_13 ),
    inference(avatar_split_clause,[],[f92,f86,f33,f41,f45])).

fof(f45,plain,
    ( spl2_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f41,plain,
    ( spl2_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f33,plain,
    ( spl2_2
  <=> v3_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f86,plain,
    ( spl2_13
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f92,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_13 ),
    inference(resolution,[],[f87,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).

fof(f87,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl2_13 ),
    inference(avatar_component_clause,[],[f86])).

fof(f90,plain,
    ( ~ spl2_5
    | ~ spl2_4
    | ~ spl2_13
    | spl2_1
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f82,f78,f29,f86,f41,f45])).

fof(f29,plain,
    ( spl2_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f78,plain,
    ( spl2_12
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f82,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_12 ),
    inference(superposition,[],[f24,f79])).

fof(f79,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f78])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_xboole_0
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_tops_1(X0,X1) != k1_xboole_0 )
            & ( k1_tops_1(X0,X1) = k1_xboole_0
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_tops_1(X0,X1) = k1_xboole_0 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_tops_1(X0,X1) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f80,plain,
    ( ~ spl2_3
    | spl2_12
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f75,f63,f45,f41,f78,f37])).

fof(f37,plain,
    ( spl2_3
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f63,plain,
    ( spl2_10
  <=> ! [X1,X3] :
        ( k1_tops_1(X1,X3) = X3
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v3_pre_topc(X3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f75,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_10 ),
    inference(resolution,[],[f74,f42])).

fof(f42,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f74,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = X0
        | ~ v3_pre_topc(X0,sK0) )
    | ~ spl2_5
    | ~ spl2_10 ),
    inference(resolution,[],[f64,f46])).

fof(f46,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f64,plain,
    ( ! [X3,X1] :
        ( ~ l1_pre_topc(X1)
        | k1_tops_1(X1,X3) = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v3_pre_topc(X3,X1) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f63])).

fof(f73,plain,
    ( ~ spl2_4
    | ~ spl2_11 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | ~ spl2_4
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f42,f69])).

fof(f69,plain,
    ( ! [X0] : ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl2_11
  <=> ! [X0] : ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f71,plain,
    ( spl2_11
    | ~ spl2_6
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f66,f60,f45,f49,f68])).

fof(f49,plain,
    ( spl2_6
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f60,plain,
    ( spl2_9
  <=> ! [X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f66,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(resolution,[],[f61,f46])).

fof(f61,plain,
    ( ! [X2,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f60])).

fof(f65,plain,
    ( spl2_9
    | spl2_10 ),
    inference(avatar_split_clause,[],[f26,f63,f60])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f51,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f17,f49])).

fof(f17,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_xboole_0 != sK1
    & v3_tops_1(sK1,sK0)
    & v3_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 != X1
            & v3_tops_1(X1,X0)
            & v3_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,sK0)
          & v3_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X1] :
        ( k1_xboole_0 != X1
        & v3_tops_1(X1,sK0)
        & v3_pre_topc(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k1_xboole_0 != sK1
      & v3_tops_1(sK1,sK0)
      & v3_pre_topc(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v3_tops_1(X1,X0)
                & v3_pre_topc(X1,X0) )
             => k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tops_1(X1,X0)
              & v3_pre_topc(X1,X0) )
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).

fof(f47,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f18,f45])).

fof(f18,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f19,f41])).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f39,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f20,f37])).

fof(f20,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f21,f33])).

fof(f21,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f31,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f22,f29])).

fof(f22,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:08:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.48  % (7178)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (7187)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (7178)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (7174)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (7186)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (7175)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (7173)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (7184)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (7184)Refutation not found, incomplete strategy% (7184)------------------------------
% 0.21/0.49  % (7184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7184)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7184)Memory used [KB]: 6012
% 0.21/0.49  % (7184)Time elapsed: 0.001 s
% 0.21/0.49  % (7184)------------------------------
% 0.21/0.49  % (7184)------------------------------
% 0.21/0.49  % (7177)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f31,f35,f39,f43,f47,f51,f65,f71,f73,f80,f90,f95])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ~spl2_5 | ~spl2_4 | ~spl2_2 | spl2_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f92,f86,f33,f41,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    spl2_5 <=> l1_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    spl2_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    spl2_2 <=> v3_tops_1(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    spl2_13 <=> v2_tops_1(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    ~v3_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_13),
% 0.21/0.49    inference(resolution,[],[f87,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    ~v2_tops_1(sK1,sK0) | spl2_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f86])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ~spl2_5 | ~spl2_4 | ~spl2_13 | spl2_1 | ~spl2_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f82,f78,f29,f86,f41,f45])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    spl2_1 <=> k1_xboole_0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    spl2_12 <=> sK1 = k1_tops_1(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | ~v2_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_12),
% 0.21/0.49    inference(superposition,[],[f24,f79])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    sK1 = k1_tops_1(sK0,sK1) | ~spl2_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f78])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_xboole_0 | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_tops_1(X0,X1) != k1_xboole_0) & (k1_tops_1(X0,X1) = k1_xboole_0 | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_tops_1(X0,X1) = k1_xboole_0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_tops_1(X0,X1) = k1_xboole_0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ~spl2_3 | spl2_12 | ~spl2_4 | ~spl2_5 | ~spl2_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f75,f63,f45,f41,f78,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    spl2_3 <=> v3_pre_topc(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    spl2_10 <=> ! [X1,X3] : (k1_tops_1(X1,X3) = X3 | ~l1_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | (~spl2_4 | ~spl2_5 | ~spl2_10)),
% 0.21/0.49    inference(resolution,[],[f74,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f41])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = X0 | ~v3_pre_topc(X0,sK0)) ) | (~spl2_5 | ~spl2_10)),
% 0.21/0.49    inference(resolution,[],[f64,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    l1_pre_topc(sK0) | ~spl2_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f45])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X3,X1] : (~l1_pre_topc(X1) | k1_tops_1(X1,X3) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1)) ) | ~spl2_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f63])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ~spl2_4 | ~spl2_11),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    $false | (~spl2_4 | ~spl2_11)),
% 0.21/0.49    inference(subsumption_resolution,[],[f42,f69])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    spl2_11 <=> ! [X0] : ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    spl2_11 | ~spl2_6 | ~spl2_5 | ~spl2_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f66,f60,f45,f49,f68])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    spl2_6 <=> v2_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    spl2_9 <=> ! [X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl2_5 | ~spl2_9)),
% 0.21/0.49    inference(resolution,[],[f61,f46])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) ) | ~spl2_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f60])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    spl2_9 | spl2_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f26,f63,f60])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    spl2_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f17,f49])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    v2_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    (k1_xboole_0 != sK1 & v3_tops_1(sK1,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f14,f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,sK0) & v3_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,sK0) & v3_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (k1_xboole_0 != sK1 & v3_tops_1(sK1,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f6])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((k1_xboole_0 != X1 & (v3_tops_1(X1,X0) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 0.21/0.49    inference(negated_conjecture,[],[f4])).
% 0.21/0.49  fof(f4,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    spl2_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f18,f45])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    spl2_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f19,f41])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    spl2_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f20,f37])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    v3_pre_topc(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    spl2_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f21,f33])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    v3_tops_1(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ~spl2_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f22,f29])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    k1_xboole_0 != sK1),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (7178)------------------------------
% 0.21/0.49  % (7178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7178)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (7178)Memory used [KB]: 10618
% 0.21/0.49  % (7178)Time elapsed: 0.072 s
% 0.21/0.49  % (7178)------------------------------
% 0.21/0.49  % (7178)------------------------------
% 0.21/0.50  % (7191)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (7171)Success in time 0.139 s
%------------------------------------------------------------------------------
