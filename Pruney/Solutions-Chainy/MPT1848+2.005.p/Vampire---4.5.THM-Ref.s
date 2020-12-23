%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 108 expanded)
%              Number of leaves         :   16 (  44 expanded)
%              Depth                    :   15
%              Number of atoms          :  211 ( 361 expanded)
%              Number of equality atoms :   31 (  67 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f106,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f43,f47,f51,f71,f82,f85,f105])).

fof(f105,plain,
    ( ~ spl3_3
    | spl3_11
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f102,f69,f49,f41,f37,f80,f45])).

fof(f45,plain,
    ( spl3_3
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f80,plain,
    ( spl3_11
  <=> v1_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f37,plain,
    ( spl3_1
  <=> v1_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f41,plain,
    ( spl3_2
  <=> u1_struct_0(sK0) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f49,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f69,plain,
    ( spl3_8
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f102,plain,
    ( v1_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f101,f70])).

fof(f70,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f69])).

fof(f101,plain,
    ( v1_subset_1(u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f100,f42])).

fof(f42,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f100,plain,
    ( v1_subset_1(u1_struct_0(sK1),k2_struct_0(sK0))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(resolution,[],[f99,f38])).

fof(f38,plain,
    ( v1_tex_2(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f99,plain,
    ( ! [X0] :
        ( ~ v1_tex_2(X0,sK0)
        | v1_subset_1(u1_struct_0(X0),k2_struct_0(sK0))
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f98,f70])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ v1_tex_2(X0,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | v1_subset_1(u1_struct_0(X0),u1_struct_0(sK0)) )
    | ~ spl3_4 ),
    inference(resolution,[],[f52,f50])).

fof(f50,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(global_subsumption,[],[f30,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK2(X0,X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK2(X0,X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v1_subset_1(X2,u1_struct_0(X0))
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f85,plain,
    ( ~ spl3_4
    | spl3_10 ),
    inference(avatar_split_clause,[],[f83,f77,f49])).

fof(f77,plain,
    ( spl3_10
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f83,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_10 ),
    inference(resolution,[],[f78,f29])).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f78,plain,
    ( ~ l1_struct_0(sK0)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f77])).

fof(f82,plain,
    ( ~ spl3_10
    | ~ spl3_11
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f75,f69,f80,f77])).

fof(f75,plain,
    ( ~ v1_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | ~ spl3_8 ),
    inference(superposition,[],[f27,f70])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).

fof(f71,plain,
    ( spl3_8
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f67,f49,f69])).

fof(f67,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f66,f50])).

fof(f66,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f28,f29])).

fof(f28,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f51,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f23,f49])).

fof(f23,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( v1_tex_2(sK1,sK0)
    & u1_struct_0(sK0) = u1_struct_0(sK1)
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_tex_2(X1,X0)
            & u1_struct_0(X0) = u1_struct_0(X1)
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( v1_tex_2(X1,sK0)
          & u1_struct_0(X1) = u1_struct_0(sK0)
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( v1_tex_2(X1,sK0)
        & u1_struct_0(X1) = u1_struct_0(sK0)
        & m1_pre_topc(X1,sK0) )
   => ( v1_tex_2(sK1,sK0)
      & u1_struct_0(sK0) = u1_struct_0(sK1)
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_tex_2(X1,X0)
          & u1_struct_0(X0) = u1_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_tex_2(X1,X0)
          & u1_struct_0(X0) = u1_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ~ ( v1_tex_2(X1,X0)
                & u1_struct_0(X0) = u1_struct_0(X1) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ~ ( v1_tex_2(X1,X0)
              & u1_struct_0(X0) = u1_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tex_2)).

fof(f47,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f24,f45])).

fof(f24,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f25,f41])).

fof(f25,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f26,f37])).

fof(f26,plain,(
    v1_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:28:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (17435)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (17444)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (17434)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (17443)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  % (17435)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (17442)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f39,f43,f47,f51,f71,f82,f85,f105])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    ~spl3_3 | spl3_11 | ~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f102,f69,f49,f41,f37,f80,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    spl3_3 <=> m1_pre_topc(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    spl3_11 <=> v1_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    spl3_1 <=> v1_tex_2(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    spl3_2 <=> u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    spl3_4 <=> l1_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    spl3_8 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    v1_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_pre_topc(sK1,sK0) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_8)),
% 0.21/0.52    inference(forward_demodulation,[],[f101,f70])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f69])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    v1_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) | ~m1_pre_topc(sK1,sK0) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_8)),
% 0.21/0.52    inference(forward_demodulation,[],[f100,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    u1_struct_0(sK0) = u1_struct_0(sK1) | ~spl3_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f41])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    v1_subset_1(u1_struct_0(sK1),k2_struct_0(sK0)) | ~m1_pre_topc(sK1,sK0) | (~spl3_1 | ~spl3_4 | ~spl3_8)),
% 0.21/0.52    inference(resolution,[],[f99,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    v1_tex_2(sK1,sK0) | ~spl3_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f37])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_tex_2(X0,sK0) | v1_subset_1(u1_struct_0(X0),k2_struct_0(sK0)) | ~m1_pre_topc(X0,sK0)) ) | (~spl3_4 | ~spl3_8)),
% 0.21/0.52    inference(forward_demodulation,[],[f98,f70])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_tex_2(X0,sK0) | ~m1_pre_topc(X0,sK0) | v1_subset_1(u1_struct_0(X0),u1_struct_0(sK0))) ) | ~spl3_4),
% 0.21/0.52    inference(resolution,[],[f52,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    l1_pre_topc(sK0) | ~spl3_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f49])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))) )),
% 0.21/0.52    inference(global_subsumption,[],[f30,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(rectify,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    ~spl3_4 | spl3_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f83,f77,f49])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    spl3_10 <=> l1_struct_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | spl3_10),
% 0.21/0.52    inference(resolution,[],[f78,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ~l1_struct_0(sK0) | spl3_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f77])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    ~spl3_10 | ~spl3_11 | ~spl3_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f75,f69,f80,f77])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ~v1_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) | ~l1_struct_0(sK0) | ~spl3_8),
% 0.21/0.52    inference(superposition,[],[f27,f70])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) => ~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    spl3_8 | ~spl3_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f67,f49,f69])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_4),
% 0.21/0.52    inference(resolution,[],[f66,f50])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.52    inference(resolution,[],[f28,f29])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    spl3_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f23,f49])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    l1_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    (v1_tex_2(sK1,sK0) & u1_struct_0(sK0) = u1_struct_0(sK1) & m1_pre_topc(sK1,sK0)) & l1_pre_topc(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f17,f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (v1_tex_2(X1,sK0) & u1_struct_0(X1) = u1_struct_0(sK0) & m1_pre_topc(X1,sK0)) & l1_pre_topc(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X1] : (v1_tex_2(X1,sK0) & u1_struct_0(X1) = u1_struct_0(sK0) & m1_pre_topc(X1,sK0)) => (v1_tex_2(sK1,sK0) & u1_struct_0(sK0) = u1_struct_0(sK1) & m1_pre_topc(sK1,sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ~(v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1))))),
% 0.21/0.52    inference(negated_conjecture,[],[f6])).
% 0.21/0.52  fof(f6,conjecture,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ~(v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tex_2)).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    spl3_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f24,f45])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    m1_pre_topc(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f25,f41])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    spl3_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f26,f37])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    v1_tex_2(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (17435)------------------------------
% 0.21/0.52  % (17435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (17435)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (17435)Memory used [KB]: 10618
% 0.21/0.52  % (17435)Time elapsed: 0.073 s
% 0.21/0.52  % (17435)------------------------------
% 0.21/0.52  % (17435)------------------------------
% 0.21/0.53  % (17428)Success in time 0.161 s
%------------------------------------------------------------------------------
