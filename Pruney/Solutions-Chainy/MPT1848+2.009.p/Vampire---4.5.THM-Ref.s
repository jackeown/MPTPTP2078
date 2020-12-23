%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 (  99 expanded)
%              Number of leaves         :   11 (  34 expanded)
%              Depth                    :   14
%              Number of atoms          :  204 ( 371 expanded)
%              Number of equality atoms :   25 (  72 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f92,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f73,f91])).

% (31362)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f91,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f88,f31])).

fof(f31,plain,(
    sQ3_eqProxy(u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(equality_proxy_replacement,[],[f20,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f20,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( v1_tex_2(sK1,sK0)
    & u1_struct_0(sK0) = u1_struct_0(sK1)
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f12,f11])).

fof(f11,plain,
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

fof(f12,plain,
    ( ? [X1] :
        ( v1_tex_2(X1,sK0)
        & u1_struct_0(X1) = u1_struct_0(sK0)
        & m1_pre_topc(X1,sK0) )
   => ( v1_tex_2(sK1,sK0)
      & u1_struct_0(sK0) = u1_struct_0(sK1)
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_tex_2(X1,X0)
          & u1_struct_0(X0) = u1_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_tex_2(X1,X0)
          & u1_struct_0(X0) = u1_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ~ ( v1_tex_2(X1,X0)
                & u1_struct_0(X0) = u1_struct_0(X1) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ~ ( v1_tex_2(X1,X0)
              & u1_struct_0(X0) = u1_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tex_2)).

fof(f88,plain,
    ( ~ sQ3_eqProxy(u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl4_1 ),
    inference(resolution,[],[f82,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(X1,X0)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f30])).

fof(f82,plain,
    ( ~ sQ3_eqProxy(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl4_1 ),
    inference(resolution,[],[f77,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f30])).

fof(f77,plain,
    ( ~ sQ3_eqProxy(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_1 ),
    inference(resolution,[],[f74,f32])).

fof(f32,plain,(
    ! [X0] : sQ3_eqProxy(k2_subset_1(X0),X0) ),
    inference(equality_proxy_replacement,[],[f23,f30])).

fof(f23,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f74,plain,
    ( ! [X0] :
        ( ~ sQ3_eqProxy(k2_subset_1(X0),u1_struct_0(sK1))
        | ~ sQ3_eqProxy(k1_zfmisc_1(X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_1 ),
    inference(resolution,[],[f55,f24])).

fof(f24,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f55,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,X2)
        | ~ sQ3_eqProxy(X3,u1_struct_0(sK1))
        | ~ sQ3_eqProxy(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl4_1
  <=> ! [X3,X2] :
        ( ~ sQ3_eqProxy(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ sQ3_eqProxy(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X3,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f73,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f68,f31])).

fof(f68,plain,
    ( ~ sQ3_eqProxy(u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl4_2 ),
    inference(resolution,[],[f64,f32])).

fof(f64,plain,
    ( ! [X2] :
        ( ~ sQ3_eqProxy(k2_subset_1(X2),u1_struct_0(sK1))
        | ~ sQ3_eqProxy(u1_struct_0(sK0),X2) )
    | ~ spl4_2 ),
    inference(resolution,[],[f60,f44])).

fof(f60,plain,
    ( ! [X0] :
        ( ~ sQ3_eqProxy(u1_struct_0(sK1),k2_subset_1(X0))
        | ~ sQ3_eqProxy(u1_struct_0(sK0),X0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f58,f22])).

fof(f22,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

fof(f58,plain,
    ( ! [X0,X1] :
        ( v1_subset_1(X1,X0)
        | ~ sQ3_eqProxy(u1_struct_0(sK1),X1)
        | ~ sQ3_eqProxy(u1_struct_0(sK0),X0) )
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl4_2
  <=> ! [X1,X0] :
        ( ~ sQ3_eqProxy(u1_struct_0(sK0),X0)
        | ~ sQ3_eqProxy(u1_struct_0(sK1),X1)
        | v1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f59,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f52,f57,f54])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sQ3_eqProxy(u1_struct_0(sK0),X0)
      | ~ sQ3_eqProxy(u1_struct_0(sK1),X1)
      | v1_subset_1(X1,X0)
      | ~ sQ3_eqProxy(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,X2)
      | ~ sQ3_eqProxy(X3,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f50,f19])).

fof(f19,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_pre_topc(sK1,sK0)
      | ~ sQ3_eqProxy(u1_struct_0(sK0),X0)
      | ~ sQ3_eqProxy(u1_struct_0(sK1),X1)
      | v1_subset_1(X1,X0)
      | ~ sQ3_eqProxy(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,X2)
      | ~ sQ3_eqProxy(X3,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f48,f21])).

fof(f21,plain,(
    v1_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_tex_2(X0,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ sQ3_eqProxy(u1_struct_0(sK0),X1)
      | ~ sQ3_eqProxy(u1_struct_0(X0),X2)
      | v1_subset_1(X2,X1)
      | ~ sQ3_eqProxy(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,X3)
      | ~ sQ3_eqProxy(X4,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f47,f18])).

fof(f18,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ v1_tex_2(X0,X1)
      | ~ sQ3_eqProxy(u1_struct_0(X1),X2)
      | ~ sQ3_eqProxy(u1_struct_0(X0),X3)
      | v1_subset_1(X3,X2)
      | ~ sQ3_eqProxy(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X5,X4)
      | ~ sQ3_eqProxy(X5,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f46,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X1,X3)
      | ~ sQ3_eqProxy(X2,X3)
      | ~ m1_subset_1(X0,X2)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f30])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v1_tex_2(X0,X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ sQ3_eqProxy(u1_struct_0(X1),X2)
      | ~ sQ3_eqProxy(u1_struct_0(X0),X3)
      | v1_subset_1(X3,X2) ) ),
    inference(resolution,[],[f29,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_subset_1(X0,X2)
      | ~ sQ3_eqProxy(X2,X3)
      | ~ sQ3_eqProxy(X0,X1)
      | v1_subset_1(X1,X3) ) ),
    inference(equality_proxy_axiom,[],[f30])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK2(X0,X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:48:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (31355)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.46  % (31357)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.46  % (31355)Refutation not found, incomplete strategy% (31355)------------------------------
% 0.20/0.46  % (31355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (31357)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f59,f73,f91])).
% 0.20/0.47  % (31362)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    ~spl4_1),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f90])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    $false | ~spl4_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f88,f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    sQ3_eqProxy(u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.47    inference(equality_proxy_replacement,[],[f20,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ! [X1,X0] : (sQ3_eqProxy(X0,X1) <=> X0 = X1)),
% 0.20/0.47    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    (v1_tex_2(sK1,sK0) & u1_struct_0(sK0) = u1_struct_0(sK1) & m1_pre_topc(sK1,sK0)) & l1_pre_topc(sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f12,f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (v1_tex_2(X1,sK0) & u1_struct_0(X1) = u1_struct_0(sK0) & m1_pre_topc(X1,sK0)) & l1_pre_topc(sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ? [X1] : (v1_tex_2(X1,sK0) & u1_struct_0(X1) = u1_struct_0(sK0) & m1_pre_topc(X1,sK0)) => (v1_tex_2(sK1,sK0) & u1_struct_0(sK0) = u1_struct_0(sK1) & m1_pre_topc(sK1,sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f7])).
% 0.20/0.47  fof(f7,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : ((v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,negated_conjecture,(
% 0.20/0.47    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ~(v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1))))),
% 0.20/0.47    inference(negated_conjecture,[],[f5])).
% 0.20/0.47  fof(f5,conjecture,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ~(v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tex_2)).
% 0.20/0.47  fof(f88,plain,(
% 0.20/0.47    ~sQ3_eqProxy(u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl4_1),
% 0.20/0.47    inference(resolution,[],[f82,f44])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ( ! [X0,X1] : (sQ3_eqProxy(X1,X0) | ~sQ3_eqProxy(X0,X1)) )),
% 0.20/0.47    inference(equality_proxy_axiom,[],[f30])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    ~sQ3_eqProxy(u1_struct_0(sK1),u1_struct_0(sK0)) | ~spl4_1),
% 0.20/0.47    inference(resolution,[],[f77,f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X0,X1] : (sQ3_eqProxy(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~sQ3_eqProxy(X0,X1)) )),
% 0.20/0.47    inference(equality_proxy_axiom,[],[f30])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    ~sQ3_eqProxy(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_1),
% 0.20/0.47    inference(resolution,[],[f74,f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X0] : (sQ3_eqProxy(k2_subset_1(X0),X0)) )),
% 0.20/0.47    inference(equality_proxy_replacement,[],[f23,f30])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    ( ! [X0] : (~sQ3_eqProxy(k2_subset_1(X0),u1_struct_0(sK1)) | ~sQ3_eqProxy(k1_zfmisc_1(X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_1),
% 0.20/0.47    inference(resolution,[],[f55,f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    ( ! [X2,X3] : (~m1_subset_1(X3,X2) | ~sQ3_eqProxy(X3,u1_struct_0(sK1)) | ~sQ3_eqProxy(X2,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f54])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    spl4_1 <=> ! [X3,X2] : (~sQ3_eqProxy(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~sQ3_eqProxy(X3,u1_struct_0(sK1)) | ~m1_subset_1(X3,X2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    ~spl4_2),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f72])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    $false | ~spl4_2),
% 0.20/0.47    inference(subsumption_resolution,[],[f68,f31])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    ~sQ3_eqProxy(u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl4_2),
% 0.20/0.47    inference(resolution,[],[f64,f32])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    ( ! [X2] : (~sQ3_eqProxy(k2_subset_1(X2),u1_struct_0(sK1)) | ~sQ3_eqProxy(u1_struct_0(sK0),X2)) ) | ~spl4_2),
% 0.20/0.47    inference(resolution,[],[f60,f44])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    ( ! [X0] : (~sQ3_eqProxy(u1_struct_0(sK1),k2_subset_1(X0)) | ~sQ3_eqProxy(u1_struct_0(sK0),X0)) ) | ~spl4_2),
% 0.20/0.47    inference(resolution,[],[f58,f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_subset_1(X1,X0) | ~sQ3_eqProxy(u1_struct_0(sK1),X1) | ~sQ3_eqProxy(u1_struct_0(sK0),X0)) ) | ~spl4_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f57])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    spl4_2 <=> ! [X1,X0] : (~sQ3_eqProxy(u1_struct_0(sK0),X0) | ~sQ3_eqProxy(u1_struct_0(sK1),X1) | v1_subset_1(X1,X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    spl4_1 | spl4_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f52,f57,f54])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~sQ3_eqProxy(u1_struct_0(sK0),X0) | ~sQ3_eqProxy(u1_struct_0(sK1),X1) | v1_subset_1(X1,X0) | ~sQ3_eqProxy(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X3,X2) | ~sQ3_eqProxy(X3,u1_struct_0(sK1))) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f50,f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    m1_pre_topc(sK1,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~m1_pre_topc(sK1,sK0) | ~sQ3_eqProxy(u1_struct_0(sK0),X0) | ~sQ3_eqProxy(u1_struct_0(sK1),X1) | v1_subset_1(X1,X0) | ~sQ3_eqProxy(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X3,X2) | ~sQ3_eqProxy(X3,u1_struct_0(sK1))) )),
% 0.20/0.47    inference(resolution,[],[f48,f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    v1_tex_2(sK1,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X3,X1] : (~v1_tex_2(X0,sK0) | ~m1_pre_topc(X0,sK0) | ~sQ3_eqProxy(u1_struct_0(sK0),X1) | ~sQ3_eqProxy(u1_struct_0(X0),X2) | v1_subset_1(X2,X1) | ~sQ3_eqProxy(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X4,X3) | ~sQ3_eqProxy(X4,u1_struct_0(X0))) )),
% 0.20/0.47    inference(resolution,[],[f47,f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    l1_pre_topc(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1) | ~v1_tex_2(X0,X1) | ~sQ3_eqProxy(u1_struct_0(X1),X2) | ~sQ3_eqProxy(u1_struct_0(X0),X3) | v1_subset_1(X3,X2) | ~sQ3_eqProxy(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X5,X4) | ~sQ3_eqProxy(X5,u1_struct_0(X0))) )),
% 0.20/0.47    inference(resolution,[],[f46,f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (m1_subset_1(X1,X3) | ~sQ3_eqProxy(X2,X3) | ~m1_subset_1(X0,X2) | ~sQ3_eqProxy(X0,X1)) )),
% 0.20/0.47    inference(equality_proxy_axiom,[],[f30])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) | ~v1_tex_2(X0,X1) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~sQ3_eqProxy(u1_struct_0(X1),X2) | ~sQ3_eqProxy(u1_struct_0(X0),X3) | v1_subset_1(X3,X2)) )),
% 0.20/0.47    inference(resolution,[],[f29,f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~v1_subset_1(X0,X2) | ~sQ3_eqProxy(X2,X3) | ~sQ3_eqProxy(X0,X1) | v1_subset_1(X1,X3)) )),
% 0.20/0.47    inference(equality_proxy_axiom,[],[f30])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.47    inference(equality_resolution,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ( ! [X0,X3,X1] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(rectify,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (31357)------------------------------
% 0.20/0.47  % (31357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (31357)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (31357)Memory used [KB]: 6140
% 0.20/0.47  % (31357)Time elapsed: 0.054 s
% 0.20/0.47  % (31357)------------------------------
% 0.20/0.47  % (31357)------------------------------
% 0.20/0.47  % (31362)Refutation not found, incomplete strategy% (31362)------------------------------
% 0.20/0.47  % (31362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (31362)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (31362)Memory used [KB]: 6140
% 0.20/0.47  % (31362)Time elapsed: 0.053 s
% 0.20/0.47  % (31362)------------------------------
% 0.20/0.47  % (31362)------------------------------
% 0.20/0.47  % (31351)Success in time 0.112 s
%------------------------------------------------------------------------------
