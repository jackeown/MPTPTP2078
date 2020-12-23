%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 172 expanded)
%              Number of leaves         :    8 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :  211 (1240 expanded)
%              Number of equality atoms :   29 ( 182 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f79,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f38,f69,f78])).

fof(f78,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f76])).

fof(f76,plain,
    ( $false
    | ~ spl4_1
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f31,f74])).

fof(f74,plain,
    ( ~ v1_subset_1(sK2,u1_struct_0(sK0))
    | spl4_2 ),
    inference(backward_demodulation,[],[f72,f73])).

fof(f73,plain,
    ( sK2 = sK3(sK0,sK1)
    | spl4_2 ),
    inference(forward_demodulation,[],[f71,f21])).

fof(f21,plain,(
    u1_struct_0(sK1) = sK2 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( ~ v1_tex_2(sK1,sK0)
      | ~ v1_subset_1(sK2,u1_struct_0(sK0)) )
    & ( v1_tex_2(sK1,sK0)
      | v1_subset_1(sK2,u1_struct_0(sK0)) )
    & u1_struct_0(sK1) = sK2
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12,f11,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ v1_tex_2(X1,X0)
                  | ~ v1_subset_1(X2,u1_struct_0(X0)) )
                & ( v1_tex_2(X1,X0)
                  | v1_subset_1(X2,u1_struct_0(X0)) )
                & u1_struct_0(X1) = X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v1_tex_2(X1,sK0)
                | ~ v1_subset_1(X2,u1_struct_0(sK0)) )
              & ( v1_tex_2(X1,sK0)
                | v1_subset_1(X2,u1_struct_0(sK0)) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ v1_tex_2(X1,sK0)
              | ~ v1_subset_1(X2,u1_struct_0(sK0)) )
            & ( v1_tex_2(X1,sK0)
              | v1_subset_1(X2,u1_struct_0(sK0)) )
            & u1_struct_0(X1) = X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_pre_topc(X1,sK0) )
   => ( ? [X2] :
          ( ( ~ v1_tex_2(sK1,sK0)
            | ~ v1_subset_1(X2,u1_struct_0(sK0)) )
          & ( v1_tex_2(sK1,sK0)
            | v1_subset_1(X2,u1_struct_0(sK0)) )
          & u1_struct_0(sK1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X2] :
        ( ( ~ v1_tex_2(sK1,sK0)
          | ~ v1_subset_1(X2,u1_struct_0(sK0)) )
        & ( v1_tex_2(sK1,sK0)
          | v1_subset_1(X2,u1_struct_0(sK0)) )
        & u1_struct_0(sK1) = X2
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ v1_tex_2(sK1,sK0)
        | ~ v1_subset_1(sK2,u1_struct_0(sK0)) )
      & ( v1_tex_2(sK1,sK0)
        | v1_subset_1(sK2,u1_struct_0(sK0)) )
      & u1_struct_0(sK1) = sK2
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v1_tex_2(X1,X0)
                | ~ v1_subset_1(X2,u1_struct_0(X0)) )
              & ( v1_tex_2(X1,X0)
                | v1_subset_1(X2,u1_struct_0(X0)) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v1_tex_2(X1,X0)
                | ~ v1_subset_1(X2,u1_struct_0(X0)) )
              & ( v1_tex_2(X1,X0)
                | v1_subset_1(X2,u1_struct_0(X0)) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <~> v1_tex_2(X1,X0) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <~> v1_tex_2(X1,X0) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => ( v1_subset_1(X2,u1_struct_0(X0))
                  <=> v1_tex_2(X1,X0) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v1_subset_1(X2,u1_struct_0(X0))
                <=> v1_tex_2(X1,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tex_2)).

fof(f71,plain,
    ( u1_struct_0(sK1) = sK3(sK0,sK1)
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f18,f19,f36,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK3(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK3(X0,X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK3(X0,X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
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
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

fof(f36,plain,
    ( ~ v1_tex_2(sK1,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl4_2
  <=> v1_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f19,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f18,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f72,plain,
    ( ~ v1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f18,f19,f36,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f31,plain,
    ( v1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl4_1
  <=> v1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f69,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | spl4_1
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f18,f19,f35,f32,f20,f40])).

fof(f40,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X1)))
      | v1_subset_1(sK2,u1_struct_0(X1))
      | ~ v1_tex_2(sK1,X1)
      | ~ m1_pre_topc(sK1,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(superposition,[],[f28,f21])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f32,plain,
    ( ~ v1_subset_1(sK2,u1_struct_0(sK0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f35,plain,
    ( v1_tex_2(sK1,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f38,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f22,f34,f30])).

fof(f22,plain,
    ( v1_tex_2(sK1,sK0)
    | v1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f37,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f23,f34,f30])).

fof(f23,plain,
    ( ~ v1_tex_2(sK1,sK0)
    | ~ v1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:22:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (30618)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.46  % (30623)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.46  % (30637)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.46  % (30629)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.46  % (30629)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f79,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f37,f38,f69,f78])).
% 0.20/0.46  fof(f78,plain,(
% 0.20/0.46    ~spl4_1 | spl4_2),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f76])).
% 0.20/0.46  fof(f76,plain,(
% 0.20/0.46    $false | (~spl4_1 | spl4_2)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f31,f74])).
% 0.20/0.46  fof(f74,plain,(
% 0.20/0.46    ~v1_subset_1(sK2,u1_struct_0(sK0)) | spl4_2),
% 0.20/0.46    inference(backward_demodulation,[],[f72,f73])).
% 0.20/0.46  fof(f73,plain,(
% 0.20/0.46    sK2 = sK3(sK0,sK1) | spl4_2),
% 0.20/0.46    inference(forward_demodulation,[],[f71,f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    u1_struct_0(sK1) = sK2),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    (((~v1_tex_2(sK1,sK0) | ~v1_subset_1(sK2,u1_struct_0(sK0))) & (v1_tex_2(sK1,sK0) | v1_subset_1(sK2,u1_struct_0(sK0))) & u1_struct_0(sK1) = sK2 & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_pre_topc(sK1,sK0)) & l1_pre_topc(sK0)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12,f11,f10])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : ((~v1_tex_2(X1,X0) | ~v1_subset_1(X2,u1_struct_0(X0))) & (v1_tex_2(X1,X0) | v1_subset_1(X2,u1_struct_0(X0))) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : ((~v1_tex_2(X1,sK0) | ~v1_subset_1(X2,u1_struct_0(sK0))) & (v1_tex_2(X1,sK0) | v1_subset_1(X2,u1_struct_0(sK0))) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_pre_topc(X1,sK0)) & l1_pre_topc(sK0))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ? [X1] : (? [X2] : ((~v1_tex_2(X1,sK0) | ~v1_subset_1(X2,u1_struct_0(sK0))) & (v1_tex_2(X1,sK0) | v1_subset_1(X2,u1_struct_0(sK0))) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_pre_topc(X1,sK0)) => (? [X2] : ((~v1_tex_2(sK1,sK0) | ~v1_subset_1(X2,u1_struct_0(sK0))) & (v1_tex_2(sK1,sK0) | v1_subset_1(X2,u1_struct_0(sK0))) & u1_struct_0(sK1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_pre_topc(sK1,sK0))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ? [X2] : ((~v1_tex_2(sK1,sK0) | ~v1_subset_1(X2,u1_struct_0(sK0))) & (v1_tex_2(sK1,sK0) | v1_subset_1(X2,u1_struct_0(sK0))) & u1_struct_0(sK1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~v1_tex_2(sK1,sK0) | ~v1_subset_1(sK2,u1_struct_0(sK0))) & (v1_tex_2(sK1,sK0) | v1_subset_1(sK2,u1_struct_0(sK0))) & u1_struct_0(sK1) = sK2 & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : ((~v1_tex_2(X1,X0) | ~v1_subset_1(X2,u1_struct_0(X0))) & (v1_tex_2(X1,X0) | v1_subset_1(X2,u1_struct_0(X0))) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.20/0.46    inference(flattening,[],[f8])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : (((~v1_tex_2(X1,X0) | ~v1_subset_1(X2,u1_struct_0(X0))) & (v1_tex_2(X1,X0) | v1_subset_1(X2,u1_struct_0(X0)))) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.20/0.46    inference(nnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) <~> v1_tex_2(X1,X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.20/0.46    inference(flattening,[],[f4])).
% 0.20/0.46  fof(f4,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : (((v1_subset_1(X2,u1_struct_0(X0)) <~> v1_tex_2(X1,X0)) & u1_struct_0(X1) = X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,negated_conjecture,(
% 0.20/0.46    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v1_subset_1(X2,u1_struct_0(X0)) <=> v1_tex_2(X1,X0))))))),
% 0.20/0.46    inference(negated_conjecture,[],[f2])).
% 0.20/0.46  fof(f2,conjecture,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v1_subset_1(X2,u1_struct_0(X0)) <=> v1_tex_2(X1,X0))))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tex_2)).
% 0.20/0.46  fof(f71,plain,(
% 0.20/0.46    u1_struct_0(sK1) = sK3(sK0,sK1) | spl4_2),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f18,f19,f36,f26])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK3(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(rectify,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(nnf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(flattening,[],[f6])).
% 0.20/0.46  fof(f6,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    ~v1_tex_2(sK1,sK0) | spl4_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f34])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    spl4_2 <=> v1_tex_2(sK1,sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    m1_pre_topc(sK1,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    l1_pre_topc(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f72,plain,(
% 0.20/0.46    ~v1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | spl4_2),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f18,f19,f36,f27])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    v1_subset_1(sK2,u1_struct_0(sK0)) | ~spl4_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    spl4_1 <=> v1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.46  fof(f69,plain,(
% 0.20/0.46    spl4_1 | ~spl4_2),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f67])).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    $false | (spl4_1 | ~spl4_2)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f18,f19,f35,f32,f20,f40])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    ( ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X1))) | v1_subset_1(sK2,u1_struct_0(X1)) | ~v1_tex_2(sK1,X1) | ~m1_pre_topc(sK1,X1) | ~l1_pre_topc(X1)) )),
% 0.20/0.46    inference(superposition,[],[f28,f21])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.46    inference(equality_resolution,[],[f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ( ! [X0,X3,X1] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ~v1_subset_1(sK2,u1_struct_0(sK0)) | spl4_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f30])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    v1_tex_2(sK1,sK0) | ~spl4_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f34])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    spl4_1 | spl4_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f22,f34,f30])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    v1_tex_2(sK1,sK0) | v1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    ~spl4_1 | ~spl4_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f23,f34,f30])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ~v1_tex_2(sK1,sK0) | ~v1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (30629)------------------------------
% 0.20/0.46  % (30629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (30629)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (30629)Memory used [KB]: 10618
% 0.20/0.46  % (30629)Time elapsed: 0.056 s
% 0.20/0.46  % (30629)------------------------------
% 0.20/0.46  % (30629)------------------------------
% 0.20/0.47  % (30617)Success in time 0.111 s
%------------------------------------------------------------------------------
