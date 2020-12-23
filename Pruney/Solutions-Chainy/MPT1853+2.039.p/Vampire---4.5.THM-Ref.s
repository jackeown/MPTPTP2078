%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:47 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 515 expanded)
%              Number of leaves         :   27 ( 144 expanded)
%              Depth                    :   21
%              Number of atoms          :  584 (2737 expanded)
%              Number of equality atoms :   50 (  75 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f339,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f97,f109,f130,f191,f239,f244,f253,f271,f326])).

fof(f326,plain,
    ( spl3_1
    | spl3_4 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | spl3_1
    | spl3_4 ),
    inference(subsumption_resolution,[],[f324,f121])).

fof(f121,plain,(
    v7_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f120,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f47,f49,f48])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
              | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
            & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
              | v1_tex_2(k1_tex_2(X0,X1),X0) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
            | ~ v1_tex_2(k1_tex_2(sK0,X1),sK0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
            | v1_tex_2(k1_tex_2(sK0,X1),sK0) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X1] :
        ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
          | ~ v1_tex_2(k1_tex_2(sK0,X1),sK0) )
        & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
          | v1_tex_2(k1_tex_2(sK0,X1),sK0) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
        | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
      & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
        | v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

fof(f120,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f119,f57])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f119,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f79,f58])).

fof(f58,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | v7_struct_0(k1_tex_2(X0,X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f324,plain,
    ( ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | spl3_1
    | spl3_4 ),
    inference(subsumption_resolution,[],[f323,f147])).

fof(f147,plain,(
    l1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f146,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f146,plain,(
    l1_pre_topc(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f145,f56])).

fof(f145,plain,
    ( v2_struct_0(sK0)
    | l1_pre_topc(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f144,f57])).

fof(f144,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | l1_pre_topc(k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f143,f58])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | l1_pre_topc(k1_tex_2(X1,X0)) ) ),
    inference(duplicate_literal_removal,[],[f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | l1_pre_topc(k1_tex_2(X1,X0))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f83,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f323,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | spl3_1
    | spl3_4 ),
    inference(subsumption_resolution,[],[f308,f108])).

fof(f108,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl3_4
  <=> v1_zfmisc_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f308,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | spl3_1 ),
    inference(superposition,[],[f75,f205])).

fof(f205,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | spl3_1 ),
    inference(forward_demodulation,[],[f204,f163])).

fof(f163,plain,
    ( u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f162,f56])).

fof(f162,plain,
    ( u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f161,f58])).

fof(f161,plain,
    ( u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f158,f57])).

fof(f158,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl3_1 ),
    inference(resolution,[],[f154,f91])).

fof(f91,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl3_1
  <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f154,plain,(
    ! [X0,X1] :
      ( v1_tex_2(k1_tex_2(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = sK2(X0,k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f153])).

fof(f153,plain,(
    ! [X0,X1] :
      ( v1_tex_2(k1_tex_2(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = sK2(X0,k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f152,f83])).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | v1_tex_2(X0,X1)
      | ~ l1_pre_topc(X1)
      | u1_struct_0(X1) = sK2(X1,X0) ) ),
    inference(subsumption_resolution,[],[f150,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f52,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK2(X0,X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
    inference(rectify,[],[f51])).

% (23058)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% (23079)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% (23087)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f51,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f150,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X0,X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | u1_struct_0(X1) = sK2(X1,X0)
      | v1_subset_1(sK2(X1,X0),u1_struct_0(X1)) ) ),
    inference(resolution,[],[f68,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f204,plain,
    ( sK2(sK0,k1_tex_2(sK0,sK1)) = u1_struct_0(k1_tex_2(sK0,sK1))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f203,f56])).

fof(f203,plain,
    ( sK2(sK0,k1_tex_2(sK0,sK1)) = u1_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f202,f58])).

fof(f202,plain,
    ( sK2(sK0,k1_tex_2(sK0,sK1)) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f199,f57])).

fof(f199,plain,
    ( sK2(sK0,k1_tex_2(sK0,sK1)) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl3_1 ),
    inference(resolution,[],[f149,f91])).

fof(f149,plain,(
    ! [X0,X1] :
      ( v1_tex_2(k1_tex_2(X0,X1),X0)
      | u1_struct_0(k1_tex_2(X0,X1)) = sK2(X0,k1_tex_2(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_tex_2(X0,X1)) = sK2(X0,k1_tex_2(X0,X1))
      | v1_tex_2(k1_tex_2(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f69,f83])).

% (23087)Refutation not found, incomplete strategy% (23087)------------------------------
% (23087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23087)Termination reason: Refutation not found, incomplete strategy

% (23087)Memory used [KB]: 1663
% (23087)Time elapsed: 0.001 s
% (23087)------------------------------
% (23087)------------------------------
fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | v1_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f75,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f271,plain,(
    ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f270])).

fof(f270,plain,
    ( $false
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f269,f118])).

fof(f118,plain,(
    ~ v2_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f117,f56])).

fof(f117,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f116,f57])).

fof(f116,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f78,f58])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f269,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f267,f147])).

fof(f267,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl3_13 ),
    inference(resolution,[],[f252,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f252,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl3_13
  <=> v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f253,plain,
    ( ~ spl3_4
    | spl3_13
    | spl3_3
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f248,f170,f89,f102,f250,f106])).

fof(f102,plain,
    ( spl3_3
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

% (23065)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
fof(f170,plain,
    ( spl3_6
  <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f248,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f247,f57])).

fof(f247,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f234,f171])).

fof(f171,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f170])).

fof(f234,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f90,f136])).

fof(f136,plain,(
    ! [X2,X3] :
      ( ~ v1_tex_2(X2,X3)
      | v1_xboole_0(u1_struct_0(X3))
      | v1_xboole_0(u1_struct_0(X2))
      | ~ v1_zfmisc_1(u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ l1_pre_topc(X3) ) ),
    inference(subsumption_resolution,[],[f132,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f132,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X3))
      | ~ v1_zfmisc_1(u1_struct_0(X3))
      | v1_xboole_0(u1_struct_0(X3))
      | v1_xboole_0(u1_struct_0(X2))
      | ~ v1_tex_2(X2,X3)
      | ~ m1_pre_topc(X2,X3)
      | ~ l1_pre_topc(X3) ) ),
    inference(extensionality_resolution,[],[f63,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) != u1_struct_0(X1)
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_tex_2(X1,X0)
          | u1_struct_0(X0) != u1_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_tex_2(X1,X0)
          | u1_struct_0(X0) != u1_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ~ ( v1_tex_2(X1,X0)
              & u1_struct_0(X0) = u1_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tex_2)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f90,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f244,plain,(
    ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f243])).

fof(f243,plain,
    ( $false
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f242,f56])).

fof(f242,plain,
    ( v2_struct_0(sK0)
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f240,f98])).

fof(f98,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f64,f57])).

fof(f240,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f104,f73])).

fof(f104,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f102])).

fof(f239,plain,
    ( spl3_2
    | spl3_4
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | spl3_2
    | spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f141,f233])).

fof(f233,plain,
    ( ~ v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0))
    | spl3_2
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f95,f129])).

fof(f129,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl3_5
  <=> k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f95,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl3_2
  <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f141,plain,
    ( v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0))
    | spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f140,f108])).

fof(f140,plain,
    ( v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0))
    | v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f138,f58])).

fof(f138,plain,
    ( v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl3_5 ),
    inference(superposition,[],[f113,f129])).

fof(f113,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_zfmisc_1(X0) ) ),
    inference(subsumption_resolution,[],[f74,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

fof(f191,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | spl3_6 ),
    inference(subsumption_resolution,[],[f189,f56])).

fof(f189,plain,
    ( v2_struct_0(sK0)
    | spl3_6 ),
    inference(subsumption_resolution,[],[f188,f57])).

fof(f188,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl3_6 ),
    inference(subsumption_resolution,[],[f187,f58])).

fof(f187,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl3_6 ),
    inference(resolution,[],[f172,f83])).

fof(f172,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f170])).

fof(f130,plain,
    ( spl3_3
    | spl3_5 ),
    inference(avatar_split_clause,[],[f125,f127,f102])).

fof(f125,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f85,f58])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f84,f61])).

fof(f61,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f84,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f109,plain,
    ( spl3_3
    | ~ spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f100,f93,f106,f102])).

fof(f100,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f99,f58])).

fof(f99,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl3_2 ),
    inference(resolution,[],[f62,f94])).

fof(f94,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ v1_zfmisc_1(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(f97,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f59,f93,f89])).

fof(f59,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f96,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f60,f93,f89])).

fof(f60,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:24:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.54  % (23064)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.47/0.56  % (23063)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.47/0.56  % (23073)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.47/0.56  % (23084)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.47/0.56  % (23066)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.47/0.57  % (23084)Refutation not found, incomplete strategy% (23084)------------------------------
% 1.47/0.57  % (23084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (23084)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.57  
% 1.47/0.57  % (23084)Memory used [KB]: 6268
% 1.47/0.57  % (23084)Time elapsed: 0.086 s
% 1.47/0.57  % (23084)------------------------------
% 1.47/0.57  % (23084)------------------------------
% 1.47/0.57  % (23061)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.47/0.57  % (23062)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.47/0.57  % (23064)Refutation found. Thanks to Tanya!
% 1.47/0.57  % SZS status Theorem for theBenchmark
% 1.47/0.57  % SZS output start Proof for theBenchmark
% 1.47/0.57  fof(f339,plain,(
% 1.47/0.57    $false),
% 1.47/0.57    inference(avatar_sat_refutation,[],[f96,f97,f109,f130,f191,f239,f244,f253,f271,f326])).
% 1.47/0.57  fof(f326,plain,(
% 1.47/0.57    spl3_1 | spl3_4),
% 1.47/0.57    inference(avatar_contradiction_clause,[],[f325])).
% 1.47/0.57  fof(f325,plain,(
% 1.47/0.57    $false | (spl3_1 | spl3_4)),
% 1.47/0.57    inference(subsumption_resolution,[],[f324,f121])).
% 1.47/0.57  fof(f121,plain,(
% 1.47/0.57    v7_struct_0(k1_tex_2(sK0,sK1))),
% 1.47/0.57    inference(subsumption_resolution,[],[f120,f56])).
% 1.47/0.57  fof(f56,plain,(
% 1.47/0.57    ~v2_struct_0(sK0)),
% 1.47/0.57    inference(cnf_transformation,[],[f50])).
% 1.47/0.57  fof(f50,plain,(
% 1.47/0.57    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.47/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f47,f49,f48])).
% 1.47/0.57  fof(f48,plain,(
% 1.47/0.57    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,X1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,X1),sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.47/0.57    introduced(choice_axiom,[])).
% 1.47/0.57  fof(f49,plain,(
% 1.47/0.57    ? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,X1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,X1),sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 1.47/0.57    introduced(choice_axiom,[])).
% 1.47/0.57  fof(f47,plain,(
% 1.47/0.57    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.47/0.57    inference(flattening,[],[f46])).
% 1.47/0.57  fof(f46,plain,(
% 1.47/0.57    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.47/0.57    inference(nnf_transformation,[],[f20])).
% 1.47/0.57  fof(f20,plain,(
% 1.47/0.57    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.47/0.57    inference(flattening,[],[f19])).
% 1.47/0.57  fof(f19,plain,(
% 1.47/0.57    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.47/0.57    inference(ennf_transformation,[],[f18])).
% 1.47/0.57  fof(f18,negated_conjecture,(
% 1.47/0.57    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 1.47/0.57    inference(negated_conjecture,[],[f17])).
% 1.47/0.57  fof(f17,conjecture,(
% 1.47/0.57    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).
% 1.47/0.57  fof(f120,plain,(
% 1.47/0.57    v7_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0)),
% 1.47/0.57    inference(subsumption_resolution,[],[f119,f57])).
% 1.47/0.57  fof(f57,plain,(
% 1.47/0.57    l1_pre_topc(sK0)),
% 1.47/0.57    inference(cnf_transformation,[],[f50])).
% 1.47/0.57  fof(f119,plain,(
% 1.47/0.57    v7_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.47/0.57    inference(resolution,[],[f79,f58])).
% 1.47/0.57  fof(f58,plain,(
% 1.47/0.57    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.47/0.57    inference(cnf_transformation,[],[f50])).
% 1.47/0.57  fof(f79,plain,(
% 1.47/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | v7_struct_0(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f41])).
% 1.47/0.57  fof(f41,plain,(
% 1.47/0.57    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.47/0.57    inference(flattening,[],[f40])).
% 1.47/0.57  fof(f40,plain,(
% 1.47/0.57    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.47/0.57    inference(ennf_transformation,[],[f12])).
% 1.47/0.57  fof(f12,axiom,(
% 1.47/0.57    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).
% 1.47/0.57  fof(f324,plain,(
% 1.47/0.57    ~v7_struct_0(k1_tex_2(sK0,sK1)) | (spl3_1 | spl3_4)),
% 1.47/0.57    inference(subsumption_resolution,[],[f323,f147])).
% 1.47/0.57  fof(f147,plain,(
% 1.47/0.57    l1_struct_0(k1_tex_2(sK0,sK1))),
% 1.47/0.57    inference(resolution,[],[f146,f64])).
% 1.47/0.57  fof(f64,plain,(
% 1.47/0.57    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f25])).
% 1.47/0.57  fof(f25,plain,(
% 1.47/0.57    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.47/0.57    inference(ennf_transformation,[],[f3])).
% 1.47/0.57  fof(f3,axiom,(
% 1.47/0.57    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.47/0.57  fof(f146,plain,(
% 1.47/0.57    l1_pre_topc(k1_tex_2(sK0,sK1))),
% 1.47/0.57    inference(subsumption_resolution,[],[f145,f56])).
% 1.47/0.57  fof(f145,plain,(
% 1.47/0.57    v2_struct_0(sK0) | l1_pre_topc(k1_tex_2(sK0,sK1))),
% 1.47/0.57    inference(subsumption_resolution,[],[f144,f57])).
% 1.47/0.57  fof(f144,plain,(
% 1.47/0.57    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | l1_pre_topc(k1_tex_2(sK0,sK1))),
% 1.47/0.57    inference(resolution,[],[f143,f58])).
% 1.47/0.57  fof(f143,plain,(
% 1.47/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(X1) | v2_struct_0(X1) | l1_pre_topc(k1_tex_2(X1,X0))) )),
% 1.47/0.57    inference(duplicate_literal_removal,[],[f142])).
% 1.47/0.57  fof(f142,plain,(
% 1.47/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(X1) | v2_struct_0(X1) | l1_pre_topc(k1_tex_2(X1,X0)) | ~l1_pre_topc(X1)) )),
% 1.47/0.57    inference(resolution,[],[f83,f65])).
% 1.47/0.57  fof(f65,plain,(
% 1.47/0.57    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f26])).
% 1.47/0.57  fof(f26,plain,(
% 1.47/0.57    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.47/0.57    inference(ennf_transformation,[],[f4])).
% 1.47/0.57  fof(f4,axiom,(
% 1.47/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.47/0.57  fof(f83,plain,(
% 1.47/0.57    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f43])).
% 1.47/0.57  fof(f43,plain,(
% 1.47/0.57    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.47/0.57    inference(flattening,[],[f42])).
% 1.47/0.57  fof(f42,plain,(
% 1.47/0.57    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.47/0.57    inference(ennf_transformation,[],[f11])).
% 1.47/0.57  fof(f11,axiom,(
% 1.47/0.57    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 1.47/0.57  fof(f323,plain,(
% 1.47/0.57    ~l1_struct_0(k1_tex_2(sK0,sK1)) | ~v7_struct_0(k1_tex_2(sK0,sK1)) | (spl3_1 | spl3_4)),
% 1.47/0.57    inference(subsumption_resolution,[],[f308,f108])).
% 1.47/0.57  fof(f108,plain,(
% 1.47/0.57    ~v1_zfmisc_1(u1_struct_0(sK0)) | spl3_4),
% 1.47/0.57    inference(avatar_component_clause,[],[f106])).
% 1.47/0.57  fof(f106,plain,(
% 1.47/0.57    spl3_4 <=> v1_zfmisc_1(u1_struct_0(sK0))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.47/0.57  fof(f308,plain,(
% 1.47/0.57    v1_zfmisc_1(u1_struct_0(sK0)) | ~l1_struct_0(k1_tex_2(sK0,sK1)) | ~v7_struct_0(k1_tex_2(sK0,sK1)) | spl3_1),
% 1.47/0.57    inference(superposition,[],[f75,f205])).
% 1.47/0.57  fof(f205,plain,(
% 1.47/0.57    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | spl3_1),
% 1.47/0.57    inference(forward_demodulation,[],[f204,f163])).
% 1.47/0.57  fof(f163,plain,(
% 1.47/0.57    u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1)) | spl3_1),
% 1.47/0.57    inference(subsumption_resolution,[],[f162,f56])).
% 1.47/0.57  fof(f162,plain,(
% 1.47/0.57    u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | spl3_1),
% 1.47/0.57    inference(subsumption_resolution,[],[f161,f58])).
% 1.47/0.57  fof(f161,plain,(
% 1.47/0.57    u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | spl3_1),
% 1.47/0.57    inference(subsumption_resolution,[],[f158,f57])).
% 1.47/0.57  fof(f158,plain,(
% 1.47/0.57    ~l1_pre_topc(sK0) | u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | spl3_1),
% 1.47/0.57    inference(resolution,[],[f154,f91])).
% 1.47/0.57  fof(f91,plain,(
% 1.47/0.57    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | spl3_1),
% 1.47/0.57    inference(avatar_component_clause,[],[f89])).
% 1.47/0.57  fof(f89,plain,(
% 1.47/0.57    spl3_1 <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.47/0.57  fof(f154,plain,(
% 1.47/0.57    ( ! [X0,X1] : (v1_tex_2(k1_tex_2(X0,X1),X0) | ~l1_pre_topc(X0) | u1_struct_0(X0) = sK2(X0,k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 1.47/0.57    inference(duplicate_literal_removal,[],[f153])).
% 1.47/0.57  fof(f153,plain,(
% 1.47/0.57    ( ! [X0,X1] : (v1_tex_2(k1_tex_2(X0,X1),X0) | ~l1_pre_topc(X0) | u1_struct_0(X0) = sK2(X0,k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.57    inference(resolution,[],[f152,f83])).
% 1.47/0.57  fof(f152,plain,(
% 1.47/0.57    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | v1_tex_2(X0,X1) | ~l1_pre_topc(X1) | u1_struct_0(X1) = sK2(X1,X0)) )),
% 1.47/0.57    inference(subsumption_resolution,[],[f150,f70])).
% 1.47/0.57  fof(f70,plain,(
% 1.47/0.57    ( ! [X0,X1] : (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f54])).
% 1.47/0.57  fof(f54,plain,(
% 1.47/0.57    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.47/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f52,f53])).
% 1.47/0.57  fof(f53,plain,(
% 1.47/0.57    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.47/0.57    introduced(choice_axiom,[])).
% 1.47/0.57  fof(f52,plain,(
% 1.47/0.57    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.47/0.57    inference(rectify,[],[f51])).
% 1.47/0.57  % (23058)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.67/0.58  % (23079)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.67/0.58  % (23087)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.67/0.58  fof(f51,plain,(
% 1.67/0.58    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.67/0.58    inference(nnf_transformation,[],[f29])).
% 1.67/0.58  fof(f29,plain,(
% 1.67/0.58    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.67/0.58    inference(flattening,[],[f28])).
% 1.67/0.58  fof(f28,plain,(
% 1.67/0.58    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.67/0.58    inference(ennf_transformation,[],[f9])).
% 1.67/0.58  fof(f9,axiom,(
% 1.67/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).
% 1.67/0.58  fof(f150,plain,(
% 1.67/0.58    ( ! [X0,X1] : (v1_tex_2(X0,X1) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | u1_struct_0(X1) = sK2(X1,X0) | v1_subset_1(sK2(X1,X0),u1_struct_0(X1))) )),
% 1.67/0.58    inference(resolution,[],[f68,f77])).
% 1.67/0.58  fof(f77,plain,(
% 1.67/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f55])).
% 1.67/0.58  fof(f55,plain,(
% 1.67/0.58    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.67/0.58    inference(nnf_transformation,[],[f39])).
% 1.67/0.58  fof(f39,plain,(
% 1.67/0.58    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.67/0.58    inference(ennf_transformation,[],[f10])).
% 1.67/0.58  fof(f10,axiom,(
% 1.67/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 1.67/0.58  fof(f68,plain,(
% 1.67/0.58    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f54])).
% 1.67/0.58  fof(f204,plain,(
% 1.67/0.58    sK2(sK0,k1_tex_2(sK0,sK1)) = u1_struct_0(k1_tex_2(sK0,sK1)) | spl3_1),
% 1.67/0.58    inference(subsumption_resolution,[],[f203,f56])).
% 1.67/0.58  fof(f203,plain,(
% 1.67/0.58    sK2(sK0,k1_tex_2(sK0,sK1)) = u1_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | spl3_1),
% 1.67/0.58    inference(subsumption_resolution,[],[f202,f58])).
% 1.67/0.58  fof(f202,plain,(
% 1.67/0.58    sK2(sK0,k1_tex_2(sK0,sK1)) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | spl3_1),
% 1.67/0.58    inference(subsumption_resolution,[],[f199,f57])).
% 1.67/0.58  fof(f199,plain,(
% 1.67/0.58    sK2(sK0,k1_tex_2(sK0,sK1)) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | spl3_1),
% 1.67/0.58    inference(resolution,[],[f149,f91])).
% 1.67/0.58  fof(f149,plain,(
% 1.67/0.58    ( ! [X0,X1] : (v1_tex_2(k1_tex_2(X0,X1),X0) | u1_struct_0(k1_tex_2(X0,X1)) = sK2(X0,k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 1.67/0.58    inference(duplicate_literal_removal,[],[f148])).
% 1.67/0.58  fof(f148,plain,(
% 1.67/0.58    ( ! [X0,X1] : (u1_struct_0(k1_tex_2(X0,X1)) = sK2(X0,k1_tex_2(X0,X1)) | v1_tex_2(k1_tex_2(X0,X1),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.67/0.58    inference(resolution,[],[f69,f83])).
% 1.67/0.58  % (23087)Refutation not found, incomplete strategy% (23087)------------------------------
% 1.67/0.58  % (23087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.58  % (23087)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.58  
% 1.67/0.58  % (23087)Memory used [KB]: 1663
% 1.67/0.58  % (23087)Time elapsed: 0.001 s
% 1.67/0.58  % (23087)------------------------------
% 1.67/0.58  % (23087)------------------------------
% 1.67/0.58  fof(f69,plain,(
% 1.67/0.58    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | u1_struct_0(X1) = sK2(X0,X1) | v1_tex_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f54])).
% 1.67/0.58  fof(f75,plain,(
% 1.67/0.58    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f38])).
% 1.67/0.58  fof(f38,plain,(
% 1.67/0.58    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 1.67/0.58    inference(flattening,[],[f37])).
% 1.67/0.58  fof(f37,plain,(
% 1.67/0.58    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 1.67/0.58    inference(ennf_transformation,[],[f6])).
% 1.67/0.58  fof(f6,axiom,(
% 1.67/0.58    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).
% 1.67/0.58  fof(f271,plain,(
% 1.67/0.58    ~spl3_13),
% 1.67/0.58    inference(avatar_contradiction_clause,[],[f270])).
% 1.67/0.58  fof(f270,plain,(
% 1.67/0.58    $false | ~spl3_13),
% 1.67/0.58    inference(subsumption_resolution,[],[f269,f118])).
% 1.67/0.58  fof(f118,plain,(
% 1.67/0.58    ~v2_struct_0(k1_tex_2(sK0,sK1))),
% 1.67/0.58    inference(subsumption_resolution,[],[f117,f56])).
% 1.67/0.58  fof(f117,plain,(
% 1.67/0.58    ~v2_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0)),
% 1.67/0.58    inference(subsumption_resolution,[],[f116,f57])).
% 1.67/0.58  fof(f116,plain,(
% 1.67/0.58    ~v2_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.67/0.58    inference(resolution,[],[f78,f58])).
% 1.67/0.58  fof(f78,plain,(
% 1.67/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_struct_0(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f41])).
% 1.67/0.58  fof(f269,plain,(
% 1.67/0.58    v2_struct_0(k1_tex_2(sK0,sK1)) | ~spl3_13),
% 1.67/0.58    inference(subsumption_resolution,[],[f267,f147])).
% 1.67/0.58  fof(f267,plain,(
% 1.67/0.58    ~l1_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~spl3_13),
% 1.67/0.58    inference(resolution,[],[f252,f73])).
% 1.67/0.58  fof(f73,plain,(
% 1.67/0.58    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f34])).
% 1.67/0.58  fof(f34,plain,(
% 1.67/0.58    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.67/0.58    inference(flattening,[],[f33])).
% 1.67/0.58  fof(f33,plain,(
% 1.67/0.58    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.67/0.58    inference(ennf_transformation,[],[f5])).
% 1.67/0.58  fof(f5,axiom,(
% 1.67/0.58    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.67/0.58  fof(f252,plain,(
% 1.67/0.58    v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~spl3_13),
% 1.67/0.58    inference(avatar_component_clause,[],[f250])).
% 1.67/0.58  fof(f250,plain,(
% 1.67/0.58    spl3_13 <=> v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 1.67/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.67/0.58  fof(f253,plain,(
% 1.67/0.58    ~spl3_4 | spl3_13 | spl3_3 | ~spl3_1 | ~spl3_6),
% 1.67/0.58    inference(avatar_split_clause,[],[f248,f170,f89,f102,f250,f106])).
% 1.67/0.58  fof(f102,plain,(
% 1.67/0.58    spl3_3 <=> v1_xboole_0(u1_struct_0(sK0))),
% 1.67/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.67/0.58  % (23065)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.67/0.58  fof(f170,plain,(
% 1.67/0.58    spl3_6 <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 1.67/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.67/0.58  fof(f248,plain,(
% 1.67/0.58    v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~v1_zfmisc_1(u1_struct_0(sK0)) | (~spl3_1 | ~spl3_6)),
% 1.67/0.58    inference(subsumption_resolution,[],[f247,f57])).
% 1.67/0.58  fof(f247,plain,(
% 1.67/0.58    v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~v1_zfmisc_1(u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | (~spl3_1 | ~spl3_6)),
% 1.67/0.58    inference(subsumption_resolution,[],[f234,f171])).
% 1.67/0.58  fof(f171,plain,(
% 1.67/0.58    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~spl3_6),
% 1.67/0.58    inference(avatar_component_clause,[],[f170])).
% 1.67/0.58  fof(f234,plain,(
% 1.67/0.58    v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~v1_zfmisc_1(u1_struct_0(sK0)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~spl3_1),
% 1.67/0.58    inference(resolution,[],[f90,f136])).
% 1.67/0.58  fof(f136,plain,(
% 1.67/0.58    ( ! [X2,X3] : (~v1_tex_2(X2,X3) | v1_xboole_0(u1_struct_0(X3)) | v1_xboole_0(u1_struct_0(X2)) | ~v1_zfmisc_1(u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~l1_pre_topc(X3)) )),
% 1.67/0.58    inference(subsumption_resolution,[],[f132,f66])).
% 1.67/0.58  fof(f66,plain,(
% 1.67/0.58    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f27])).
% 1.67/0.58  fof(f27,plain,(
% 1.67/0.58    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.67/0.58    inference(ennf_transformation,[],[f8])).
% 1.67/0.58  fof(f8,axiom,(
% 1.67/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).
% 1.67/0.58  fof(f132,plain,(
% 1.67/0.58    ( ! [X2,X3] : (~r1_tarski(u1_struct_0(X2),u1_struct_0(X3)) | ~v1_zfmisc_1(u1_struct_0(X3)) | v1_xboole_0(u1_struct_0(X3)) | v1_xboole_0(u1_struct_0(X2)) | ~v1_tex_2(X2,X3) | ~m1_pre_topc(X2,X3) | ~l1_pre_topc(X3)) )),
% 1.67/0.58    inference(extensionality_resolution,[],[f63,f71])).
% 1.67/0.58  fof(f71,plain,(
% 1.67/0.58    ( ! [X0,X1] : (u1_struct_0(X0) != u1_struct_0(X1) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f31])).
% 1.67/0.58  fof(f31,plain,(
% 1.67/0.58    ! [X0] : (! [X1] : (~v1_tex_2(X1,X0) | u1_struct_0(X0) != u1_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.67/0.58    inference(flattening,[],[f30])).
% 1.67/0.58  fof(f30,plain,(
% 1.67/0.58    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) | u1_struct_0(X0) != u1_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.67/0.58    inference(ennf_transformation,[],[f13])).
% 1.67/0.58  fof(f13,axiom,(
% 1.67/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ~(v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1))))),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tex_2)).
% 1.67/0.58  fof(f63,plain,(
% 1.67/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f24])).
% 1.67/0.58  fof(f24,plain,(
% 1.67/0.58    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.67/0.58    inference(flattening,[],[f23])).
% 1.67/0.58  fof(f23,plain,(
% 1.67/0.58    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.67/0.58    inference(ennf_transformation,[],[f14])).
% 1.67/0.58  fof(f14,axiom,(
% 1.67/0.58    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 1.67/0.58  fof(f90,plain,(
% 1.67/0.58    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl3_1),
% 1.67/0.58    inference(avatar_component_clause,[],[f89])).
% 1.67/0.58  fof(f244,plain,(
% 1.67/0.58    ~spl3_3),
% 1.67/0.58    inference(avatar_contradiction_clause,[],[f243])).
% 1.67/0.58  fof(f243,plain,(
% 1.67/0.58    $false | ~spl3_3),
% 1.67/0.58    inference(subsumption_resolution,[],[f242,f56])).
% 1.67/0.58  fof(f242,plain,(
% 1.67/0.58    v2_struct_0(sK0) | ~spl3_3),
% 1.67/0.58    inference(subsumption_resolution,[],[f240,f98])).
% 1.67/0.58  fof(f98,plain,(
% 1.67/0.58    l1_struct_0(sK0)),
% 1.67/0.58    inference(resolution,[],[f64,f57])).
% 1.67/0.58  fof(f240,plain,(
% 1.67/0.58    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl3_3),
% 1.67/0.58    inference(resolution,[],[f104,f73])).
% 1.67/0.58  fof(f104,plain,(
% 1.67/0.58    v1_xboole_0(u1_struct_0(sK0)) | ~spl3_3),
% 1.67/0.58    inference(avatar_component_clause,[],[f102])).
% 1.67/0.58  fof(f239,plain,(
% 1.67/0.58    spl3_2 | spl3_4 | ~spl3_5),
% 1.67/0.58    inference(avatar_contradiction_clause,[],[f238])).
% 1.67/0.58  fof(f238,plain,(
% 1.67/0.58    $false | (spl3_2 | spl3_4 | ~spl3_5)),
% 1.67/0.58    inference(subsumption_resolution,[],[f141,f233])).
% 1.67/0.58  fof(f233,plain,(
% 1.67/0.58    ~v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0)) | (spl3_2 | ~spl3_5)),
% 1.67/0.58    inference(forward_demodulation,[],[f95,f129])).
% 1.67/0.58  fof(f129,plain,(
% 1.67/0.58    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | ~spl3_5),
% 1.67/0.58    inference(avatar_component_clause,[],[f127])).
% 1.67/0.58  fof(f127,plain,(
% 1.67/0.58    spl3_5 <=> k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)),
% 1.67/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.67/0.58  fof(f95,plain,(
% 1.67/0.58    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | spl3_2),
% 1.67/0.58    inference(avatar_component_clause,[],[f93])).
% 1.67/0.58  fof(f93,plain,(
% 1.67/0.58    spl3_2 <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 1.67/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.67/0.58  fof(f141,plain,(
% 1.67/0.58    v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0)) | (spl3_4 | ~spl3_5)),
% 1.67/0.58    inference(subsumption_resolution,[],[f140,f108])).
% 1.67/0.58  fof(f140,plain,(
% 1.67/0.58    v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0)) | v1_zfmisc_1(u1_struct_0(sK0)) | ~spl3_5),
% 1.67/0.58    inference(subsumption_resolution,[],[f138,f58])).
% 1.67/0.58  fof(f138,plain,(
% 1.67/0.58    v1_subset_1(k2_tarski(sK1,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_zfmisc_1(u1_struct_0(sK0)) | ~spl3_5),
% 1.67/0.58    inference(superposition,[],[f113,f129])).
% 1.67/0.58  fof(f113,plain,(
% 1.67/0.58    ( ! [X0,X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_zfmisc_1(X0)) )),
% 1.67/0.58    inference(subsumption_resolution,[],[f74,f72])).
% 1.67/0.58  fof(f72,plain,(
% 1.67/0.58    ( ! [X0] : (~v1_xboole_0(X0) | v1_zfmisc_1(X0)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f32])).
% 1.67/0.58  fof(f32,plain,(
% 1.67/0.58    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 1.67/0.58    inference(ennf_transformation,[],[f2])).
% 1.67/0.58  fof(f2,axiom,(
% 1.67/0.58    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).
% 1.67/0.58  fof(f74,plain,(
% 1.67/0.58    ( ! [X0,X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f36])).
% 1.67/0.58  fof(f36,plain,(
% 1.67/0.58    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 1.67/0.58    inference(flattening,[],[f35])).
% 1.67/0.58  fof(f35,plain,(
% 1.67/0.58    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 1.67/0.58    inference(ennf_transformation,[],[f16])).
% 1.67/0.58  fof(f16,axiom,(
% 1.67/0.58    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).
% 1.67/0.58  fof(f191,plain,(
% 1.67/0.58    spl3_6),
% 1.67/0.58    inference(avatar_contradiction_clause,[],[f190])).
% 1.67/0.58  fof(f190,plain,(
% 1.67/0.58    $false | spl3_6),
% 1.67/0.58    inference(subsumption_resolution,[],[f189,f56])).
% 1.67/0.58  fof(f189,plain,(
% 1.67/0.58    v2_struct_0(sK0) | spl3_6),
% 1.67/0.58    inference(subsumption_resolution,[],[f188,f57])).
% 1.67/0.58  fof(f188,plain,(
% 1.67/0.58    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl3_6),
% 1.67/0.58    inference(subsumption_resolution,[],[f187,f58])).
% 1.67/0.58  fof(f187,plain,(
% 1.67/0.58    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl3_6),
% 1.67/0.58    inference(resolution,[],[f172,f83])).
% 1.67/0.58  fof(f172,plain,(
% 1.67/0.58    ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | spl3_6),
% 1.67/0.58    inference(avatar_component_clause,[],[f170])).
% 1.67/0.58  fof(f130,plain,(
% 1.67/0.58    spl3_3 | spl3_5),
% 1.67/0.58    inference(avatar_split_clause,[],[f125,f127,f102])).
% 1.67/0.58  fof(f125,plain,(
% 1.67/0.58    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | v1_xboole_0(u1_struct_0(sK0))),
% 1.67/0.58    inference(resolution,[],[f85,f58])).
% 1.67/0.58  fof(f85,plain,(
% 1.67/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) )),
% 1.67/0.58    inference(definition_unfolding,[],[f84,f61])).
% 1.67/0.58  fof(f61,plain,(
% 1.67/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f1])).
% 1.67/0.58  fof(f1,axiom,(
% 1.67/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.67/0.58  fof(f84,plain,(
% 1.67/0.58    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f45])).
% 1.67/0.58  fof(f45,plain,(
% 1.67/0.58    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.67/0.58    inference(flattening,[],[f44])).
% 1.67/0.58  fof(f44,plain,(
% 1.67/0.58    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.67/0.58    inference(ennf_transformation,[],[f7])).
% 1.67/0.58  fof(f7,axiom,(
% 1.67/0.58    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.67/0.58  fof(f109,plain,(
% 1.67/0.58    spl3_3 | ~spl3_4 | ~spl3_2),
% 1.67/0.58    inference(avatar_split_clause,[],[f100,f93,f106,f102])).
% 1.67/0.58  fof(f100,plain,(
% 1.67/0.58    ~v1_zfmisc_1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~spl3_2),
% 1.67/0.58    inference(subsumption_resolution,[],[f99,f58])).
% 1.67/0.58  fof(f99,plain,(
% 1.67/0.58    ~v1_zfmisc_1(u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~spl3_2),
% 1.67/0.58    inference(resolution,[],[f62,f94])).
% 1.67/0.58  fof(f94,plain,(
% 1.67/0.58    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl3_2),
% 1.67/0.58    inference(avatar_component_clause,[],[f93])).
% 1.67/0.58  fof(f62,plain,(
% 1.67/0.58    ( ! [X0,X1] : (~v1_subset_1(k6_domain_1(X0,X1),X0) | ~v1_zfmisc_1(X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f22])).
% 1.67/0.58  fof(f22,plain,(
% 1.67/0.58    ! [X0] : (! [X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 1.67/0.58    inference(flattening,[],[f21])).
% 1.67/0.58  fof(f21,plain,(
% 1.67/0.58    ! [X0] : (! [X1] : ((~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0)) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 1.67/0.58    inference(ennf_transformation,[],[f15])).
% 1.67/0.58  fof(f15,axiom,(
% 1.67/0.58    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 1.67/0.58  fof(f97,plain,(
% 1.67/0.58    spl3_1 | spl3_2),
% 1.67/0.58    inference(avatar_split_clause,[],[f59,f93,f89])).
% 1.67/0.58  fof(f59,plain,(
% 1.67/0.58    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 1.67/0.58    inference(cnf_transformation,[],[f50])).
% 1.67/0.58  fof(f96,plain,(
% 1.67/0.58    ~spl3_1 | ~spl3_2),
% 1.67/0.58    inference(avatar_split_clause,[],[f60,f93,f89])).
% 1.67/0.58  fof(f60,plain,(
% 1.67/0.58    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 1.67/0.58    inference(cnf_transformation,[],[f50])).
% 1.67/0.58  % SZS output end Proof for theBenchmark
% 1.67/0.58  % (23064)------------------------------
% 1.67/0.58  % (23064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.58  % (23064)Termination reason: Refutation
% 1.67/0.58  
% 1.67/0.58  % (23064)Memory used [KB]: 10874
% 1.67/0.58  % (23064)Time elapsed: 0.148 s
% 1.67/0.58  % (23064)------------------------------
% 1.67/0.58  % (23064)------------------------------
% 1.67/0.59  % (23057)Success in time 0.224 s
%------------------------------------------------------------------------------
