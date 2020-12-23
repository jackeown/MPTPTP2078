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
% DateTime   : Thu Dec  3 13:18:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  222 ( 588 expanded)
%              Number of leaves         :   56 ( 291 expanded)
%              Depth                    :   13
%              Number of atoms          : 1392 (6274 expanded)
%              Number of equality atoms :   38 ( 356 expanded)
%              Maximal formula depth    :   27 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (9916)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% (9917)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f452,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f119,f122,f126,f130,f134,f138,f142,f146,f150,f154,f158,f162,f166,f170,f174,f178,f182,f198,f203,f232,f238,f246,f247,f253,f282,f291,f304,f315,f339,f369,f372,f420,f427,f430,f443])).

fof(f443,plain,
    ( spl9_8
    | ~ spl9_49
    | ~ spl9_50
    | ~ spl9_19
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_51 ),
    inference(avatar_split_clause,[],[f439,f418,f128,f124,f201,f415,f412,f144])).

fof(f144,plain,
    ( spl9_8
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f412,plain,
    ( spl9_49
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).

fof(f415,plain,
    ( spl9_50
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).

fof(f201,plain,
    ( spl9_19
  <=> m1_subset_1(sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f124,plain,
    ( spl9_3
  <=> sK4 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f128,plain,
    ( spl9_4
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f418,plain,
    ( spl9_51
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X1,sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_51])])).

fof(f439,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_51 ),
    inference(resolution,[],[f434,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK8(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK8(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f42,f62])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK8(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).

fof(f434,plain,
    ( ! [X0] : ~ m1_connsp_2(X0,sK3,sK4)
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_51 ),
    inference(forward_demodulation,[],[f431,f125])).

fof(f125,plain,
    ( sK4 = sK5
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f124])).

fof(f431,plain,
    ( ! [X0] : ~ m1_connsp_2(X0,sK3,sK5)
    | ~ spl9_4
    | ~ spl9_51 ),
    inference(resolution,[],[f419,f129])).

fof(f129,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f128])).

fof(f419,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X1,sK3,X0) )
    | ~ spl9_51 ),
    inference(avatar_component_clause,[],[f418])).

fof(f430,plain,
    ( ~ spl9_12
    | ~ spl9_6
    | spl9_50 ),
    inference(avatar_split_clause,[],[f429,f415,f136,f160])).

fof(f160,plain,
    ( spl9_12
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f136,plain,
    ( spl9_6
  <=> m1_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f429,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl9_6
    | spl9_50 ),
    inference(resolution,[],[f428,f137])).

fof(f137,plain,
    ( m1_pre_topc(sK3,sK1)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f136])).

fof(f428,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0) )
    | spl9_50 ),
    inference(resolution,[],[f416,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f416,plain,
    ( ~ l1_pre_topc(sK3)
    | spl9_50 ),
    inference(avatar_component_clause,[],[f415])).

fof(f427,plain,
    ( ~ spl9_13
    | ~ spl9_12
    | ~ spl9_6
    | spl9_49 ),
    inference(avatar_split_clause,[],[f426,f412,f136,f160,f164])).

fof(f164,plain,
    ( spl9_13
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f426,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl9_6
    | spl9_49 ),
    inference(resolution,[],[f425,f137])).

fof(f425,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | spl9_49 ),
    inference(resolution,[],[f413,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f413,plain,
    ( ~ v2_pre_topc(sK3)
    | spl9_49 ),
    inference(avatar_component_clause,[],[f412])).

fof(f420,plain,
    ( ~ spl9_49
    | spl9_8
    | ~ spl9_50
    | spl9_51
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f410,f367,f418,f415,f144,f412])).

fof(f367,plain,
    ( spl9_44
  <=> ! [X46,X45,X47] :
        ( ~ l1_pre_topc(X45)
        | ~ m1_subset_1(X46,u1_struct_0(X45))
        | ~ m1_connsp_2(X47,X45,X46)
        | ~ m1_subset_1(sK6(X45,X46,X47),k1_zfmisc_1(u1_struct_0(sK3)))
        | v2_struct_0(X45)
        | ~ v2_pre_topc(X45) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).

fof(f410,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X1,sK3,X0)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ v2_pre_topc(sK3) )
    | ~ spl9_44 ),
    inference(duplicate_literal_removal,[],[f408])).

fof(f408,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X1,sK3,X0)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ v2_pre_topc(sK3)
        | ~ m1_connsp_2(X1,sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl9_44 ),
    inference(resolution,[],[f368,f184])).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f83,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( r2_hidden(X1,sK6(X0,X1,X2))
                    & r1_tarski(sK6(X0,X1,X2),X2)
                    & v3_pre_topc(sK6(X0,X1,X2),X0)
                    & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f54,f55])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK6(X0,X1,X2))
        & r1_tarski(sK6(X0,X1,X2),X2)
        & v3_pre_topc(sK6(X0,X1,X2),X0)
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( r2_hidden(X1,X4)
                      & r1_tarski(X4,X2)
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( r2_hidden(X1,X3)
                      & r1_tarski(X3,X2)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_connsp_2)).

fof(f368,plain,
    ( ! [X47,X45,X46] :
        ( ~ m1_subset_1(sK6(X45,X46,X47),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X46,u1_struct_0(X45))
        | ~ m1_connsp_2(X47,X45,X46)
        | ~ l1_pre_topc(X45)
        | v2_struct_0(X45)
        | ~ v2_pre_topc(X45) )
    | ~ spl9_44 ),
    inference(avatar_component_clause,[],[f367])).

% (9906)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f372,plain,
    ( ~ spl9_13
    | ~ spl9_12
    | ~ spl9_25
    | ~ spl9_7
    | ~ spl9_6
    | spl9_38 ),
    inference(avatar_split_clause,[],[f370,f337,f136,f140,f277,f160,f164])).

fof(f277,plain,
    ( spl9_25
  <=> m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f140,plain,
    ( spl9_7
  <=> v1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f337,plain,
    ( spl9_38
  <=> v3_pre_topc(u1_struct_0(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f370,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ v1_tsep_1(sK3,sK1)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl9_38 ),
    inference(resolution,[],[f338,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f338,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK3),sK1)
    | spl9_38 ),
    inference(avatar_component_clause,[],[f337])).

fof(f369,plain,
    ( ~ spl9_19
    | spl9_44
    | spl9_30 ),
    inference(avatar_split_clause,[],[f345,f302,f367,f201])).

fof(f302,plain,
    ( spl9_30
  <=> r2_hidden(sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f345,plain,
    ( ! [X47,X45,X46] :
        ( ~ l1_pre_topc(X45)
        | ~ v2_pre_topc(X45)
        | v2_struct_0(X45)
        | ~ m1_subset_1(sK6(X45,X46,X47),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_connsp_2(X47,X45,X46)
        | ~ m1_subset_1(X46,u1_struct_0(X45))
        | ~ m1_subset_1(sK4,u1_struct_0(sK3)) )
    | spl9_30 ),
    inference(resolution,[],[f303,f208])).

fof(f208,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(sK6(X1,X0,X2),k1_zfmisc_1(X3))
      | ~ m1_connsp_2(X2,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X4,X3) ) ),
    inference(resolution,[],[f207,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f207,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_xboole_0(X3)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(sK6(X1,X2,X0),k1_zfmisc_1(X3))
      | ~ m1_connsp_2(X0,X1,X2) ) ),
    inference(resolution,[],[f187,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f187,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK6(X0,X1,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f86,f103])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK6(X0,X1,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f303,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(sK3))
    | spl9_30 ),
    inference(avatar_component_clause,[],[f302])).

fof(f339,plain,
    ( spl9_14
    | ~ spl9_13
    | ~ spl9_12
    | ~ spl9_25
    | ~ spl9_5
    | ~ spl9_38
    | ~ spl9_30
    | spl9_32 ),
    inference(avatar_split_clause,[],[f331,f313,f302,f337,f132,f277,f160,f164,f168])).

fof(f168,plain,
    ( spl9_14
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f132,plain,
    ( spl9_5
  <=> m1_subset_1(sK4,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f313,plain,
    ( spl9_32
  <=> m1_connsp_2(u1_struct_0(sK3),sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f331,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(sK3))
    | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl9_32 ),
    inference(resolution,[],[f314,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f314,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK3),sK1,sK4)
    | spl9_32 ),
    inference(avatar_component_clause,[],[f313])).

fof(f315,plain,
    ( spl9_14
    | ~ spl9_13
    | ~ spl9_12
    | ~ spl9_5
    | ~ spl9_32
    | spl9_29 ),
    inference(avatar_split_clause,[],[f309,f299,f313,f132,f160,f164,f168])).

fof(f299,plain,
    ( spl9_29
  <=> m1_connsp_2(sK7(sK1,sK4,u1_struct_0(sK3)),sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f309,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK3),sK1,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl9_29 ),
    inference(resolution,[],[f300,f190])).

fof(f190,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK7(X0,X1,X2),X0,X1)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f90,f103])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK7(X0,X1,X2),X0,X1)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(sK7(X0,X1,X2),X2)
                & v3_pre_topc(sK7(X0,X1,X2),X0)
                & m1_connsp_2(sK7(X0,X1,X2),X0,X1)
                & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                & ~ v1_xboole_0(sK7(X0,X1,X2)) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f24,f57])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_tarski(X3,X2)
          & v3_pre_topc(X3,X0)
          & m1_connsp_2(X3,X0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X3) )
     => ( r1_tarski(sK7(X0,X1,X2),X2)
        & v3_pre_topc(sK7(X0,X1,X2),X0)
        & m1_connsp_2(sK7(X0,X1,X2),X0,X1)
        & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK7(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X3) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X3) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_tarski(X3,X2)
                          & v3_pre_topc(X3,X0)
                          & m1_connsp_2(X3,X0,X1) ) )
                  & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_connsp_2)).

fof(f300,plain,
    ( ~ m1_connsp_2(sK7(sK1,sK4,u1_struct_0(sK3)),sK1,sK4)
    | spl9_29 ),
    inference(avatar_component_clause,[],[f299])).

fof(f304,plain,
    ( ~ spl9_29
    | ~ spl9_30
    | ~ spl9_5
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f296,f280,f132,f302,f299])).

fof(f280,plain,
    ( spl9_26
  <=> ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_connsp_2(sK7(sK1,X0,u1_struct_0(sK3)),sK1,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f296,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(sK3))
    | ~ m1_connsp_2(sK7(sK1,sK4,u1_struct_0(sK3)),sK1,sK4)
    | ~ spl9_5
    | ~ spl9_26 ),
    inference(resolution,[],[f281,f133])).

fof(f133,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f132])).

fof(f281,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(sK7(sK1,X0,u1_struct_0(sK3)),sK1,sK4) )
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f280])).

fof(f291,plain,
    ( ~ spl9_12
    | ~ spl9_6
    | spl9_25 ),
    inference(avatar_split_clause,[],[f289,f277,f136,f160])).

fof(f289,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK1)
    | spl9_25 ),
    inference(resolution,[],[f278,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f278,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl9_25 ),
    inference(avatar_component_clause,[],[f277])).

fof(f282,plain,
    ( ~ spl9_6
    | ~ spl9_25
    | spl9_26
    | spl9_14
    | ~ spl9_13
    | ~ spl9_12
    | ~ spl9_7
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f275,f244,f140,f160,f164,f168,f280,f277,f136])).

fof(f244,plain,
    ( spl9_22
  <=> ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f275,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(sK7(sK1,X0,u1_struct_0(sK3)),sK1,sK4)
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_pre_topc(sK3,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl9_7
    | ~ spl9_22 ),
    inference(resolution,[],[f274,f141])).

fof(f141,plain,
    ( v1_tsep_1(sK3,sK1)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f140])).

fof(f274,plain,
    ( ! [X0,X1] :
        ( ~ v1_tsep_1(sK3,X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(sK7(X1,X0,u1_struct_0(sK3)),sK1,sK4)
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_subset_1(X0,u1_struct_0(X1)) )
    | ~ spl9_22 ),
    inference(duplicate_literal_removal,[],[f273])).

fof(f273,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(sK7(X1,X0,u1_struct_0(sK3)),sK1,sK4)
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_pre_topc(sK3,X1)
        | ~ v1_tsep_1(sK3,X1)
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl9_22 ),
    inference(resolution,[],[f270,f112])).

fof(f270,plain,
    ( ! [X4,X3] :
        ( ~ v3_pre_topc(u1_struct_0(sK3),X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3)
        | ~ r2_hidden(X4,u1_struct_0(sK3))
        | ~ m1_connsp_2(sK7(X3,X4,u1_struct_0(sK3)),sK1,sK4)
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X3))) )
    | ~ spl9_22 ),
    inference(duplicate_literal_removal,[],[f269])).

fof(f269,plain,
    ( ! [X4,X3] :
        ( ~ m1_connsp_2(sK7(X3,X4,u1_struct_0(sK3)),sK1,sK4)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3)
        | ~ r2_hidden(X4,u1_struct_0(sK3))
        | ~ v3_pre_topc(u1_struct_0(sK3),X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X3)))
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl9_22 ),
    inference(resolution,[],[f257,f93])).

fof(f257,plain,
    ( ! [X2,X3] :
        ( ~ m1_connsp_2(u1_struct_0(sK3),X2,X3)
        | ~ m1_connsp_2(sK7(X2,X3,u1_struct_0(sK3)),sK1,sK4)
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl9_22 ),
    inference(resolution,[],[f245,f192])).

fof(f192,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK7(X0,X1,X2),X2)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f92,f103])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK7(X0,X1,X2),X2)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f245,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK4) )
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f244])).

fof(f253,plain,
    ( spl9_17
    | ~ spl9_16
    | ~ spl9_15
    | spl9_14
    | ~ spl9_13
    | ~ spl9_12
    | ~ spl9_11
    | ~ spl9_10
    | ~ spl9_9
    | spl9_8
    | ~ spl9_6
    | ~ spl9_5
    | ~ spl9_19
    | ~ spl9_1
    | spl9_18 ),
    inference(avatar_split_clause,[],[f249,f196,f114,f201,f132,f136,f144,f148,f152,f156,f160,f164,f168,f172,f176,f180])).

fof(f180,plain,
    ( spl9_17
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f176,plain,
    ( spl9_16
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f172,plain,
    ( spl9_15
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f156,plain,
    ( spl9_11
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f152,plain,
    ( spl9_10
  <=> v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f148,plain,
    ( spl9_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f114,plain,
    ( spl9_1
  <=> r1_tmap_1(sK1,sK0,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f196,plain,
    ( spl9_18
  <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f249,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl9_18 ),
    inference(resolution,[],[f242,f106])).

fof(f106,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).

fof(f242,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | spl9_18 ),
    inference(avatar_component_clause,[],[f196])).

fof(f247,plain,
    ( sK4 != sK5
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f246,plain,
    ( spl9_8
    | ~ spl9_19
    | ~ spl9_18
    | spl9_22
    | ~ spl9_6
    | ~ spl9_21 ),
    inference(avatar_split_clause,[],[f239,f236,f136,f244,f196,f201,f144])).

fof(f236,plain,
    ( spl9_21
  <=> ! [X1,X0] :
        ( ~ m1_connsp_2(X0,sK1,sK4)
        | ~ r1_tarski(X0,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),sK4)
        | ~ m1_subset_1(sK4,u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f239,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK4)
        | v2_struct_0(sK3) )
    | ~ spl9_6
    | ~ spl9_21 ),
    inference(resolution,[],[f237,f137])).

fof(f237,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X1,sK1)
        | ~ r1_tarski(X0,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),sK4)
        | ~ m1_subset_1(sK4,u1_struct_0(X1))
        | ~ m1_connsp_2(X0,sK1,sK4)
        | v2_struct_0(X1) )
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f236])).

fof(f238,plain,
    ( ~ spl9_5
    | spl9_21
    | spl9_1
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f233,f230,f114,f236,f132])).

fof(f230,plain,
    ( spl9_20
  <=> ! [X1,X0,X2] :
        ( ~ m1_connsp_2(X0,sK1,X1)
        | r1_tmap_1(sK1,sK0,sK2,X1)
        | ~ r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X2))
        | ~ r1_tarski(X0,u1_struct_0(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f233,plain,
    ( ! [X0,X1] :
        ( ~ m1_connsp_2(X0,sK1,sK4)
        | ~ r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),sK4)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK1)
        | ~ m1_subset_1(sK4,u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,u1_struct_0(X1))
        | ~ r1_tarski(X0,u1_struct_0(X1)) )
    | spl9_1
    | ~ spl9_20 ),
    inference(resolution,[],[f231,f115])).

fof(f115,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f114])).

fof(f231,plain,
    ( ! [X2,X0,X1] :
        ( r1_tmap_1(sK1,sK0,sK2,X1)
        | ~ m1_connsp_2(X0,sK1,X1)
        | ~ r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X2))
        | ~ r1_tarski(X0,u1_struct_0(X2)) )
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f230])).

fof(f232,plain,
    ( spl9_17
    | ~ spl9_16
    | ~ spl9_15
    | spl9_14
    | ~ spl9_13
    | ~ spl9_12
    | ~ spl9_9
    | spl9_20
    | ~ spl9_10
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f221,f156,f152,f230,f148,f160,f164,f168,f172,f176,f180])).

fof(f221,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_connsp_2(X0,sK1,X1)
        | ~ r1_tarski(X0,u1_struct_0(X2))
        | ~ m1_subset_1(X1,u1_struct_0(X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_pre_topc(X2,sK1)
        | v2_struct_0(X2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1)
        | r1_tmap_1(sK1,sK0,sK2,X1)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_10
    | ~ spl9_11 ),
    inference(resolution,[],[f220,f153])).

fof(f153,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f152])).

fof(f220,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v1_funct_2(sK2,u1_struct_0(X2),u1_struct_0(X1))
        | ~ m1_connsp_2(X4,X2,X3)
        | ~ r1_tarski(X4,u1_struct_0(X0))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | ~ m1_pre_topc(X0,X2)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
        | r1_tmap_1(X2,X1,sK2,X3)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl9_11 ),
    inference(resolution,[],[f193,f157])).

fof(f157,plain,
    ( v1_funct_1(sK2)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f156])).

fof(f193,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ m1_connsp_2(X4,X1,X6)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | r1_tmap_1(X1,X0,X2,X6)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f107,f103])).

fof(f107,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X6)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ m1_connsp_2(X4,X1,X6)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X5)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | X5 != X6
      | ~ m1_connsp_2(X4,X1,X5)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( r1_tmap_1(X1,X0,X2,X5)
                                  | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                                & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                  | ~ r1_tmap_1(X1,X0,X2,X5) ) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( X5 = X6
                                  & m1_connsp_2(X4,X1,X5)
                                  & r1_tarski(X4,u1_struct_0(X3)) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tmap_1)).

fof(f203,plain,
    ( spl9_19
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f199,f128,f124,f201])).

fof(f199,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(superposition,[],[f129,f125])).

fof(f198,plain,
    ( spl9_18
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f194,f124,f117,f196])).

fof(f117,plain,
    ( spl9_2
  <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f194,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(forward_demodulation,[],[f121,f125])).

fof(f121,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f182,plain,(
    ~ spl9_17 ),
    inference(avatar_split_clause,[],[f64,f180])).

fof(f64,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
      | ~ r1_tmap_1(sK1,sK0,sK2,sK4) )
    & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
      | r1_tmap_1(sK1,sK0,sK2,sK4) )
    & sK4 = sK5
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_pre_topc(sK3,sK1)
    & v1_tsep_1(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f45,f51,f50,f49,f48,f47,f46])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                              | ~ r1_tmap_1(X1,X0,X2,X4) )
                            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                              | r1_tmap_1(X1,X0,X2,X4) )
                            & X4 = X5
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_pre_topc(X3,X1)
                    & v1_tsep_1(X3,X1)
                    & ~ v2_struct_0(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5)
                            | ~ r1_tmap_1(X1,sK0,X2,X4) )
                          & ( r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5)
                            | r1_tmap_1(X1,sK0,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,sK0,X2,X4) )
                        & ( r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5)
                          | r1_tmap_1(X1,sK0,X2,X4) )
                        & X4 = X5
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_subset_1(X4,u1_struct_0(X1)) )
                & m1_pre_topc(X3,X1)
                & v1_tsep_1(X3,X1)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
            & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5)
                        | ~ r1_tmap_1(sK1,sK0,X2,X4) )
                      & ( r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5)
                        | r1_tmap_1(sK1,sK0,X2,X4) )
                      & X4 = X5
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_subset_1(X4,u1_struct_0(sK1)) )
              & m1_pre_topc(X3,sK1)
              & v1_tsep_1(X3,sK1)
              & ~ v2_struct_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
          & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5)
                      | ~ r1_tmap_1(sK1,sK0,X2,X4) )
                    & ( r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5)
                      | r1_tmap_1(sK1,sK0,X2,X4) )
                    & X4 = X5
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_subset_1(X4,u1_struct_0(sK1)) )
            & m1_pre_topc(X3,sK1)
            & v1_tsep_1(X3,sK1)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5)
                    | ~ r1_tmap_1(sK1,sK0,sK2,X4) )
                  & ( r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5)
                    | r1_tmap_1(sK1,sK0,sK2,X4) )
                  & X4 = X5
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_subset_1(X4,u1_struct_0(sK1)) )
          & m1_pre_topc(X3,sK1)
          & v1_tsep_1(X3,sK1)
          & ~ v2_struct_0(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5)
                  | ~ r1_tmap_1(sK1,sK0,sK2,X4) )
                & ( r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5)
                  | r1_tmap_1(sK1,sK0,sK2,X4) )
                & X4 = X5
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & m1_subset_1(X4,u1_struct_0(sK1)) )
        & m1_pre_topc(X3,sK1)
        & v1_tsep_1(X3,sK1)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5)
                | ~ r1_tmap_1(sK1,sK0,sK2,X4) )
              & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5)
                | r1_tmap_1(sK1,sK0,sK2,X4) )
              & X4 = X5
              & m1_subset_1(X5,u1_struct_0(sK3)) )
          & m1_subset_1(X4,u1_struct_0(sK1)) )
      & m1_pre_topc(sK3,sK1)
      & v1_tsep_1(sK3,sK1)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5)
              | ~ r1_tmap_1(sK1,sK0,sK2,X4) )
            & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5)
              | r1_tmap_1(sK1,sK0,sK2,X4) )
            & X4 = X5
            & m1_subset_1(X5,u1_struct_0(sK3)) )
        & m1_subset_1(X4,u1_struct_0(sK1)) )
   => ( ? [X5] :
          ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5)
            | ~ r1_tmap_1(sK1,sK0,sK2,sK4) )
          & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5)
            | r1_tmap_1(sK1,sK0,sK2,sK4) )
          & sK4 = X5
          & m1_subset_1(X5,u1_struct_0(sK3)) )
      & m1_subset_1(sK4,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X5] :
        ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5)
          | ~ r1_tmap_1(sK1,sK0,sK2,sK4) )
        & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5)
          | r1_tmap_1(sK1,sK0,sK2,sK4) )
        & sK4 = X5
        & m1_subset_1(X5,u1_struct_0(sK3)) )
   => ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
        | ~ r1_tmap_1(sK1,sK0,sK2,sK4) )
      & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
        | r1_tmap_1(sK1,sK0,sK2,sK4) )
      & sK4 = sK5
      & m1_subset_1(sK5,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | ~ r1_tmap_1(X1,X0,X2,X4) )
                          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | r1_tmap_1(X1,X0,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | ~ r1_tmap_1(X1,X0,X2,X4) )
                          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | r1_tmap_1(X1,X0,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X1)
                      & v1_tsep_1(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ( X4 = X5
                             => ( r1_tmap_1(X1,X0,X2,X4)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & v1_tsep_1(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( X4 = X5
                           => ( r1_tmap_1(X1,X0,X2,X4)
                            <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).

fof(f178,plain,(
    spl9_16 ),
    inference(avatar_split_clause,[],[f65,f176])).

fof(f65,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f174,plain,(
    spl9_15 ),
    inference(avatar_split_clause,[],[f66,f172])).

fof(f66,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f170,plain,(
    ~ spl9_14 ),
    inference(avatar_split_clause,[],[f67,f168])).

fof(f67,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f166,plain,(
    spl9_13 ),
    inference(avatar_split_clause,[],[f68,f164])).

fof(f68,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f162,plain,(
    spl9_12 ),
    inference(avatar_split_clause,[],[f69,f160])).

fof(f69,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f158,plain,(
    spl9_11 ),
    inference(avatar_split_clause,[],[f70,f156])).

fof(f70,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f154,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f71,f152])).

fof(f71,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f150,plain,(
    spl9_9 ),
    inference(avatar_split_clause,[],[f72,f148])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f52])).

fof(f146,plain,(
    ~ spl9_8 ),
    inference(avatar_split_clause,[],[f73,f144])).

fof(f73,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f142,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f74,f140])).

fof(f74,plain,(
    v1_tsep_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f138,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f75,f136])).

fof(f75,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f134,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f76,f132])).

fof(f76,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f130,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f77,f128])).

fof(f77,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f52])).

fof(f126,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f78,f124])).

fof(f78,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f52])).

fof(f122,plain,
    ( spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f79,f117,f114])).

fof(f79,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f119,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f80,f117,f114])).

fof(f80,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:34:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (9915)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.47  % (9920)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (9918)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (9912)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (9908)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  % (9926)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (9911)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (9923)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.49  % (9912)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  % (9916)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (9917)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  fof(f452,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f119,f122,f126,f130,f134,f138,f142,f146,f150,f154,f158,f162,f166,f170,f174,f178,f182,f198,f203,f232,f238,f246,f247,f253,f282,f291,f304,f315,f339,f369,f372,f420,f427,f430,f443])).
% 0.21/0.49  fof(f443,plain,(
% 0.21/0.49    spl9_8 | ~spl9_49 | ~spl9_50 | ~spl9_19 | ~spl9_3 | ~spl9_4 | ~spl9_51),
% 0.21/0.49    inference(avatar_split_clause,[],[f439,f418,f128,f124,f201,f415,f412,f144])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    spl9_8 <=> v2_struct_0(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.21/0.49  fof(f412,plain,(
% 0.21/0.49    spl9_49 <=> v2_pre_topc(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).
% 0.21/0.49  fof(f415,plain,(
% 0.21/0.49    spl9_50 <=> l1_pre_topc(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).
% 0.21/0.49  fof(f201,plain,(
% 0.21/0.49    spl9_19 <=> m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    spl9_3 <=> sK4 = sK5),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    spl9_4 <=> m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.49  fof(f418,plain,(
% 0.21/0.49    spl9_51 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X1,sK3,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_51])])).
% 0.21/0.49  fof(f439,plain,(
% 0.21/0.49    ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_3 | ~spl9_4 | ~spl9_51)),
% 0.21/0.49    inference(resolution,[],[f434,f104])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_connsp_2(sK8(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_connsp_2(sK8(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f42,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : m1_connsp_2(X2,X0,X1) => m1_connsp_2(sK8(X0,X1),X0,X1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).
% 0.21/0.49  fof(f434,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK4)) ) | (~spl9_3 | ~spl9_4 | ~spl9_51)),
% 0.21/0.49    inference(forward_demodulation,[],[f431,f125])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    sK4 = sK5 | ~spl9_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f124])).
% 0.21/0.49  fof(f431,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5)) ) | (~spl9_4 | ~spl9_51)),
% 0.21/0.49    inference(resolution,[],[f419,f129])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    m1_subset_1(sK5,u1_struct_0(sK3)) | ~spl9_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f128])).
% 0.21/0.49  fof(f419,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X1,sK3,X0)) ) | ~spl9_51),
% 0.21/0.49    inference(avatar_component_clause,[],[f418])).
% 0.21/0.49  fof(f430,plain,(
% 0.21/0.49    ~spl9_12 | ~spl9_6 | spl9_50),
% 0.21/0.49    inference(avatar_split_clause,[],[f429,f415,f136,f160])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    spl9_12 <=> l1_pre_topc(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    spl9_6 <=> m1_pre_topc(sK3,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.21/0.49  fof(f429,plain,(
% 0.21/0.49    ~l1_pre_topc(sK1) | (~spl9_6 | spl9_50)),
% 0.21/0.49    inference(resolution,[],[f428,f137])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    m1_pre_topc(sK3,sK1) | ~spl9_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f136])).
% 0.21/0.49  fof(f428,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0)) ) | spl9_50),
% 0.21/0.49    inference(resolution,[],[f416,f81])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.49  fof(f416,plain,(
% 0.21/0.49    ~l1_pre_topc(sK3) | spl9_50),
% 0.21/0.49    inference(avatar_component_clause,[],[f415])).
% 0.21/0.49  fof(f427,plain,(
% 0.21/0.49    ~spl9_13 | ~spl9_12 | ~spl9_6 | spl9_49),
% 0.21/0.49    inference(avatar_split_clause,[],[f426,f412,f136,f160,f164])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    spl9_13 <=> v2_pre_topc(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 0.21/0.49  fof(f426,plain,(
% 0.21/0.49    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl9_6 | spl9_49)),
% 0.21/0.49    inference(resolution,[],[f425,f137])).
% 0.21/0.49  fof(f425,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | spl9_49),
% 0.21/0.49    inference(resolution,[],[f413,f98])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.21/0.49  fof(f413,plain,(
% 0.21/0.49    ~v2_pre_topc(sK3) | spl9_49),
% 0.21/0.49    inference(avatar_component_clause,[],[f412])).
% 0.21/0.49  fof(f420,plain,(
% 0.21/0.49    ~spl9_49 | spl9_8 | ~spl9_50 | spl9_51 | ~spl9_44),
% 0.21/0.49    inference(avatar_split_clause,[],[f410,f367,f418,f415,f144,f412])).
% 0.21/0.49  fof(f367,plain,(
% 0.21/0.49    spl9_44 <=> ! [X46,X45,X47] : (~l1_pre_topc(X45) | ~m1_subset_1(X46,u1_struct_0(X45)) | ~m1_connsp_2(X47,X45,X46) | ~m1_subset_1(sK6(X45,X46,X47),k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(X45) | ~v2_pre_topc(X45))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).
% 0.21/0.49  fof(f410,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X1,sK3,X0) | ~l1_pre_topc(sK3) | v2_struct_0(sK3) | ~v2_pre_topc(sK3)) ) | ~spl9_44),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f408])).
% 0.21/0.49  fof(f408,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X1,sK3,X0) | ~l1_pre_topc(sK3) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~m1_connsp_2(X1,sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl9_44),
% 0.21/0.49    inference(resolution,[],[f368,f184])).
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f83,f103])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK6(X0,X1,X2)) & r1_tarski(sK6(X0,X1,X2),X2) & v3_pre_topc(sK6(X0,X1,X2),X0) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f54,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK6(X0,X1,X2)) & r1_tarski(sK6(X0,X1,X2),X2) & v3_pre_topc(sK6(X0,X1,X2),X0) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(rectify,[],[f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_connsp_2)).
% 0.21/0.49  fof(f368,plain,(
% 0.21/0.49    ( ! [X47,X45,X46] : (~m1_subset_1(sK6(X45,X46,X47),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X46,u1_struct_0(X45)) | ~m1_connsp_2(X47,X45,X46) | ~l1_pre_topc(X45) | v2_struct_0(X45) | ~v2_pre_topc(X45)) ) | ~spl9_44),
% 0.21/0.49    inference(avatar_component_clause,[],[f367])).
% 0.21/0.49  % (9906)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  fof(f372,plain,(
% 0.21/0.49    ~spl9_13 | ~spl9_12 | ~spl9_25 | ~spl9_7 | ~spl9_6 | spl9_38),
% 0.21/0.49    inference(avatar_split_clause,[],[f370,f337,f136,f140,f277,f160,f164])).
% 0.21/0.49  fof(f277,plain,(
% 0.21/0.49    spl9_25 <=> m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    spl9_7 <=> v1_tsep_1(sK3,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.21/0.49  fof(f337,plain,(
% 0.21/0.49    spl9_38 <=> v3_pre_topc(u1_struct_0(sK3),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).
% 0.21/0.49  fof(f370,plain,(
% 0.21/0.49    ~m1_pre_topc(sK3,sK1) | ~v1_tsep_1(sK3,sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | spl9_38),
% 0.21/0.49    inference(resolution,[],[f338,f112])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f111])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f99])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.21/0.49  fof(f338,plain,(
% 0.21/0.49    ~v3_pre_topc(u1_struct_0(sK3),sK1) | spl9_38),
% 0.21/0.49    inference(avatar_component_clause,[],[f337])).
% 0.21/0.49  fof(f369,plain,(
% 0.21/0.49    ~spl9_19 | spl9_44 | spl9_30),
% 0.21/0.49    inference(avatar_split_clause,[],[f345,f302,f367,f201])).
% 0.21/0.49  fof(f302,plain,(
% 0.21/0.49    spl9_30 <=> r2_hidden(sK4,u1_struct_0(sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).
% 0.21/0.49  fof(f345,plain,(
% 0.21/0.49    ( ! [X47,X45,X46] : (~l1_pre_topc(X45) | ~v2_pre_topc(X45) | v2_struct_0(X45) | ~m1_subset_1(sK6(X45,X46,X47),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_connsp_2(X47,X45,X46) | ~m1_subset_1(X46,u1_struct_0(X45)) | ~m1_subset_1(sK4,u1_struct_0(sK3))) ) | spl9_30),
% 0.21/0.49    inference(resolution,[],[f303,f208])).
% 0.21/0.49  fof(f208,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X4,X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_subset_1(sK6(X1,X0,X2),k1_zfmisc_1(X3)) | ~m1_connsp_2(X2,X1,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X4,X3)) )),
% 0.21/0.49    inference(resolution,[],[f207,f102])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_xboole_0(X1) | r2_hidden(X0,X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.49  fof(f207,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v1_xboole_0(X3) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_subset_1(sK6(X1,X2,X0),k1_zfmisc_1(X3)) | ~m1_connsp_2(X0,X1,X2)) )),
% 0.21/0.49    inference(resolution,[],[f187,f105])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(X1,sK6(X0,X1,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f86,f103])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(X1,sK6(X0,X1,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f56])).
% 0.21/0.49  fof(f303,plain,(
% 0.21/0.49    ~r2_hidden(sK4,u1_struct_0(sK3)) | spl9_30),
% 0.21/0.49    inference(avatar_component_clause,[],[f302])).
% 0.21/0.49  fof(f339,plain,(
% 0.21/0.49    spl9_14 | ~spl9_13 | ~spl9_12 | ~spl9_25 | ~spl9_5 | ~spl9_38 | ~spl9_30 | spl9_32),
% 0.21/0.49    inference(avatar_split_clause,[],[f331,f313,f302,f337,f132,f277,f160,f164,f168])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    spl9_14 <=> v2_struct_0(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    spl9_5 <=> m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.21/0.49  fof(f313,plain,(
% 0.21/0.49    spl9_32 <=> m1_connsp_2(u1_struct_0(sK3),sK1,sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).
% 0.21/0.49  fof(f331,plain,(
% 0.21/0.49    ~r2_hidden(sK4,u1_struct_0(sK3)) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl9_32),
% 0.21/0.49    inference(resolution,[],[f314,f93])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).
% 0.21/0.49  fof(f314,plain,(
% 0.21/0.49    ~m1_connsp_2(u1_struct_0(sK3),sK1,sK4) | spl9_32),
% 0.21/0.49    inference(avatar_component_clause,[],[f313])).
% 0.21/0.49  fof(f315,plain,(
% 0.21/0.49    spl9_14 | ~spl9_13 | ~spl9_12 | ~spl9_5 | ~spl9_32 | spl9_29),
% 0.21/0.49    inference(avatar_split_clause,[],[f309,f299,f313,f132,f160,f164,f168])).
% 0.21/0.49  fof(f299,plain,(
% 0.21/0.49    spl9_29 <=> m1_connsp_2(sK7(sK1,sK4,u1_struct_0(sK3)),sK1,sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).
% 0.21/0.49  fof(f309,plain,(
% 0.21/0.49    ~m1_connsp_2(u1_struct_0(sK3),sK1,sK4) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl9_29),
% 0.21/0.49    inference(resolution,[],[f300,f190])).
% 0.21/0.49  fof(f190,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_connsp_2(sK7(X0,X1,X2),X0,X1) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f90,f103])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_connsp_2(sK7(X0,X1,X2),X0,X1) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(sK7(X0,X1,X2),X2) & v3_pre_topc(sK7(X0,X1,X2),X0) & m1_connsp_2(sK7(X0,X1,X2),X0,X1) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK7(X0,X1,X2))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f24,f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => (r1_tarski(sK7(X0,X1,X2),X2) & v3_pre_topc(sK7(X0,X1,X2),X0) & m1_connsp_2(sK7(X0,X1,X2),X0,X1) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK7(X0,X1,X2))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : ((r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1)) & (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_connsp_2)).
% 0.21/0.49  fof(f300,plain,(
% 0.21/0.49    ~m1_connsp_2(sK7(sK1,sK4,u1_struct_0(sK3)),sK1,sK4) | spl9_29),
% 0.21/0.49    inference(avatar_component_clause,[],[f299])).
% 0.21/0.49  fof(f304,plain,(
% 0.21/0.49    ~spl9_29 | ~spl9_30 | ~spl9_5 | ~spl9_26),
% 0.21/0.49    inference(avatar_split_clause,[],[f296,f280,f132,f302,f299])).
% 0.21/0.49  fof(f280,plain,(
% 0.21/0.49    spl9_26 <=> ! [X0] : (~r2_hidden(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_connsp_2(sK7(sK1,X0,u1_struct_0(sK3)),sK1,sK4))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 0.21/0.49  fof(f296,plain,(
% 0.21/0.49    ~r2_hidden(sK4,u1_struct_0(sK3)) | ~m1_connsp_2(sK7(sK1,sK4,u1_struct_0(sK3)),sK1,sK4) | (~spl9_5 | ~spl9_26)),
% 0.21/0.49    inference(resolution,[],[f281,f133])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    m1_subset_1(sK4,u1_struct_0(sK1)) | ~spl9_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f132])).
% 0.21/0.49  fof(f281,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(X0,u1_struct_0(sK3)) | ~m1_connsp_2(sK7(sK1,X0,u1_struct_0(sK3)),sK1,sK4)) ) | ~spl9_26),
% 0.21/0.49    inference(avatar_component_clause,[],[f280])).
% 0.21/0.49  fof(f291,plain,(
% 0.21/0.49    ~spl9_12 | ~spl9_6 | spl9_25),
% 0.21/0.49    inference(avatar_split_clause,[],[f289,f277,f136,f160])).
% 0.21/0.49  fof(f289,plain,(
% 0.21/0.49    ~m1_pre_topc(sK3,sK1) | ~l1_pre_topc(sK1) | spl9_25),
% 0.21/0.49    inference(resolution,[],[f278,f82])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.49  fof(f278,plain,(
% 0.21/0.49    ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | spl9_25),
% 0.21/0.49    inference(avatar_component_clause,[],[f277])).
% 0.21/0.49  fof(f282,plain,(
% 0.21/0.49    ~spl9_6 | ~spl9_25 | spl9_26 | spl9_14 | ~spl9_13 | ~spl9_12 | ~spl9_7 | ~spl9_22),
% 0.21/0.49    inference(avatar_split_clause,[],[f275,f244,f140,f160,f164,f168,f280,f277,f136])).
% 0.21/0.49  fof(f244,plain,(
% 0.21/0.49    spl9_22 <=> ! [X0] : (~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK4))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 0.21/0.49  fof(f275,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r2_hidden(X0,u1_struct_0(sK3)) | ~m1_connsp_2(sK7(sK1,X0,u1_struct_0(sK3)),sK1,sK4) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,u1_struct_0(sK1))) ) | (~spl9_7 | ~spl9_22)),
% 0.21/0.49    inference(resolution,[],[f274,f141])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    v1_tsep_1(sK3,sK1) | ~spl9_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f140])).
% 0.21/0.49  fof(f274,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_tsep_1(sK3,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~r2_hidden(X0,u1_struct_0(sK3)) | ~m1_connsp_2(sK7(X1,X0,u1_struct_0(sK3)),sK1,sK4) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(sK3,X1) | ~m1_subset_1(X0,u1_struct_0(X1))) ) | ~spl9_22),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f273])).
% 0.21/0.50  fof(f273,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~r2_hidden(X0,u1_struct_0(sK3)) | ~m1_connsp_2(sK7(X1,X0,u1_struct_0(sK3)),sK1,sK4) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(sK3,X1) | ~v1_tsep_1(sK3,X1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) ) | ~spl9_22),
% 0.21/0.50    inference(resolution,[],[f270,f112])).
% 0.21/0.50  fof(f270,plain,(
% 0.21/0.50    ( ! [X4,X3] : (~v3_pre_topc(u1_struct_0(sK3),X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~r2_hidden(X4,u1_struct_0(sK3)) | ~m1_connsp_2(sK7(X3,X4,u1_struct_0(sK3)),sK1,sK4) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X3)))) ) | ~spl9_22),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f269])).
% 0.21/0.50  fof(f269,plain,(
% 0.21/0.50    ( ! [X4,X3] : (~m1_connsp_2(sK7(X3,X4,u1_struct_0(sK3)),sK1,sK4) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~r2_hidden(X4,u1_struct_0(sK3)) | ~v3_pre_topc(u1_struct_0(sK3),X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X3))) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) ) | ~spl9_22),
% 0.21/0.50    inference(resolution,[],[f257,f93])).
% 0.21/0.50  fof(f257,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~m1_connsp_2(u1_struct_0(sK3),X2,X3) | ~m1_connsp_2(sK7(X2,X3,u1_struct_0(sK3)),sK1,sK4) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl9_22),
% 0.21/0.50    inference(resolution,[],[f245,f192])).
% 0.21/0.50  fof(f192,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_tarski(sK7(X0,X1,X2),X2) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f92,f103])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_tarski(sK7(X0,X1,X2),X2) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f58])).
% 0.21/0.50  fof(f245,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK4)) ) | ~spl9_22),
% 0.21/0.50    inference(avatar_component_clause,[],[f244])).
% 0.21/0.50  fof(f253,plain,(
% 0.21/0.50    spl9_17 | ~spl9_16 | ~spl9_15 | spl9_14 | ~spl9_13 | ~spl9_12 | ~spl9_11 | ~spl9_10 | ~spl9_9 | spl9_8 | ~spl9_6 | ~spl9_5 | ~spl9_19 | ~spl9_1 | spl9_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f249,f196,f114,f201,f132,f136,f144,f148,f152,f156,f160,f164,f168,f172,f176,f180])).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    spl9_17 <=> v2_struct_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 0.21/0.50  fof(f176,plain,(
% 0.21/0.50    spl9_16 <=> v2_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.21/0.50  fof(f172,plain,(
% 0.21/0.50    spl9_15 <=> l1_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    spl9_11 <=> v1_funct_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    spl9_10 <=> v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    spl9_9 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    spl9_1 <=> r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.50  fof(f196,plain,(
% 0.21/0.50    spl9_18 <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 0.21/0.50  fof(f249,plain,(
% 0.21/0.50    ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl9_18),
% 0.21/0.50    inference(resolution,[],[f242,f106])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f94])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).
% 0.21/0.50  fof(f242,plain,(
% 0.21/0.50    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | spl9_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f196])).
% 0.21/0.50  fof(f247,plain,(
% 0.21/0.50    sK4 != sK5 | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f246,plain,(
% 0.21/0.50    spl9_8 | ~spl9_19 | ~spl9_18 | spl9_22 | ~spl9_6 | ~spl9_21),
% 0.21/0.50    inference(avatar_split_clause,[],[f239,f236,f136,f244,f196,f201,f144])).
% 0.21/0.50  fof(f236,plain,(
% 0.21/0.50    spl9_21 <=> ! [X1,X0] : (~m1_connsp_2(X0,sK1,sK4) | ~r1_tarski(X0,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),sK4) | ~m1_subset_1(sK4,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 0.21/0.50  fof(f239,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK4) | v2_struct_0(sK3)) ) | (~spl9_6 | ~spl9_21)),
% 0.21/0.50    inference(resolution,[],[f237,f137])).
% 0.21/0.50  fof(f237,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,sK1) | ~r1_tarski(X0,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),sK4) | ~m1_subset_1(sK4,u1_struct_0(X1)) | ~m1_connsp_2(X0,sK1,sK4) | v2_struct_0(X1)) ) | ~spl9_21),
% 0.21/0.50    inference(avatar_component_clause,[],[f236])).
% 0.21/0.50  fof(f238,plain,(
% 0.21/0.50    ~spl9_5 | spl9_21 | spl9_1 | ~spl9_20),
% 0.21/0.50    inference(avatar_split_clause,[],[f233,f230,f114,f236,f132])).
% 0.21/0.50  fof(f230,plain,(
% 0.21/0.50    spl9_20 <=> ! [X1,X0,X2] : (~m1_connsp_2(X0,sK1,X1) | r1_tmap_1(sK1,sK0,sK2,X1) | ~r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~r1_tarski(X0,u1_struct_0(X2)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 0.21/0.50  fof(f233,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_connsp_2(X0,sK1,sK4) | ~r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),sK4) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(X1)) | ~r1_tarski(X0,u1_struct_0(X1))) ) | (spl9_1 | ~spl9_20)),
% 0.21/0.50    inference(resolution,[],[f231,f115])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    ~r1_tmap_1(sK1,sK0,sK2,sK4) | spl9_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f114])).
% 0.21/0.50  fof(f231,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_tmap_1(sK1,sK0,sK2,X1) | ~m1_connsp_2(X0,sK1,X1) | ~r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~r1_tarski(X0,u1_struct_0(X2))) ) | ~spl9_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f230])).
% 0.21/0.50  fof(f232,plain,(
% 0.21/0.50    spl9_17 | ~spl9_16 | ~spl9_15 | spl9_14 | ~spl9_13 | ~spl9_12 | ~spl9_9 | spl9_20 | ~spl9_10 | ~spl9_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f221,f156,f152,f230,f148,f160,f164,f168,f172,f176,f180])).
% 0.21/0.50  fof(f221,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_connsp_2(X0,sK1,X1) | ~r1_tarski(X0,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_pre_topc(X2,sK1) | v2_struct_0(X2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1) | r1_tmap_1(sK1,sK0,sK2,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl9_10 | ~spl9_11)),
% 0.21/0.50    inference(resolution,[],[f220,f153])).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~spl9_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f152])).
% 0.21/0.50  fof(f220,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(sK2,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_connsp_2(X4,X2,X3) | ~r1_tarski(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3) | r1_tmap_1(X2,X1,sK2,X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl9_11),
% 0.21/0.50    inference(resolution,[],[f193,f157])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    v1_funct_1(sK2) | ~spl9_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f156])).
% 0.21/0.50  fof(f193,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | r1_tmap_1(X1,X0,X2,X6) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f107,f103])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f96])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tmap_1)).
% 0.21/0.50  fof(f203,plain,(
% 0.21/0.50    spl9_19 | ~spl9_3 | ~spl9_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f199,f128,f124,f201])).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    m1_subset_1(sK4,u1_struct_0(sK3)) | (~spl9_3 | ~spl9_4)),
% 0.21/0.50    inference(superposition,[],[f129,f125])).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    spl9_18 | ~spl9_2 | ~spl9_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f194,f124,f117,f196])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    spl9_2 <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | (~spl9_2 | ~spl9_3)),
% 0.21/0.50    inference(forward_demodulation,[],[f121,f125])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~spl9_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f117])).
% 0.21/0.50  fof(f182,plain,(
% 0.21/0.50    ~spl9_17),
% 0.21/0.50    inference(avatar_split_clause,[],[f64,f180])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ~v2_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ((((((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)) & sK4 = sK5 & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK1))) & m1_pre_topc(sK3,sK1) & v1_tsep_1(sK3,sK1) & ~v2_struct_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f45,f51,f50,f49,f48,f47,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | ~r1_tmap_1(X1,sK0,X2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | r1_tmap_1(X1,sK0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | ~r1_tmap_1(X1,sK0,X2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | r1_tmap_1(X1,sK0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5) | ~r1_tmap_1(sK1,sK0,X2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5) | r1_tmap_1(sK1,sK0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(X3,sK1) & v1_tsep_1(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5) | ~r1_tmap_1(sK1,sK0,X2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5) | r1_tmap_1(sK1,sK0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(X3,sK1) & v1_tsep_1(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5) | ~r1_tmap_1(sK1,sK0,sK2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5) | r1_tmap_1(sK1,sK0,sK2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(X3,sK1) & v1_tsep_1(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5) | ~r1_tmap_1(sK1,sK0,sK2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5) | r1_tmap_1(sK1,sK0,sK2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(X3,sK1) & v1_tsep_1(X3,sK1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | ~r1_tmap_1(sK1,sK0,sK2,X4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | r1_tmap_1(sK1,sK0,sK2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(sK3,sK1) & v1_tsep_1(sK3,sK1) & ~v2_struct_0(sK3))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ? [X4] : (? [X5] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | ~r1_tmap_1(sK1,sK0,sK2,X4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | r1_tmap_1(sK1,sK0,sK2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,u1_struct_0(sK1))) => (? [X5] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | r1_tmap_1(sK1,sK0,sK2,sK4)) & sK4 = X5 & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK1)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ? [X5] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | r1_tmap_1(sK1,sK0,sK2,sK4)) & sK4 = X5 & m1_subset_1(X5,u1_struct_0(sK3))) => ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)) & sK4 = sK5 & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4))) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f15])).
% 0.21/0.50  fof(f15,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).
% 0.21/0.50  fof(f178,plain,(
% 0.21/0.50    spl9_16),
% 0.21/0.50    inference(avatar_split_clause,[],[f65,f176])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    v2_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f174,plain,(
% 0.21/0.50    spl9_15),
% 0.21/0.50    inference(avatar_split_clause,[],[f66,f172])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    ~spl9_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f67,f168])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ~v2_struct_0(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    spl9_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f68,f164])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    v2_pre_topc(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    spl9_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f69,f160])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    l1_pre_topc(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    spl9_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f70,f156])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    v1_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    spl9_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f71,f152])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    spl9_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f72,f148])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    ~spl9_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f73,f144])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ~v2_struct_0(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    spl9_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f74,f140])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    v1_tsep_1(sK3,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    spl9_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f75,f136])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    m1_pre_topc(sK3,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    spl9_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f76,f132])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    spl9_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f77,f128])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    spl9_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f78,f124])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    sK4 = sK5),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    spl9_1 | spl9_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f79,f117,f114])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    ~spl9_1 | ~spl9_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f80,f117,f114])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (9912)------------------------------
% 0.21/0.50  % (9912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (9912)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (9912)Memory used [KB]: 11129
% 0.21/0.50  % (9912)Time elapsed: 0.029 s
% 0.21/0.50  % (9912)------------------------------
% 0.21/0.50  % (9912)------------------------------
% 0.21/0.50  % (9903)Success in time 0.142 s
%------------------------------------------------------------------------------
