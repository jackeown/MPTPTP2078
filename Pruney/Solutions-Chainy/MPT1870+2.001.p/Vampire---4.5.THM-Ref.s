%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 252 expanded)
%              Number of leaves         :    9 (  58 expanded)
%              Depth                    :   17
%              Number of atoms          :  499 (1881 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f239,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f112,f123,f175,f236,f238])).

fof(f238,plain,
    ( spl5_4
    | spl5_2 ),
    inference(avatar_split_clause,[],[f237,f76,f100])).

fof(f100,plain,
    ( spl5_4
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0)
        | ~ v2_tex_2(X1,sK0)
        | ~ v3_pre_topc(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f76,plain,
    ( spl5_2
  <=> v3_pre_topc(sK4(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f237,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X1,sK0)
        | ~ v2_tex_2(X1,sK0)
        | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0) )
    | spl5_2 ),
    inference(subsumption_resolution,[],[f67,f77])).

fof(f77,plain,
    ( ~ v3_pre_topc(sK4(sK0),sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f67,plain,(
    ! [X1] :
      ( v3_pre_topc(sK4(sK0),sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | ~ v2_tex_2(X1,sK0)
      | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0) ) ),
    inference(subsumption_resolution,[],[f66,f18])).

fof(f18,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_tex_2(X2,X0)
              & v2_tex_2(X1,X0)
              & v3_pre_topc(X2,X0)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_tex_2(X2,X0)
              & v2_tex_2(X1,X0)
              & v3_pre_topc(X2,X0)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    & v2_tex_2(X1,X0)
                    & v3_pre_topc(X2,X0)
                    & v3_pre_topc(X1,X0) )
                 => v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  & v2_tex_2(X1,X0)
                  & v3_pre_topc(X2,X0)
                  & v3_pre_topc(X1,X0) )
               => v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_tex_2)).

fof(f66,plain,(
    ! [X1] :
      ( v3_pre_topc(sK4(sK0),sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | ~ v2_tex_2(sK1,sK0)
      | ~ v2_tex_2(X1,sK0)
      | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0) ) ),
    inference(subsumption_resolution,[],[f65,f16])).

fof(f16,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f65,plain,(
    ! [X1] :
      ( v3_pre_topc(sK4(sK0),sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(sK1,sK0)
      | ~ v3_pre_topc(X1,sK0)
      | ~ v2_tex_2(sK1,sK0)
      | ~ v2_tex_2(X1,sK0)
      | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0) ) ),
    inference(subsumption_resolution,[],[f61,f24])).

fof(f24,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X1] :
      ( v3_pre_topc(sK4(sK0),sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(sK1,sK0)
      | ~ v3_pre_topc(X1,sK0)
      | ~ v2_tex_2(sK1,sK0)
      | ~ v2_tex_2(X1,sK0)
      | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0) ) ),
    inference(resolution,[],[f27,f21])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X4,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(sK4(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | ~ v3_pre_topc(X4,X0)
      | ~ v2_tex_2(X3,X0)
      | ~ v2_tex_2(X4,X0)
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X3] :
          ( ! [X4] :
              ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0)
              | ~ v2_tex_2(X4,X0)
              | ~ v2_tex_2(X3,X0)
              | ~ v3_pre_topc(X4,X0)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
      | ? [X1] :
          ( ? [X2] :
              ( ( ~ v3_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                | ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) )
              & v3_pre_topc(X2,X0)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X3] :
          ( ! [X4] :
              ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0)
              | ~ v2_tex_2(X4,X0)
              | ~ v2_tex_2(X3,X0)
              | ~ v3_pre_topc(X4,X0)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
      | ? [X1] :
          ( ? [X2] :
              ( ( ~ v3_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                | ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) )
              & v3_pre_topc(X2,X0)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & v3_pre_topc(X1,X0) )
                 => ( v3_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                    & v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) )
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X4,X0)
                    & v2_tex_2(X3,X0)
                    & v3_pre_topc(X4,X0)
                    & v3_pre_topc(X3,X0) )
                 => v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0) ) ) ) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & v3_pre_topc(X1,X0) )
                 => ( v3_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                    & v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    & v2_tex_2(X1,X0)
                    & v3_pre_topc(X2,X0)
                    & v3_pre_topc(X1,X0) )
                 => v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tex_2)).

fof(f236,plain,
    ( spl5_4
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f235,f172,f109,f89,f76,f100])).

fof(f89,plain,
    ( spl5_3
  <=> v3_pre_topc(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f109,plain,
    ( spl5_5
  <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f172,plain,
    ( spl5_8
  <=> m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f235,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ v2_tex_2(X0,sK0)
        | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X0),sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f234,f18])).

fof(f234,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ v2_tex_2(sK1,sK0)
        | ~ v2_tex_2(X0,sK0)
        | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X0),sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f230,f16])).

fof(f230,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK1,sK0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ v2_tex_2(sK1,sK0)
        | ~ v2_tex_2(X0,sK0)
        | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X0),sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(resolution,[],[f204,f21])).

fof(f204,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ v3_pre_topc(X1,sK0)
        | ~ v2_tex_2(X0,sK0)
        | ~ v2_tex_2(X1,sK0)
        | v2_tex_2(k4_subset_1(u1_struct_0(sK0),X0,X1),sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f203,f194])).

fof(f194,plain,
    ( v3_pre_topc(k4_subset_1(u1_struct_0(sK0),sK3(sK0),sK4(sK0)),sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f181,f78])).

fof(f78,plain,
    ( v3_pre_topc(sK4(sK0),sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f181,plain,
    ( ~ v3_pre_topc(sK4(sK0),sK0)
    | v3_pre_topc(k4_subset_1(u1_struct_0(sK0),sK3(sK0),sK4(sK0)),sK0)
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(resolution,[],[f174,f146])).

fof(f146,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X4,sK0)
        | v3_pre_topc(k4_subset_1(u1_struct_0(sK0),sK3(sK0),X4),sK0) )
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f145,f91])).

fof(f91,plain,
    ( v3_pre_topc(sK3(sK0),sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f145,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK3(sK0),sK0)
        | ~ v3_pre_topc(X4,sK0)
        | v3_pre_topc(k4_subset_1(u1_struct_0(sK0),sK3(sK0),X4),sK0) )
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f144,f23])).

fof(f23,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f144,plain,
    ( ! [X4] :
        ( ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK3(sK0),sK0)
        | ~ v3_pre_topc(X4,sK0)
        | v3_pre_topc(k4_subset_1(u1_struct_0(sK0),sK3(sK0),X4),sK0) )
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f135,f24])).

fof(f135,plain,
    ( ! [X4] :
        ( ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK3(sK0),sK0)
        | ~ v3_pre_topc(X4,sK0)
        | v3_pre_topc(k4_subset_1(u1_struct_0(sK0),sK3(sK0),X4),sK0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f111,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | v3_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v3_pre_topc(X2,X0)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v3_pre_topc(X2,X0)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v3_pre_topc(X2,X0)
                  & v3_pre_topc(X1,X0) )
               => v3_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_tops_1)).

fof(f111,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f109])).

fof(f174,plain,
    ( m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f172])).

fof(f203,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(k4_subset_1(u1_struct_0(sK0),sK3(sK0),sK4(sK0)),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ v3_pre_topc(X1,sK0)
        | ~ v2_tex_2(X0,sK0)
        | ~ v2_tex_2(X1,sK0)
        | v2_tex_2(k4_subset_1(u1_struct_0(sK0),X0,X1),sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f202,f24])).

fof(f202,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ v3_pre_topc(k4_subset_1(u1_struct_0(sK0),sK3(sK0),sK4(sK0)),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ v3_pre_topc(X1,sK0)
        | ~ v2_tex_2(X0,sK0)
        | ~ v2_tex_2(X1,sK0)
        | v2_tex_2(k4_subset_1(u1_struct_0(sK0),X0,X1),sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(resolution,[],[f195,f25])).

fof(f25,plain,(
    ! [X4,X0,X3] :
      ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(k4_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | ~ v3_pre_topc(X4,X0)
      | ~ v2_tex_2(X3,X0)
      | ~ v2_tex_2(X4,X0)
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f195,plain,
    ( v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK3(sK0),sK4(sK0)),sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f182,f78])).

fof(f182,plain,
    ( ~ v3_pre_topc(sK4(sK0),sK0)
    | v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK3(sK0),sK4(sK0)),sK0)
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(resolution,[],[f174,f149])).

fof(f149,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X5,sK0)
        | v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK3(sK0),X5),sK0) )
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f148,f91])).

fof(f148,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK3(sK0),sK0)
        | ~ v3_pre_topc(X5,sK0)
        | v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK3(sK0),X5),sK0) )
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f147,f23])).

fof(f147,plain,
    ( ! [X5] :
        ( ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK3(sK0),sK0)
        | ~ v3_pre_topc(X5,sK0)
        | v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK3(sK0),X5),sK0) )
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f136,f24])).

fof(f136,plain,
    ( ! [X5] :
        ( ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK3(sK0),sK0)
        | ~ v3_pre_topc(X5,sK0)
        | v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK3(sK0),X5),sK0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f111,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v3_pre_topc(X2,X0)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v3_pre_topc(X2,X0)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v3_pre_topc(X2,X0)
                  & v3_pre_topc(X1,X0) )
               => v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_tops_1)).

fof(f175,plain,
    ( spl5_4
    | spl5_8 ),
    inference(avatar_split_clause,[],[f117,f172,f100])).

fof(f117,plain,(
    ! [X1] :
      ( m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | ~ v2_tex_2(X1,sK0)
      | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0) ) ),
    inference(subsumption_resolution,[],[f116,f18])).

fof(f116,plain,(
    ! [X1] :
      ( m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | ~ v2_tex_2(sK1,sK0)
      | ~ v2_tex_2(X1,sK0)
      | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0) ) ),
    inference(subsumption_resolution,[],[f115,f16])).

fof(f115,plain,(
    ! [X1] :
      ( m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(sK1,sK0)
      | ~ v3_pre_topc(X1,sK0)
      | ~ v2_tex_2(sK1,sK0)
      | ~ v2_tex_2(X1,sK0)
      | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0) ) ),
    inference(subsumption_resolution,[],[f114,f24])).

fof(f114,plain,(
    ! [X1] :
      ( m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(sK1,sK0)
      | ~ v3_pre_topc(X1,sK0)
      | ~ v2_tex_2(sK1,sK0)
      | ~ v2_tex_2(X1,sK0)
      | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0) ) ),
    inference(resolution,[],[f29,f21])).

fof(f29,plain,(
    ! [X4,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | ~ v3_pre_topc(X4,X0)
      | ~ v2_tex_2(X3,X0)
      | ~ v2_tex_2(X4,X0)
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f123,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f121,f17])).

fof(f17,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f121,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f120,f19])).

fof(f19,plain,(
    v2_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f120,plain,
    ( ~ v2_tex_2(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f118,f20])).

fof(f20,plain,(
    ~ v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f118,plain,
    ( v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ v2_tex_2(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f101,f15])).

fof(f15,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f101,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0)
        | ~ v2_tex_2(X1,sK0)
        | ~ v3_pre_topc(X1,sK0) )
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f112,plain,
    ( spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f107,f109,f100])).

fof(f107,plain,(
    ! [X1] :
      ( m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | ~ v2_tex_2(X1,sK0)
      | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0) ) ),
    inference(subsumption_resolution,[],[f106,f18])).

fof(f106,plain,(
    ! [X1] :
      ( m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | ~ v2_tex_2(sK1,sK0)
      | ~ v2_tex_2(X1,sK0)
      | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0) ) ),
    inference(subsumption_resolution,[],[f105,f16])).

fof(f105,plain,(
    ! [X1] :
      ( m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(sK1,sK0)
      | ~ v3_pre_topc(X1,sK0)
      | ~ v2_tex_2(sK1,sK0)
      | ~ v2_tex_2(X1,sK0)
      | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0) ) ),
    inference(subsumption_resolution,[],[f104,f24])).

fof(f104,plain,(
    ! [X1] :
      ( m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(sK1,sK0)
      | ~ v3_pre_topc(X1,sK0)
      | ~ v2_tex_2(sK1,sK0)
      | ~ v2_tex_2(X1,sK0)
      | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0) ) ),
    inference(resolution,[],[f26,f21])).

fof(f26,plain,(
    ! [X4,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | ~ v3_pre_topc(X4,X0)
      | ~ v2_tex_2(X3,X0)
      | ~ v2_tex_2(X4,X0)
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f102,plain,
    ( spl5_4
    | spl5_3 ),
    inference(avatar_split_clause,[],[f87,f89,f100])).

fof(f87,plain,(
    ! [X1] :
      ( v3_pre_topc(sK3(sK0),sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | ~ v2_tex_2(X1,sK0)
      | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0) ) ),
    inference(subsumption_resolution,[],[f86,f18])).

fof(f86,plain,(
    ! [X1] :
      ( v3_pre_topc(sK3(sK0),sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | ~ v2_tex_2(sK1,sK0)
      | ~ v2_tex_2(X1,sK0)
      | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0) ) ),
    inference(subsumption_resolution,[],[f85,f16])).

fof(f85,plain,(
    ! [X1] :
      ( v3_pre_topc(sK3(sK0),sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(sK1,sK0)
      | ~ v3_pre_topc(X1,sK0)
      | ~ v2_tex_2(sK1,sK0)
      | ~ v2_tex_2(X1,sK0)
      | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0) ) ),
    inference(subsumption_resolution,[],[f81,f24])).

fof(f81,plain,(
    ! [X1] :
      ( v3_pre_topc(sK3(sK0),sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(sK1,sK0)
      | ~ v3_pre_topc(X1,sK0)
      | ~ v2_tex_2(sK1,sK0)
      | ~ v2_tex_2(X1,sK0)
      | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0) ) ),
    inference(resolution,[],[f28,f21])).

fof(f28,plain,(
    ! [X4,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(sK3(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | ~ v3_pre_topc(X4,X0)
      | ~ v2_tex_2(X3,X0)
      | ~ v2_tex_2(X4,X0)
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0) ) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:48:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (25091)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.47  % (25092)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.47  % (25099)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.47  % (25092)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (25100)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f239,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f102,f112,f123,f175,f236,f238])).
% 0.21/0.48  fof(f238,plain,(
% 0.21/0.48    spl5_4 | spl5_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f237,f76,f100])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    spl5_4 <=> ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0) | ~v2_tex_2(X1,sK0) | ~v3_pre_topc(X1,sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    spl5_2 <=> v3_pre_topc(sK4(sK0),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.48  fof(f237,plain,(
% 0.21/0.48    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | ~v2_tex_2(X1,sK0) | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0)) ) | spl5_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f67,f77])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    ~v3_pre_topc(sK4(sK0),sK0) | spl5_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f76])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X1] : (v3_pre_topc(sK4(sK0),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | ~v2_tex_2(X1,sK0) | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f66,f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    v2_tex_2(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_tex_2(X2,X0) & v2_tex_2(X1,X0) & v3_pre_topc(X2,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) & v2_tex_2(X1,X0) & v3_pre_topc(X2,X0) & v3_pre_topc(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) & v2_tex_2(X1,X0) & v3_pre_topc(X2,X0) & v3_pre_topc(X1,X0)) => v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f4])).
% 0.21/0.48  fof(f4,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) & v2_tex_2(X1,X0) & v3_pre_topc(X2,X0) & v3_pre_topc(X1,X0)) => v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_tex_2)).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X1] : (v3_pre_topc(sK4(sK0),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | ~v2_tex_2(sK1,sK0) | ~v2_tex_2(X1,sK0) | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f65,f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    v3_pre_topc(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X1] : (v3_pre_topc(sK4(sK0),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0) | ~v3_pre_topc(X1,sK0) | ~v2_tex_2(sK1,sK0) | ~v2_tex_2(X1,sK0) | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f61,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X1] : (v3_pre_topc(sK4(sK0),sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0) | ~v3_pre_topc(X1,sK0) | ~v2_tex_2(sK1,sK0) | ~v2_tex_2(X1,sK0) | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0)) )),
% 0.21/0.48    inference(resolution,[],[f27,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X4,X0,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(sK4(X0),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X3,X0) | ~v3_pre_topc(X4,X0) | ~v2_tex_2(X3,X0) | ~v2_tex_2(X4,X0) | v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : (! [X3] : (! [X4] : (v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0) | ~v2_tex_2(X4,X0) | ~v2_tex_2(X3,X0) | ~v3_pre_topc(X4,X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X1] : (? [X2] : ((~v3_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)) & v3_pre_topc(X2,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0] : ((! [X3] : (! [X4] : ((v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0) | (~v2_tex_2(X4,X0) | ~v2_tex_2(X3,X0) | ~v3_pre_topc(X4,X0) | ~v3_pre_topc(X3,X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X1] : (? [X2] : (((~v3_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)) & (v3_pre_topc(X2,X0) & v3_pre_topc(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v3_pre_topc(X1,X0)) => (v3_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0))))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X4,X0) & v2_tex_2(X3,X0) & v3_pre_topc(X4,X0) & v3_pre_topc(X3,X0)) => v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0))))))),
% 0.21/0.48    inference(rectify,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v3_pre_topc(X1,X0)) => (v3_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0))))) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) & v2_tex_2(X1,X0) & v3_pre_topc(X2,X0) & v3_pre_topc(X1,X0)) => v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tex_2)).
% 0.21/0.48  fof(f236,plain,(
% 0.21/0.48    spl5_4 | ~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f235,f172,f109,f89,f76,f100])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    spl5_3 <=> v3_pre_topc(sK3(sK0),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    spl5_5 <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.48  fof(f172,plain,(
% 0.21/0.48    spl5_8 <=> m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.48  fof(f235,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~v2_tex_2(X0,sK0) | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X0),sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f234,f18])).
% 0.21/0.48  fof(f234,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~v2_tex_2(sK1,sK0) | ~v2_tex_2(X0,sK0) | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X0),sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f230,f16])).
% 0.21/0.48  fof(f230,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0) | ~v3_pre_topc(X0,sK0) | ~v2_tex_2(sK1,sK0) | ~v2_tex_2(X0,sK0) | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X0),sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_8)),
% 0.21/0.48    inference(resolution,[],[f204,f21])).
% 0.21/0.48  fof(f204,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~v3_pre_topc(X1,sK0) | ~v2_tex_2(X0,sK0) | ~v2_tex_2(X1,sK0) | v2_tex_2(k4_subset_1(u1_struct_0(sK0),X0,X1),sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f203,f194])).
% 0.21/0.48  fof(f194,plain,(
% 0.21/0.48    v3_pre_topc(k4_subset_1(u1_struct_0(sK0),sK3(sK0),sK4(sK0)),sK0) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f181,f78])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    v3_pre_topc(sK4(sK0),sK0) | ~spl5_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f76])).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    ~v3_pre_topc(sK4(sK0),sK0) | v3_pre_topc(k4_subset_1(u1_struct_0(sK0),sK3(sK0),sK4(sK0)),sK0) | (~spl5_3 | ~spl5_5 | ~spl5_8)),
% 0.21/0.48    inference(resolution,[],[f174,f146])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X4,sK0) | v3_pre_topc(k4_subset_1(u1_struct_0(sK0),sK3(sK0),X4),sK0)) ) | (~spl5_3 | ~spl5_5)),
% 0.21/0.48    inference(subsumption_resolution,[],[f145,f91])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    v3_pre_topc(sK3(sK0),sK0) | ~spl5_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f89])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK3(sK0),sK0) | ~v3_pre_topc(X4,sK0) | v3_pre_topc(k4_subset_1(u1_struct_0(sK0),sK3(sK0),X4),sK0)) ) | ~spl5_5),
% 0.21/0.48    inference(subsumption_resolution,[],[f144,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    ( ! [X4] : (~v2_pre_topc(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK3(sK0),sK0) | ~v3_pre_topc(X4,sK0) | v3_pre_topc(k4_subset_1(u1_struct_0(sK0),sK3(sK0),X4),sK0)) ) | ~spl5_5),
% 0.21/0.48    inference(subsumption_resolution,[],[f135,f24])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    ( ! [X4] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK3(sK0),sK0) | ~v3_pre_topc(X4,sK0) | v3_pre_topc(k4_subset_1(u1_struct_0(sK0),sK3(sK0),X4),sK0)) ) | ~spl5_5),
% 0.21/0.48    inference(resolution,[],[f111,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~v3_pre_topc(X2,X0) | v3_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (v3_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v3_pre_topc(X2,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v3_pre_topc(X2,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v3_pre_topc(X1,X0)) => v3_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_tops_1)).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f109])).
% 0.21/0.48  fof(f174,plain,(
% 0.21/0.48    m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f172])).
% 0.21/0.48  fof(f203,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v3_pre_topc(k4_subset_1(u1_struct_0(sK0),sK3(sK0),sK4(sK0)),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~v3_pre_topc(X1,sK0) | ~v2_tex_2(X0,sK0) | ~v2_tex_2(X1,sK0) | v2_tex_2(k4_subset_1(u1_struct_0(sK0),X0,X1),sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f202,f24])).
% 0.21/0.48  fof(f202,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~l1_pre_topc(sK0) | ~v3_pre_topc(k4_subset_1(u1_struct_0(sK0),sK3(sK0),sK4(sK0)),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~v3_pre_topc(X1,sK0) | ~v2_tex_2(X0,sK0) | ~v2_tex_2(X1,sK0) | v2_tex_2(k4_subset_1(u1_struct_0(sK0),X0,X1),sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_8)),
% 0.21/0.48    inference(resolution,[],[f195,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X4,X0,X3] : (~v3_pre_topc(k9_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),X0) | ~l1_pre_topc(X0) | ~v3_pre_topc(k4_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X3,X0) | ~v3_pre_topc(X4,X0) | ~v2_tex_2(X3,X0) | ~v2_tex_2(X4,X0) | v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f195,plain,(
% 0.21/0.48    v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK3(sK0),sK4(sK0)),sK0) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f182,f78])).
% 0.21/0.48  fof(f182,plain,(
% 0.21/0.48    ~v3_pre_topc(sK4(sK0),sK0) | v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK3(sK0),sK4(sK0)),sK0) | (~spl5_3 | ~spl5_5 | ~spl5_8)),
% 0.21/0.48    inference(resolution,[],[f174,f149])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X5,sK0) | v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK3(sK0),X5),sK0)) ) | (~spl5_3 | ~spl5_5)),
% 0.21/0.48    inference(subsumption_resolution,[],[f148,f91])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK3(sK0),sK0) | ~v3_pre_topc(X5,sK0) | v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK3(sK0),X5),sK0)) ) | ~spl5_5),
% 0.21/0.48    inference(subsumption_resolution,[],[f147,f23])).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    ( ! [X5] : (~v2_pre_topc(sK0) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK3(sK0),sK0) | ~v3_pre_topc(X5,sK0) | v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK3(sK0),X5),sK0)) ) | ~spl5_5),
% 0.21/0.48    inference(subsumption_resolution,[],[f136,f24])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    ( ! [X5] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK3(sK0),sK0) | ~v3_pre_topc(X5,sK0) | v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK3(sK0),X5),sK0)) ) | ~spl5_5),
% 0.21/0.48    inference(resolution,[],[f111,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~v3_pre_topc(X2,X0) | v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v3_pre_topc(X2,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v3_pre_topc(X2,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v3_pre_topc(X1,X0)) => v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_tops_1)).
% 0.21/0.48  fof(f175,plain,(
% 0.21/0.48    spl5_4 | spl5_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f117,f172,f100])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    ( ! [X1] : (m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | ~v2_tex_2(X1,sK0) | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f116,f18])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    ( ! [X1] : (m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | ~v2_tex_2(sK1,sK0) | ~v2_tex_2(X1,sK0) | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f115,f16])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    ( ! [X1] : (m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0) | ~v3_pre_topc(X1,sK0) | ~v2_tex_2(sK1,sK0) | ~v2_tex_2(X1,sK0) | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f114,f24])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    ( ! [X1] : (m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0) | ~v3_pre_topc(X1,sK0) | ~v2_tex_2(sK1,sK0) | ~v2_tex_2(X1,sK0) | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0)) )),
% 0.21/0.48    inference(resolution,[],[f29,f21])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X4,X0,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X3,X0) | ~v3_pre_topc(X4,X0) | ~v2_tex_2(X3,X0) | ~v2_tex_2(X4,X0) | v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    ~spl5_4),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f122])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    $false | ~spl5_4),
% 0.21/0.48    inference(subsumption_resolution,[],[f121,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    v3_pre_topc(sK2,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    ~v3_pre_topc(sK2,sK0) | ~spl5_4),
% 0.21/0.48    inference(subsumption_resolution,[],[f120,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    v2_tex_2(sK2,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    ~v2_tex_2(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | ~spl5_4),
% 0.21/0.48    inference(subsumption_resolution,[],[f118,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ~v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | ~v2_tex_2(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | ~spl5_4),
% 0.21/0.48    inference(resolution,[],[f101,f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0) | ~v2_tex_2(X1,sK0) | ~v3_pre_topc(X1,sK0)) ) | ~spl5_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f100])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    spl5_4 | spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f107,f109,f100])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    ( ! [X1] : (m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | ~v2_tex_2(X1,sK0) | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f106,f18])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    ( ! [X1] : (m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | ~v2_tex_2(sK1,sK0) | ~v2_tex_2(X1,sK0) | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f105,f16])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    ( ! [X1] : (m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0) | ~v3_pre_topc(X1,sK0) | ~v2_tex_2(sK1,sK0) | ~v2_tex_2(X1,sK0) | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f104,f24])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    ( ! [X1] : (m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0) | ~v3_pre_topc(X1,sK0) | ~v2_tex_2(sK1,sK0) | ~v2_tex_2(X1,sK0) | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0)) )),
% 0.21/0.48    inference(resolution,[],[f26,f21])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X4,X0,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X3,X0) | ~v3_pre_topc(X4,X0) | ~v2_tex_2(X3,X0) | ~v2_tex_2(X4,X0) | v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    spl5_4 | spl5_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f87,f89,f100])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ( ! [X1] : (v3_pre_topc(sK3(sK0),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | ~v2_tex_2(X1,sK0) | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f86,f18])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ( ! [X1] : (v3_pre_topc(sK3(sK0),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | ~v2_tex_2(sK1,sK0) | ~v2_tex_2(X1,sK0) | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f85,f16])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ( ! [X1] : (v3_pre_topc(sK3(sK0),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0) | ~v3_pre_topc(X1,sK0) | ~v2_tex_2(sK1,sK0) | ~v2_tex_2(X1,sK0) | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f81,f24])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ( ! [X1] : (v3_pre_topc(sK3(sK0),sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0) | ~v3_pre_topc(X1,sK0) | ~v2_tex_2(sK1,sK0) | ~v2_tex_2(X1,sK0) | v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X1),sK0)) )),
% 0.21/0.48    inference(resolution,[],[f28,f21])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X4,X0,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(sK3(X0),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X3,X0) | ~v3_pre_topc(X4,X0) | ~v2_tex_2(X3,X0) | ~v2_tex_2(X4,X0) | v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (25092)------------------------------
% 0.21/0.48  % (25092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (25092)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (25092)Memory used [KB]: 5500
% 0.21/0.48  % (25092)Time elapsed: 0.057 s
% 0.21/0.48  % (25092)------------------------------
% 0.21/0.48  % (25092)------------------------------
% 0.21/0.48  % (25085)Success in time 0.12 s
%------------------------------------------------------------------------------
