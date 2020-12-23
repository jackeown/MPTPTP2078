%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 341 expanded)
%              Number of leaves         :   21 ( 112 expanded)
%              Depth                    :   75
%              Number of atoms          : 1427 (3423 expanded)
%              Number of equality atoms :    7 (  17 expanded)
%              Maximal formula depth    :   27 (  12 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f262,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f53,f58,f63,f68,f73,f78,f83,f88,f108,f118,f245])).

fof(f245,plain,
    ( spl5_14
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f244,f105,f85,f80,f75,f70,f65,f60,f55,f50,f115])).

fof(f115,plain,
    ( spl5_14
  <=> v2_tex_2(k2_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f50,plain,
    ( spl5_2
  <=> v2_tex_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f55,plain,
    ( spl5_3
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f60,plain,
    ( spl5_4
  <=> v4_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f65,plain,
    ( spl5_5
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f70,plain,
    ( spl5_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f75,plain,
    ( spl5_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f80,plain,
    ( spl5_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f85,plain,
    ( spl5_9
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f105,plain,
    ( spl5_12
  <=> k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f244,plain,
    ( v2_tex_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f235,f107])).

fof(f107,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f105])).

fof(f235,plain,
    ( v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f82,f87,f52,f62,f57,f67,f72,f77,f232])).

fof(f232,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_pre_topc(X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ v2_tex_2(X0,X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f231])).

fof(f231,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ v2_tex_2(X0,X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1) ) ),
    inference(condensation,[],[f230])).

fof(f230,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_tex_2(X2,X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ v2_tex_2(X3,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1) ) ),
    inference(duplicate_literal_removal,[],[f229])).

fof(f229,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_tex_2(X2,X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ v2_tex_2(X3,X1)
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1) ) ),
    inference(condensation,[],[f228])).

fof(f228,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_tex_2(X2,X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ v2_tex_2(X3,X1)
      | ~ v2_tex_2(X4,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1) ) ),
    inference(duplicate_literal_removal,[],[f227])).

fof(f227,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_tex_2(X2,X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ v2_tex_2(X3,X1)
      | ~ v2_tex_2(X4,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f226,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(sK3(X0),X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ( ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),X0)
          | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),X0) )
        & v4_pre_topc(sK4(X0),X0)
        & v4_pre_topc(sK3(X0),X0)
        & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f25,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),X3,X4),X0)
                | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),X3,X4),X0) )
              & v4_pre_topc(X4,X0)
              & v4_pre_topc(X3,X0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X4] :
            ( ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),sK3(X0),X4),X0)
              | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),sK3(X0),X4),X0) )
            & v4_pre_topc(X4,X0)
            & v4_pre_topc(sK3(X0),X0)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

% (1130)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f25,plain,(
    ! [X0] :
      ( ? [X4] :
          ( ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),sK3(X0),X4),X0)
            | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),sK3(X0),X4),X0) )
          & v4_pre_topc(X4,X0)
          & v4_pre_topc(sK3(X0),X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),X0)
          | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),X0) )
        & v4_pre_topc(sK4(X0),X0)
        & v4_pre_topc(sK3(X0),X0)
        & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ? [X3] :
          ( ? [X4] :
              ( ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),X3,X4),X0)
                | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),X3,X4),X0) )
              & v4_pre_topc(X4,X0)
              & v4_pre_topc(X3,X0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X3] :
          ( ! [X4] :
              ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0)
              | ~ v2_tex_2(X4,X0)
              | ~ v2_tex_2(X3,X0)
              | ~ v4_pre_topc(X4,X0)
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
      | ? [X1] :
          ( ? [X2] :
              ( ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) )
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X3] :
          ( ! [X4] :
              ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0)
              | ~ v2_tex_2(X4,X0)
              | ~ v2_tex_2(X3,X0)
              | ~ v4_pre_topc(X4,X0)
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
      | ? [X1] :
          ( ? [X2] :
              ( ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) )
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v4_pre_topc(X2,X0)
                    & v4_pre_topc(X1,X0) )
                 => ( v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                    & v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) )
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X4,X0)
                    & v2_tex_2(X3,X0)
                    & v4_pre_topc(X4,X0)
                    & v4_pre_topc(X3,X0) )
                 => v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0) ) ) ) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v4_pre_topc(X2,X0)
                    & v4_pre_topc(X1,X0) )
                 => ( v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                    & v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    & v2_tex_2(X1,X0)
                    & v4_pre_topc(X2,X0)
                    & v4_pre_topc(X1,X0) )
                 => v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tex_2)).

fof(f226,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(sK3(X0),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v2_tex_2(X2,X0)
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ),
    inference(duplicate_literal_removal,[],[f225])).

fof(f225,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v4_pre_topc(sK3(X0),X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(condensation,[],[f224])).

fof(f224,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ v2_tex_2(X3,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1) ) ),
    inference(duplicate_literal_removal,[],[f223])).

fof(f223,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ v2_tex_2(X3,X1)
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1) ) ),
    inference(condensation,[],[f222])).

fof(f222,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ v2_tex_2(X3,X1)
      | ~ v2_tex_2(X4,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1) ) ),
    inference(duplicate_literal_removal,[],[f221])).

fof(f221,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ v2_tex_2(X3,X1)
      | ~ v2_tex_2(X4,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f220,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(sK4(X0),X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f220,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(sK4(X1),X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(sK3(X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f219])).

fof(f219,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(X0,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(sK4(X1),X1)
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ v2_tex_2(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1) ) ),
    inference(condensation,[],[f218])).

fof(f218,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_pre_topc(X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(sK4(X1),X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ v2_tex_2(X3,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1) ) ),
    inference(duplicate_literal_removal,[],[f217])).

fof(f217,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_pre_topc(X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(sK4(X1),X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ v2_tex_2(X3,X1)
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1) ) ),
    inference(condensation,[],[f216])).

fof(f216,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_pre_topc(X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(sK4(X1),X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ v2_tex_2(X3,X1)
      | ~ v2_tex_2(X4,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1) ) ),
    inference(duplicate_literal_removal,[],[f215])).

fof(f215,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_pre_topc(X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(sK4(X1),X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ v2_tex_2(X3,X1)
      | ~ v2_tex_2(X4,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f214,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f214,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ v2_pre_topc(X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(sK4(X1),X1)
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(sK3(X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f213])).

fof(f213,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ v2_pre_topc(X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(sK4(X1),X1)
      | ~ m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1) ) ),
    inference(condensation,[],[f212])).

fof(f212,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_pre_topc(X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(sK4(X1),X1)
      | ~ m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ v2_tex_2(X3,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1) ) ),
    inference(duplicate_literal_removal,[],[f211])).

fof(f211,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_pre_topc(X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(sK4(X1),X1)
      | ~ m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ v2_tex_2(X3,X1)
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1) ) ),
    inference(condensation,[],[f210])).

fof(f210,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_pre_topc(X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(sK4(X1),X1)
      | ~ m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ v2_tex_2(X3,X1)
      | ~ v2_tex_2(X4,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1) ) ),
    inference(duplicate_literal_removal,[],[f209])).

fof(f209,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_pre_topc(X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(sK4(X1),X1)
      | ~ m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ v2_tex_2(X3,X1)
      | ~ v2_tex_2(X4,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f208,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f208,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_pre_topc(X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(sK4(X1),X1)
      | ~ m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(sK3(X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f207])).

fof(f207,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_pre_topc(X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(sK4(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(sK4(X1),X1)
      | ~ m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(resolution,[],[f206,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_tops_1)).

fof(f206,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(k2_xboole_0(sK3(X0),sK4(X0)),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v2_pre_topc(X0)
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(duplicate_literal_removal,[],[f205])).

fof(f205,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v2_pre_topc(X0)
      | ~ v4_pre_topc(k2_xboole_0(sK3(X0),sK4(X0)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(condensation,[],[f204])).

fof(f204,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_pre_topc(X1)
      | ~ v4_pre_topc(k2_xboole_0(sK3(X1),sK4(X1)),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X3,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1) ) ),
    inference(duplicate_literal_removal,[],[f203])).

fof(f203,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_pre_topc(X1)
      | ~ v4_pre_topc(k2_xboole_0(sK3(X1),sK4(X1)),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X3,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1) ) ),
    inference(condensation,[],[f202])).

fof(f202,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_pre_topc(X1)
      | ~ v4_pre_topc(k2_xboole_0(sK3(X1),sK4(X1)),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X3,X1)
      | ~ v2_tex_2(X4,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1) ) ),
    inference(duplicate_literal_removal,[],[f201])).

fof(f201,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_pre_topc(X1)
      | ~ v4_pre_topc(k2_xboole_0(sK3(X1),sK4(X1)),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X3,X1)
      | ~ v2_tex_2(X4,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f200,f37])).

fof(f200,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ v2_pre_topc(X1)
      | ~ v4_pre_topc(k2_xboole_0(sK3(X1),sK4(X1)),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(duplicate_literal_removal,[],[f199])).

fof(f199,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ v2_pre_topc(X1)
      | ~ v4_pre_topc(k2_xboole_0(sK3(X1),sK4(X1)),X1)
      | ~ m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1) ) ),
    inference(condensation,[],[f198])).

fof(f198,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_pre_topc(X1)
      | ~ v4_pre_topc(k2_xboole_0(sK3(X1),sK4(X1)),X1)
      | ~ m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X3,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1) ) ),
    inference(duplicate_literal_removal,[],[f197])).

fof(f197,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_pre_topc(X1)
      | ~ v4_pre_topc(k2_xboole_0(sK3(X1),sK4(X1)),X1)
      | ~ m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X3,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1) ) ),
    inference(condensation,[],[f196])).

fof(f196,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_pre_topc(X1)
      | ~ v4_pre_topc(k2_xboole_0(sK3(X1),sK4(X1)),X1)
      | ~ m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X3,X1)
      | ~ v2_tex_2(X4,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1) ) ),
    inference(duplicate_literal_removal,[],[f195])).

fof(f195,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_pre_topc(X1)
      | ~ v4_pre_topc(k2_xboole_0(sK3(X1),sK4(X1)),X1)
      | ~ m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X3,X1)
      | ~ v2_tex_2(X4,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f194,f38])).

fof(f194,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v2_pre_topc(X0)
      | ~ v4_pre_topc(k2_xboole_0(sK3(X0),sK4(X0)),X0)
      | ~ m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(superposition,[],[f193,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f193,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f192])).

fof(f192,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1)
      | ~ l1_pre_topc(X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ v2_pre_topc(X1)
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1) ) ),
    inference(condensation,[],[f191])).

fof(f191,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_pre_topc(X1)
      | ~ v2_tex_2(X3,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1) ) ),
    inference(duplicate_literal_removal,[],[f190])).

fof(f190,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_pre_topc(X1)
      | ~ v2_tex_2(X3,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1) ) ),
    inference(condensation,[],[f189])).

fof(f189,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_pre_topc(X1)
      | ~ v2_tex_2(X3,X1)
      | ~ v2_tex_2(X4,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1) ) ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_pre_topc(X1)
      | ~ v2_tex_2(X3,X1)
      | ~ v2_tex_2(X4,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f187,f39])).

fof(f187,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(sK3(X0),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f186])).

fof(f186,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(sK3(X0),X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(condensation,[],[f185])).

fof(f185,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_pre_topc(X1)
      | ~ v2_tex_2(X3,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1) ) ),
    inference(duplicate_literal_removal,[],[f184])).

fof(f184,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_pre_topc(X1)
      | ~ v2_tex_2(X3,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1) ) ),
    inference(condensation,[],[f183])).

fof(f183,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_pre_topc(X1)
      | ~ v2_tex_2(X3,X1)
      | ~ v2_tex_2(X4,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1) ) ),
    inference(duplicate_literal_removal,[],[f182])).

fof(f182,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_pre_topc(X1)
      | ~ v2_tex_2(X3,X1)
      | ~ v2_tex_2(X4,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f181,f40])).

fof(f181,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(sK4(X1),X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f180])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
      | ~ l1_pre_topc(X1)
      | ~ v4_pre_topc(sK4(X1),X1)
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ v2_pre_topc(X1)
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1) ) ),
    inference(condensation,[],[f179])).

fof(f179,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ l1_pre_topc(X1)
      | ~ v4_pre_topc(sK4(X1),X1)
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_pre_topc(X1)
      | ~ v2_tex_2(X3,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1) ) ),
    inference(duplicate_literal_removal,[],[f178])).

fof(f178,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ l1_pre_topc(X1)
      | ~ v4_pre_topc(sK4(X1),X1)
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_pre_topc(X1)
      | ~ v2_tex_2(X3,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1) ) ),
    inference(condensation,[],[f177])).

fof(f177,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ l1_pre_topc(X1)
      | ~ v4_pre_topc(sK4(X1),X1)
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_pre_topc(X1)
      | ~ v2_tex_2(X3,X1)
      | ~ v2_tex_2(X4,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1) ) ),
    inference(duplicate_literal_removal,[],[f176])).

fof(f176,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ l1_pre_topc(X1)
      | ~ v4_pre_topc(sK4(X1),X1)
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v2_pre_topc(X1)
      | ~ v2_tex_2(X3,X1)
      | ~ v2_tex_2(X4,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f175,f37])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
      | ~ l1_pre_topc(X1)
      | ~ v4_pre_topc(sK4(X1),X1)
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f174])).

fof(f174,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(X0,X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
      | ~ l1_pre_topc(X1)
      | ~ v4_pre_topc(sK4(X1),X1)
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ v2_tex_2(X0,X1)
      | ~ m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_pre_topc(X1)
      | ~ v2_tex_2(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1) ) ),
    inference(condensation,[],[f173])).

fof(f173,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ l1_pre_topc(X1)
      | ~ v4_pre_topc(sK4(X1),X1)
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ v2_tex_2(X2,X1)
      | ~ m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_pre_topc(X1)
      | ~ v2_tex_2(X3,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1) ) ),
    inference(duplicate_literal_removal,[],[f172])).

fof(f172,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ l1_pre_topc(X1)
      | ~ v4_pre_topc(sK4(X1),X1)
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ v2_tex_2(X2,X1)
      | ~ m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_pre_topc(X1)
      | ~ v2_tex_2(X3,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1) ) ),
    inference(condensation,[],[f171])).

fof(f171,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ l1_pre_topc(X1)
      | ~ v4_pre_topc(sK4(X1),X1)
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ v2_tex_2(X2,X1)
      | ~ m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_pre_topc(X1)
      | ~ v2_tex_2(X3,X1)
      | ~ v2_tex_2(X4,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1) ) ),
    inference(duplicate_literal_removal,[],[f170])).

fof(f170,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_tex_2(X0,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1)
      | ~ l1_pre_topc(X1)
      | ~ v4_pre_topc(sK4(X1),X1)
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ v2_tex_2(X2,X1)
      | ~ m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_pre_topc(X1)
      | ~ v2_tex_2(X3,X1)
      | ~ v2_tex_2(X4,X1)
      | ~ v4_pre_topc(X3,X1)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f169,f38])).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
      | ~ l1_pre_topc(X1)
      | ~ v4_pre_topc(sK4(X1),X1)
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ v2_tex_2(X0,X1)
      | ~ m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_tex_2(X0,X1)
      | ~ v2_tex_2(X2,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ v4_pre_topc(X2,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1)
      | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
      | ~ l1_pre_topc(X1)
      | ~ v4_pre_topc(sK4(X1),X1)
      | ~ v4_pre_topc(sK3(X1),X1)
      | ~ m1_subset_1(sK4(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(resolution,[],[f41,f43])).

% (1141)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% (1133)Refutation not found, incomplete strategy% (1133)------------------------------
% (1133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1133)Termination reason: Refutation not found, incomplete strategy

% (1133)Memory used [KB]: 10618
% (1133)Time elapsed: 0.098 s
% (1133)------------------------------
% (1133)------------------------------
% (1134)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% (1148)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% (1140)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% (1145)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% (1144)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% (1147)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% (1142)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% (1148)Refutation not found, incomplete strategy% (1148)------------------------------
% (1148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1148)Termination reason: Refutation not found, incomplete strategy

% (1148)Memory used [KB]: 10618
% (1148)Time elapsed: 0.061 s
% (1148)------------------------------
% (1148)------------------------------
% (1140)Refutation not found, incomplete strategy% (1140)------------------------------
% (1140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1140)Termination reason: Refutation not found, incomplete strategy

% (1140)Memory used [KB]: 1663
% (1140)Time elapsed: 0.111 s
% (1140)------------------------------
% (1140)------------------------------
% (1137)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% (1136)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% (1131)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% (1138)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% (1131)Refutation not found, incomplete strategy% (1131)------------------------------
% (1131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1131)Termination reason: Refutation not found, incomplete strategy

% (1131)Memory used [KB]: 10618
% (1131)Time elapsed: 0.108 s
% (1131)------------------------------
% (1131)------------------------------
% (1130)Refutation not found, incomplete strategy% (1130)------------------------------
% (1130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1130)Termination reason: Refutation not found, incomplete strategy

% (1130)Memory used [KB]: 6140
% (1130)Time elapsed: 0.059 s
% (1130)------------------------------
% (1130)------------------------------
fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & v4_pre_topc(X1,X0) )
               => v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(k9_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),X0)
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f77,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f75])).

fof(f72,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f70])).

fof(f67,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f57,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f62,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f52,plain,
    ( v2_tex_2(sK2,sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f87,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f85])).

fof(f82,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f80])).

fof(f118,plain,
    ( ~ spl5_7
    | ~ spl5_6
    | ~ spl5_14
    | spl5_1 ),
    inference(avatar_split_clause,[],[f93,f45,f115,f70,f75])).

fof(f45,plain,
    ( spl5_1
  <=> v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f93,plain,
    ( ~ v2_tex_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_1 ),
    inference(superposition,[],[f47,f36])).

fof(f47,plain,
    ( ~ v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f108,plain,
    ( spl5_12
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f90,f75,f70,f105])).

fof(f90,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f77,f72,f36])).

fof(f88,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f27,f85])).

fof(f27,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v2_tex_2(sK2,sK0)
    & v2_tex_2(sK1,sK0)
    & v4_pre_topc(sK2,sK0)
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f21,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v2_tex_2(X2,X0)
                & v2_tex_2(X1,X0)
                & v4_pre_topc(X2,X0)
                & v4_pre_topc(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v2_tex_2(X2,sK0)
              & v2_tex_2(X1,sK0)
              & v4_pre_topc(X2,sK0)
              & v4_pre_topc(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_tex_2(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & v2_tex_2(X2,sK0)
            & v2_tex_2(X1,sK0)
            & v4_pre_topc(X2,sK0)
            & v4_pre_topc(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & v2_tex_2(X2,sK0)
          & v2_tex_2(sK1,sK0)
          & v4_pre_topc(X2,sK0)
          & v4_pre_topc(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( ~ v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & v2_tex_2(X2,sK0)
        & v2_tex_2(sK1,sK0)
        & v4_pre_topc(X2,sK0)
        & v4_pre_topc(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & v2_tex_2(sK2,sK0)
      & v2_tex_2(sK1,sK0)
      & v4_pre_topc(sK2,sK0)
      & v4_pre_topc(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_tex_2(X2,X0)
              & v2_tex_2(X1,X0)
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_tex_2(X2,X0)
              & v2_tex_2(X1,X0)
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    & v2_tex_2(X1,X0)
                    & v4_pre_topc(X2,X0)
                    & v4_pre_topc(X1,X0) )
                 => v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,negated_conjecture,(
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
                    & v4_pre_topc(X2,X0)
                    & v4_pre_topc(X1,X0) )
                 => v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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
                  & v4_pre_topc(X2,X0)
                  & v4_pre_topc(X1,X0) )
               => v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_tex_2)).

fof(f83,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f28,f80])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f78,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f29,f75])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f73,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f30,f70])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f68,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f31,f65])).

fof(f31,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f32,f60])).

fof(f32,plain,(
    v4_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f33,f55])).

fof(f33,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f34,f50])).

fof(f34,plain,(
    v2_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f35,f45])).

fof(f35,plain,(
    ~ v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:47:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (1124)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.49  % (1125)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.49  % (1129)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.49  % (1132)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.50  % (1126)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.50  % (1127)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.50  % (1128)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.50  % (1126)Refutation not found, incomplete strategy% (1126)------------------------------
% 0.20/0.50  % (1126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (1126)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (1126)Memory used [KB]: 10618
% 0.20/0.50  % (1126)Time elapsed: 0.087 s
% 0.20/0.50  % (1126)------------------------------
% 0.20/0.50  % (1126)------------------------------
% 0.20/0.50  % (1123)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.50  % (1139)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.50  % (1133)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.50  % (1143)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.50  % (1129)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f262,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f48,f53,f58,f63,f68,f73,f78,f83,f88,f108,f118,f245])).
% 0.20/0.50  fof(f245,plain,(
% 0.20/0.50    spl5_14 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_12),
% 0.20/0.50    inference(avatar_split_clause,[],[f244,f105,f85,f80,f75,f70,f65,f60,f55,f50,f115])).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    spl5_14 <=> v2_tex_2(k2_xboole_0(sK1,sK2),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    spl5_2 <=> v2_tex_2(sK2,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    spl5_3 <=> v2_tex_2(sK1,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    spl5_4 <=> v4_pre_topc(sK2,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    spl5_5 <=> v4_pre_topc(sK1,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    spl5_6 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    spl5_7 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    spl5_8 <=> l1_pre_topc(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    spl5_9 <=> v2_pre_topc(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    spl5_12 <=> k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.50  fof(f244,plain,(
% 0.20/0.50    v2_tex_2(k2_xboole_0(sK1,sK2),sK0) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_12)),
% 0.20/0.50    inference(forward_demodulation,[],[f235,f107])).
% 0.20/0.50  fof(f107,plain,(
% 0.20/0.50    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) | ~spl5_12),
% 0.20/0.50    inference(avatar_component_clause,[],[f105])).
% 0.20/0.50  fof(f235,plain,(
% 0.20/0.50    v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f82,f87,f52,f62,f57,f67,f72,f77,f232])).
% 0.20/0.50  fof(f232,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~l1_pre_topc(X1) | ~v4_pre_topc(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_pre_topc(X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X0,X1) | ~v2_tex_2(X0,X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f231])).
% 0.20/0.50  fof(f231,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X0,X1) | ~v2_tex_2(X0,X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(X0,X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)) )),
% 0.20/0.50    inference(condensation,[],[f230])).
% 0.20/0.50  fof(f230,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(X2,X1) | ~v2_tex_2(X2,X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~v2_tex_2(X3,X1) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1)) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f229])).
% 0.20/0.50  fof(f229,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(X2,X1) | ~v2_tex_2(X2,X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~v2_tex_2(X3,X1) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1)) )),
% 0.20/0.50    inference(condensation,[],[f228])).
% 0.20/0.50  fof(f228,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(X2,X1) | ~v2_tex_2(X2,X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~v2_tex_2(X3,X1) | ~v2_tex_2(X4,X1) | ~v4_pre_topc(X3,X1) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1)) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f227])).
% 0.20/0.50  fof(f227,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(X2,X1) | ~v2_tex_2(X2,X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~v2_tex_2(X3,X1) | ~v2_tex_2(X4,X1) | ~v4_pre_topc(X3,X1) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1) | ~l1_pre_topc(X1)) )),
% 0.20/0.50    inference(resolution,[],[f226,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v4_pre_topc(sK3(X0),X0) | ~v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (((~v4_pre_topc(k4_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),X0) | ~v4_pre_topc(k9_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),X0)) & v4_pre_topc(sK4(X0),X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f25,f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : (? [X3] : (? [X4] : ((~v4_pre_topc(k4_subset_1(u1_struct_0(X0),X3,X4),X0) | ~v4_pre_topc(k9_subset_1(u1_struct_0(X0),X3,X4),X0)) & v4_pre_topc(X4,X0) & v4_pre_topc(X3,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X4] : ((~v4_pre_topc(k4_subset_1(u1_struct_0(X0),sK3(X0),X4),X0) | ~v4_pre_topc(k9_subset_1(u1_struct_0(X0),sK3(X0),X4),X0)) & v4_pre_topc(X4,X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  % (1130)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0] : (? [X4] : ((~v4_pre_topc(k4_subset_1(u1_struct_0(X0),sK3(X0),X4),X0) | ~v4_pre_topc(k9_subset_1(u1_struct_0(X0),sK3(X0),X4),X0)) & v4_pre_topc(X4,X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => ((~v4_pre_topc(k4_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),X0) | ~v4_pre_topc(k9_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),X0)) & v4_pre_topc(sK4(X0),X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X3] : (? [X4] : ((~v4_pre_topc(k4_subset_1(u1_struct_0(X0),X3,X4),X0) | ~v4_pre_topc(k9_subset_1(u1_struct_0(X0),X3,X4),X0)) & v4_pre_topc(X4,X0) & v4_pre_topc(X3,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(rectify,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0] : (! [X3] : (! [X4] : (v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0) | ~v2_tex_2(X4,X0) | ~v2_tex_2(X3,X0) | ~v4_pre_topc(X4,X0) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X1] : (? [X2] : ((~v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)) & v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0] : ((! [X3] : (! [X4] : ((v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0) | (~v2_tex_2(X4,X0) | ~v2_tex_2(X3,X0) | ~v4_pre_topc(X4,X0) | ~v4_pre_topc(X3,X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X1] : (? [X2] : (((~v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)) & (v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,plain,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => (v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0) & v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0))))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X4,X0) & v2_tex_2(X3,X0) & v4_pre_topc(X4,X0) & v4_pre_topc(X3,X0)) => v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0))))))),
% 0.20/0.50    inference(rectify,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => (v4_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0) & v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0))))) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) & v2_tex_2(X1,X0) & v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tex_2)).
% 0.20/0.50  fof(f226,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v4_pre_topc(sK3(X0),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~v4_pre_topc(X2,X0) | ~v2_tex_2(X2,X0) | v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f225])).
% 0.20/0.50  fof(f225,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~v4_pre_topc(X2,X0) | ~v2_tex_2(X2,X0) | ~v4_pre_topc(sK3(X0),X0) | ~v2_tex_2(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.50    inference(condensation,[],[f224])).
% 0.20/0.51  fof(f224,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(X2,X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(sK3(X1),X1) | ~v2_tex_2(X3,X1) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f223])).
% 0.20/0.51  fof(f223,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(X2,X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(sK3(X1),X1) | ~v2_tex_2(X3,X1) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1)) )),
% 0.20/0.51    inference(condensation,[],[f222])).
% 0.20/0.51  fof(f222,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(X2,X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(sK3(X1),X1) | ~v2_tex_2(X3,X1) | ~v2_tex_2(X4,X1) | ~v4_pre_topc(X3,X1) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f221])).
% 0.20/0.51  fof(f221,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(X2,X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(sK3(X1),X1) | ~v2_tex_2(X3,X1) | ~v2_tex_2(X4,X1) | ~v4_pre_topc(X3,X1) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1) | ~l1_pre_topc(X1)) )),
% 0.20/0.51    inference(resolution,[],[f220,f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (v4_pre_topc(sK4(X0),X0) | ~v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f220,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v4_pre_topc(sK4(X1),X1) | ~v4_pre_topc(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X0,X1) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(sK3(X1),X1)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f219])).
% 0.20/0.51  fof(f219,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v4_pre_topc(X0,X1) | ~v4_pre_topc(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(sK4(X1),X1) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(sK3(X1),X1) | ~v2_tex_2(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)) )),
% 0.20/0.51    inference(condensation,[],[f218])).
% 0.20/0.51  fof(f218,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v4_pre_topc(X2,X1) | ~v2_pre_topc(X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(sK4(X1),X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(sK3(X1),X1) | ~v2_tex_2(X3,X1) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f217])).
% 0.20/0.51  fof(f217,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v4_pre_topc(X2,X1) | ~v2_pre_topc(X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(sK4(X1),X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(sK3(X1),X1) | ~v2_tex_2(X3,X1) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1)) )),
% 0.20/0.51    inference(condensation,[],[f216])).
% 0.20/0.51  fof(f216,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v4_pre_topc(X2,X1) | ~v2_pre_topc(X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(sK4(X1),X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(sK3(X1),X1) | ~v2_tex_2(X3,X1) | ~v2_tex_2(X4,X1) | ~v4_pre_topc(X3,X1) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f215])).
% 0.20/0.51  fof(f215,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v4_pre_topc(X2,X1) | ~v2_pre_topc(X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(sK4(X1),X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(sK3(X1),X1) | ~v2_tex_2(X3,X1) | ~v2_tex_2(X4,X1) | ~v4_pre_topc(X3,X1) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1) | ~l1_pre_topc(X1)) )),
% 0.20/0.51    inference(resolution,[],[f214,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f214,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v4_pre_topc(X0,X1) | ~v2_pre_topc(X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(sK4(X1),X1) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(sK3(X1),X1)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f213])).
% 0.20/0.51  fof(f213,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v2_tex_2(X0,X1) | ~v4_pre_topc(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v4_pre_topc(X0,X1) | ~v2_pre_topc(X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(sK4(X1),X1) | ~m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(sK3(X1),X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)) )),
% 0.20/0.51    inference(condensation,[],[f212])).
% 0.20/0.51  fof(f212,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~v2_pre_topc(X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(sK4(X1),X1) | ~m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(sK3(X1),X1) | ~v2_tex_2(X3,X1) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f211])).
% 0.20/0.51  fof(f211,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~v2_pre_topc(X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(sK4(X1),X1) | ~m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(sK3(X1),X1) | ~v2_tex_2(X3,X1) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1)) )),
% 0.20/0.51    inference(condensation,[],[f210])).
% 0.20/0.51  fof(f210,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~v2_pre_topc(X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(sK4(X1),X1) | ~m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(sK3(X1),X1) | ~v2_tex_2(X3,X1) | ~v2_tex_2(X4,X1) | ~v4_pre_topc(X3,X1) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f209])).
% 0.20/0.51  fof(f209,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~v2_pre_topc(X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(sK4(X1),X1) | ~m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(sK3(X1),X1) | ~v2_tex_2(X3,X1) | ~v2_tex_2(X4,X1) | ~v4_pre_topc(X3,X1) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1) | ~l1_pre_topc(X1)) )),
% 0.20/0.51    inference(resolution,[],[f208,f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f208,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(sK4(X1),k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~v2_pre_topc(X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(sK4(X1),X1) | ~m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(sK3(X1),X1)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f207])).
% 0.20/0.51  fof(f207,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v2_tex_2(X0,X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~v2_pre_topc(X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(sK4(X1),k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(sK4(X1),X1) | ~m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(sK3(X1),X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 0.20/0.51    inference(resolution,[],[f206,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (v4_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (v4_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (v4_pre_topc(k2_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_xboole_0(X1,X2),X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_tops_1)).
% 0.20/0.51  fof(f206,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v4_pre_topc(k2_xboole_0(sK3(X0),sK4(X0)),X0) | ~v2_tex_2(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_tex_2(X2,X0) | ~v4_pre_topc(X2,X0) | ~v2_pre_topc(X0) | v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f205])).
% 0.20/0.51  fof(f205,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v2_tex_2(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_tex_2(X2,X0) | ~v4_pre_topc(X2,X0) | ~v2_pre_topc(X0) | ~v4_pre_topc(k2_xboole_0(sK3(X0),sK4(X0)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.51    inference(condensation,[],[f204])).
% 0.20/0.51  fof(f204,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~v2_tex_2(X0,X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~v2_pre_topc(X1) | ~v4_pre_topc(k2_xboole_0(sK3(X1),sK4(X1)),X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X3,X1) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f203])).
% 0.20/0.51  fof(f203,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~v2_tex_2(X0,X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~v2_pre_topc(X1) | ~v4_pre_topc(k2_xboole_0(sK3(X1),sK4(X1)),X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X3,X1) | ~v4_pre_topc(X3,X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1)) )),
% 0.20/0.51    inference(condensation,[],[f202])).
% 0.20/0.51  fof(f202,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (~v2_tex_2(X0,X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~v2_pre_topc(X1) | ~v4_pre_topc(k2_xboole_0(sK3(X1),sK4(X1)),X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X3,X1) | ~v2_tex_2(X4,X1) | ~v4_pre_topc(X3,X1) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f201])).
% 0.20/0.51  fof(f201,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (~v2_tex_2(X0,X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~v2_pre_topc(X1) | ~v4_pre_topc(k2_xboole_0(sK3(X1),sK4(X1)),X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X3,X1) | ~v2_tex_2(X4,X1) | ~v4_pre_topc(X3,X1) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1) | ~l1_pre_topc(X1)) )),
% 0.20/0.51    inference(resolution,[],[f200,f37])).
% 0.20/0.51  fof(f200,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(X0,X1) | ~v2_pre_topc(X1) | ~v4_pre_topc(k2_xboole_0(sK3(X1),sK4(X1)),X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f199])).
% 0.20/0.51  fof(f199,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(X0,X1) | ~v2_pre_topc(X1) | ~v4_pre_topc(k2_xboole_0(sK3(X1),sK4(X1)),X1) | ~m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(X0,X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)) )),
% 0.20/0.51    inference(condensation,[],[f198])).
% 0.20/0.51  fof(f198,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~v2_tex_2(X0,X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~v2_pre_topc(X1) | ~v4_pre_topc(k2_xboole_0(sK3(X1),sK4(X1)),X1) | ~m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X3,X1) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f197])).
% 0.20/0.51  fof(f197,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~v2_tex_2(X0,X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~v2_pre_topc(X1) | ~v4_pre_topc(k2_xboole_0(sK3(X1),sK4(X1)),X1) | ~m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X3,X1) | ~v4_pre_topc(X3,X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1)) )),
% 0.20/0.51    inference(condensation,[],[f196])).
% 0.20/0.51  fof(f196,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (~v2_tex_2(X0,X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~v2_pre_topc(X1) | ~v4_pre_topc(k2_xboole_0(sK3(X1),sK4(X1)),X1) | ~m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X3,X1) | ~v2_tex_2(X4,X1) | ~v4_pre_topc(X3,X1) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f195])).
% 0.20/0.51  fof(f195,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (~v2_tex_2(X0,X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~v2_pre_topc(X1) | ~v4_pre_topc(k2_xboole_0(sK3(X1),sK4(X1)),X1) | ~m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X3,X1) | ~v2_tex_2(X4,X1) | ~v4_pre_topc(X3,X1) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1) | ~l1_pre_topc(X1)) )),
% 0.20/0.51    inference(resolution,[],[f194,f38])).
% 0.20/0.51  fof(f194,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v2_tex_2(X2,X0) | ~v4_pre_topc(X2,X0) | ~v2_pre_topc(X0) | ~v4_pre_topc(k2_xboole_0(sK3(X0),sK4(X0)),X0) | ~m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.51    inference(superposition,[],[f193,f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(flattening,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.20/0.51  fof(f193,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(X0,X1) | ~v2_pre_topc(X1)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f192])).
% 0.20/0.51  fof(f192,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1) | ~l1_pre_topc(X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(X0,X1) | ~v2_pre_topc(X1) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(X0,X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)) )),
% 0.20/0.51    inference(condensation,[],[f191])).
% 0.20/0.51  fof(f191,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~v2_tex_2(X0,X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~v2_pre_topc(X1) | ~v2_tex_2(X3,X1) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f190])).
% 0.20/0.51  fof(f190,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~v2_tex_2(X0,X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~v2_pre_topc(X1) | ~v2_tex_2(X3,X1) | ~v4_pre_topc(X3,X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1)) )),
% 0.20/0.51    inference(condensation,[],[f189])).
% 0.20/0.51  fof(f189,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (~v2_tex_2(X0,X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~v2_pre_topc(X1) | ~v2_tex_2(X3,X1) | ~v2_tex_2(X4,X1) | ~v4_pre_topc(X3,X1) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f188])).
% 0.20/0.51  fof(f188,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (~v2_tex_2(X0,X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~v2_pre_topc(X1) | ~v2_tex_2(X3,X1) | ~v2_tex_2(X4,X1) | ~v4_pre_topc(X3,X1) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1) | ~l1_pre_topc(X1)) )),
% 0.20/0.51    inference(resolution,[],[f187,f39])).
% 0.20/0.51  fof(f187,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v4_pre_topc(sK3(X0),X0) | ~v2_tex_2(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(k4_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v2_tex_2(X2,X0) | ~v4_pre_topc(X2,X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f186])).
% 0.20/0.51  fof(f186,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v2_tex_2(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(k4_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(sK3(X0),X0) | ~v2_tex_2(X2,X0) | ~v4_pre_topc(X2,X0) | ~v2_pre_topc(X0) | ~v2_tex_2(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.51    inference(condensation,[],[f185])).
% 0.20/0.51  fof(f185,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~v2_tex_2(X0,X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(sK3(X1),X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~v2_pre_topc(X1) | ~v2_tex_2(X3,X1) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f184])).
% 0.20/0.51  fof(f184,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~v2_tex_2(X0,X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(sK3(X1),X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~v2_pre_topc(X1) | ~v2_tex_2(X3,X1) | ~v4_pre_topc(X3,X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1)) )),
% 0.20/0.51    inference(condensation,[],[f183])).
% 0.20/0.51  fof(f183,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (~v2_tex_2(X0,X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(sK3(X1),X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~v2_pre_topc(X1) | ~v2_tex_2(X3,X1) | ~v2_tex_2(X4,X1) | ~v4_pre_topc(X3,X1) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f182])).
% 0.20/0.51  fof(f182,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (~v2_tex_2(X0,X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(sK3(X1),X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~v2_pre_topc(X1) | ~v2_tex_2(X3,X1) | ~v2_tex_2(X4,X1) | ~v4_pre_topc(X3,X1) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1) | ~l1_pre_topc(X1)) )),
% 0.20/0.51    inference(resolution,[],[f181,f40])).
% 0.20/0.51  fof(f181,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v4_pre_topc(sK4(X1),X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1) | ~l1_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(sK3(X1),X1) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(X0,X1) | ~v2_pre_topc(X1)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f180])).
% 0.20/0.51  fof(f180,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1) | ~l1_pre_topc(X1) | ~v4_pre_topc(sK4(X1),X1) | ~v4_pre_topc(sK3(X1),X1) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(X0,X1) | ~v2_pre_topc(X1) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(X0,X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)) )),
% 0.20/0.51    inference(condensation,[],[f179])).
% 0.20/0.51  fof(f179,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~v2_tex_2(X0,X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~l1_pre_topc(X1) | ~v4_pre_topc(sK4(X1),X1) | ~v4_pre_topc(sK3(X1),X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~v2_pre_topc(X1) | ~v2_tex_2(X3,X1) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f178])).
% 0.20/0.51  fof(f178,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~v2_tex_2(X0,X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~l1_pre_topc(X1) | ~v4_pre_topc(sK4(X1),X1) | ~v4_pre_topc(sK3(X1),X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~v2_pre_topc(X1) | ~v2_tex_2(X3,X1) | ~v4_pre_topc(X3,X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1)) )),
% 0.20/0.51    inference(condensation,[],[f177])).
% 0.20/0.51  fof(f177,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (~v2_tex_2(X0,X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~l1_pre_topc(X1) | ~v4_pre_topc(sK4(X1),X1) | ~v4_pre_topc(sK3(X1),X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~v2_pre_topc(X1) | ~v2_tex_2(X3,X1) | ~v2_tex_2(X4,X1) | ~v4_pre_topc(X3,X1) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f176])).
% 0.20/0.51  fof(f176,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (~v2_tex_2(X0,X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~l1_pre_topc(X1) | ~v4_pre_topc(sK4(X1),X1) | ~v4_pre_topc(sK3(X1),X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~v2_pre_topc(X1) | ~v2_tex_2(X3,X1) | ~v2_tex_2(X4,X1) | ~v4_pre_topc(X3,X1) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1) | ~l1_pre_topc(X1)) )),
% 0.20/0.51    inference(resolution,[],[f175,f37])).
% 0.20/0.51  fof(f175,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1) | ~l1_pre_topc(X1) | ~v4_pre_topc(sK4(X1),X1) | ~v4_pre_topc(sK3(X1),X1) | ~v2_tex_2(X0,X1) | ~v4_pre_topc(X0,X1) | ~v2_pre_topc(X1)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f174])).
% 0.20/0.51  fof(f174,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v4_pre_topc(X0,X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X2,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1) | ~l1_pre_topc(X1) | ~v4_pre_topc(sK4(X1),X1) | ~v4_pre_topc(sK3(X1),X1) | ~v2_tex_2(X0,X1) | ~m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1))) | ~v2_pre_topc(X1) | ~v2_tex_2(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1)) )),
% 0.20/0.51    inference(condensation,[],[f173])).
% 0.20/0.51  fof(f173,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~v2_tex_2(X0,X1) | ~v4_pre_topc(X2,X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~l1_pre_topc(X1) | ~v4_pre_topc(sK4(X1),X1) | ~v4_pre_topc(sK3(X1),X1) | ~v2_tex_2(X2,X1) | ~m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1))) | ~v2_pre_topc(X1) | ~v2_tex_2(X3,X1) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f172])).
% 0.20/0.51  fof(f172,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~v2_tex_2(X0,X1) | ~v4_pre_topc(X2,X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~l1_pre_topc(X1) | ~v4_pre_topc(sK4(X1),X1) | ~v4_pre_topc(sK3(X1),X1) | ~v2_tex_2(X2,X1) | ~m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1))) | ~v2_pre_topc(X1) | ~v2_tex_2(X3,X1) | ~v4_pre_topc(X3,X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X3),X1)) )),
% 0.20/0.51    inference(condensation,[],[f171])).
% 0.20/0.51  fof(f171,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (~v2_tex_2(X0,X1) | ~v4_pre_topc(X2,X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~l1_pre_topc(X1) | ~v4_pre_topc(sK4(X1),X1) | ~v4_pre_topc(sK3(X1),X1) | ~v2_tex_2(X2,X1) | ~m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1))) | ~v2_pre_topc(X1) | ~v2_tex_2(X3,X1) | ~v2_tex_2(X4,X1) | ~v4_pre_topc(X3,X1) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f170])).
% 0.20/0.51  fof(f170,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (~v2_tex_2(X0,X1) | ~v4_pre_topc(X2,X1) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X0,X2),X1) | ~l1_pre_topc(X1) | ~v4_pre_topc(sK4(X1),X1) | ~v4_pre_topc(sK3(X1),X1) | ~v2_tex_2(X2,X1) | ~m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1))) | ~v2_pre_topc(X1) | ~v2_tex_2(X3,X1) | ~v2_tex_2(X4,X1) | ~v4_pre_topc(X3,X1) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X4,X3),X1) | ~l1_pre_topc(X1)) )),
% 0.20/0.51    inference(resolution,[],[f169,f38])).
% 0.20/0.51  fof(f169,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(sK4(X1),k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X0,X1) | ~v4_pre_topc(X2,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1) | ~l1_pre_topc(X1) | ~v4_pre_topc(sK4(X1),X1) | ~v4_pre_topc(sK3(X1),X1) | ~v2_tex_2(X0,X1) | ~m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1))) | ~v2_pre_topc(X1)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f168])).
% 0.20/0.51  fof(f168,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v2_tex_2(X0,X1) | ~v2_tex_2(X2,X1) | ~v4_pre_topc(X0,X1) | ~v4_pre_topc(X2,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(k4_subset_1(u1_struct_0(X1),sK3(X1),sK4(X1)),X1) | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X0),X1) | ~l1_pre_topc(X1) | ~v4_pre_topc(sK4(X1),X1) | ~v4_pre_topc(sK3(X1),X1) | ~m1_subset_1(sK4(X1),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 0.20/0.51    inference(resolution,[],[f41,f43])).
% 0.20/0.51  % (1141)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.51  % (1133)Refutation not found, incomplete strategy% (1133)------------------------------
% 0.20/0.51  % (1133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (1133)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (1133)Memory used [KB]: 10618
% 0.20/0.51  % (1133)Time elapsed: 0.098 s
% 0.20/0.51  % (1133)------------------------------
% 0.20/0.51  % (1133)------------------------------
% 0.20/0.51  % (1134)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.51  % (1148)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.51  % (1140)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.51  % (1145)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.51  % (1144)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.51  % (1147)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.51  % (1142)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.51  % (1148)Refutation not found, incomplete strategy% (1148)------------------------------
% 0.20/0.51  % (1148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (1148)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (1148)Memory used [KB]: 10618
% 0.20/0.51  % (1148)Time elapsed: 0.061 s
% 0.20/0.51  % (1148)------------------------------
% 0.20/0.51  % (1148)------------------------------
% 0.20/0.51  % (1140)Refutation not found, incomplete strategy% (1140)------------------------------
% 0.20/0.51  % (1140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (1140)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (1140)Memory used [KB]: 1663
% 0.20/0.51  % (1140)Time elapsed: 0.111 s
% 0.20/0.51  % (1140)------------------------------
% 0.20/0.51  % (1140)------------------------------
% 0.20/0.52  % (1137)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.20/0.52  % (1136)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 1.20/0.52  % (1131)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.20/0.52  % (1138)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.20/0.52  % (1131)Refutation not found, incomplete strategy% (1131)------------------------------
% 1.20/0.52  % (1131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (1131)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.52  
% 1.20/0.52  % (1131)Memory used [KB]: 10618
% 1.20/0.52  % (1131)Time elapsed: 0.108 s
% 1.20/0.52  % (1131)------------------------------
% 1.20/0.52  % (1131)------------------------------
% 1.20/0.52  % (1130)Refutation not found, incomplete strategy% (1130)------------------------------
% 1.20/0.52  % (1130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (1130)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.52  
% 1.20/0.52  % (1130)Memory used [KB]: 6140
% 1.20/0.52  % (1130)Time elapsed: 0.059 s
% 1.20/0.52  % (1130)------------------------------
% 1.20/0.52  % (1130)------------------------------
% 1.20/0.52  fof(f43,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f18])).
% 1.20/0.52  fof(f18,plain,(
% 1.20/0.52    ! [X0] : (! [X1] : (! [X2] : (v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.20/0.52    inference(flattening,[],[f17])).
% 1.20/0.52  fof(f17,plain,(
% 1.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.20/0.52    inference(ennf_transformation,[],[f3])).
% 1.20/0.52  fof(f3,axiom,(
% 1.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_1)).
% 1.20/0.52  fof(f41,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (~v4_pre_topc(k9_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),X0) | ~v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(k4_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),X0) | v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | ~l1_pre_topc(X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f26])).
% 1.20/0.52  fof(f77,plain,(
% 1.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_7),
% 1.20/0.52    inference(avatar_component_clause,[],[f75])).
% 1.20/0.52  fof(f72,plain,(
% 1.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_6),
% 1.20/0.52    inference(avatar_component_clause,[],[f70])).
% 1.20/0.52  fof(f67,plain,(
% 1.20/0.52    v4_pre_topc(sK1,sK0) | ~spl5_5),
% 1.20/0.52    inference(avatar_component_clause,[],[f65])).
% 1.20/0.52  fof(f57,plain,(
% 1.20/0.52    v2_tex_2(sK1,sK0) | ~spl5_3),
% 1.20/0.52    inference(avatar_component_clause,[],[f55])).
% 1.20/0.52  fof(f62,plain,(
% 1.20/0.52    v4_pre_topc(sK2,sK0) | ~spl5_4),
% 1.20/0.52    inference(avatar_component_clause,[],[f60])).
% 1.20/0.52  fof(f52,plain,(
% 1.20/0.52    v2_tex_2(sK2,sK0) | ~spl5_2),
% 1.20/0.52    inference(avatar_component_clause,[],[f50])).
% 1.20/0.52  fof(f87,plain,(
% 1.20/0.52    v2_pre_topc(sK0) | ~spl5_9),
% 1.20/0.52    inference(avatar_component_clause,[],[f85])).
% 1.20/0.52  fof(f82,plain,(
% 1.20/0.52    l1_pre_topc(sK0) | ~spl5_8),
% 1.20/0.52    inference(avatar_component_clause,[],[f80])).
% 1.20/0.52  fof(f118,plain,(
% 1.20/0.52    ~spl5_7 | ~spl5_6 | ~spl5_14 | spl5_1),
% 1.20/0.52    inference(avatar_split_clause,[],[f93,f45,f115,f70,f75])).
% 1.20/0.52  fof(f45,plain,(
% 1.20/0.52    spl5_1 <=> v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 1.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.20/0.52  fof(f93,plain,(
% 1.20/0.52    ~v2_tex_2(k2_xboole_0(sK1,sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl5_1),
% 1.20/0.52    inference(superposition,[],[f47,f36])).
% 1.20/0.52  fof(f47,plain,(
% 1.20/0.52    ~v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | spl5_1),
% 1.20/0.52    inference(avatar_component_clause,[],[f45])).
% 1.20/0.52  fof(f108,plain,(
% 1.20/0.52    spl5_12 | ~spl5_6 | ~spl5_7),
% 1.20/0.52    inference(avatar_split_clause,[],[f90,f75,f70,f105])).
% 1.20/0.52  fof(f90,plain,(
% 1.20/0.52    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) | (~spl5_6 | ~spl5_7)),
% 1.20/0.52    inference(unit_resulting_resolution,[],[f77,f72,f36])).
% 1.20/0.52  fof(f88,plain,(
% 1.20/0.52    spl5_9),
% 1.20/0.52    inference(avatar_split_clause,[],[f27,f85])).
% 1.20/0.52  fof(f27,plain,(
% 1.20/0.52    v2_pre_topc(sK0)),
% 1.20/0.52    inference(cnf_transformation,[],[f22])).
% 1.20/0.52  fof(f22,plain,(
% 1.20/0.52    ((~v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v2_tex_2(sK2,sK0) & v2_tex_2(sK1,sK0) & v4_pre_topc(sK2,sK0) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f21,f20,f19])).
% 1.20/0.52  fof(f19,plain,(
% 1.20/0.52    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_tex_2(X2,X0) & v2_tex_2(X1,X0) & v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tex_2(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v2_tex_2(X2,sK0) & v2_tex_2(X1,sK0) & v4_pre_topc(X2,sK0) & v4_pre_topc(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.20/0.52    introduced(choice_axiom,[])).
% 1.20/0.52  fof(f20,plain,(
% 1.20/0.52    ? [X1] : (? [X2] : (~v2_tex_2(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v2_tex_2(X2,sK0) & v2_tex_2(X1,sK0) & v4_pre_topc(X2,sK0) & v4_pre_topc(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v2_tex_2(X2,sK0) & v2_tex_2(sK1,sK0) & v4_pre_topc(X2,sK0) & v4_pre_topc(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.20/0.52    introduced(choice_axiom,[])).
% 1.20/0.52  fof(f21,plain,(
% 1.20/0.52    ? [X2] : (~v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v2_tex_2(X2,sK0) & v2_tex_2(sK1,sK0) & v4_pre_topc(X2,sK0) & v4_pre_topc(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v2_tex_2(sK2,sK0) & v2_tex_2(sK1,sK0) & v4_pre_topc(sK2,sK0) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.20/0.52    introduced(choice_axiom,[])).
% 1.20/0.52  fof(f10,plain,(
% 1.20/0.52    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_tex_2(X2,X0) & v2_tex_2(X1,X0) & v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.20/0.52    inference(flattening,[],[f9])).
% 1.20/0.52  fof(f9,plain,(
% 1.20/0.52    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) & v2_tex_2(X1,X0) & v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.20/0.52    inference(ennf_transformation,[],[f8])).
% 1.20/0.52  fof(f8,plain,(
% 1.20/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) & v2_tex_2(X1,X0) & v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 1.20/0.52    inference(pure_predicate_removal,[],[f6])).
% 1.20/0.52  fof(f6,negated_conjecture,(
% 1.20/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) & v2_tex_2(X1,X0) & v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 1.20/0.52    inference(negated_conjecture,[],[f5])).
% 1.20/0.52  fof(f5,conjecture,(
% 1.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) & v2_tex_2(X1,X0) & v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_tex_2)).
% 1.20/0.52  fof(f83,plain,(
% 1.20/0.52    spl5_8),
% 1.20/0.52    inference(avatar_split_clause,[],[f28,f80])).
% 1.20/0.52  fof(f28,plain,(
% 1.20/0.52    l1_pre_topc(sK0)),
% 1.20/0.52    inference(cnf_transformation,[],[f22])).
% 1.20/0.52  fof(f78,plain,(
% 1.20/0.52    spl5_7),
% 1.20/0.52    inference(avatar_split_clause,[],[f29,f75])).
% 1.20/0.52  fof(f29,plain,(
% 1.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.20/0.52    inference(cnf_transformation,[],[f22])).
% 1.20/0.52  fof(f73,plain,(
% 1.20/0.52    spl5_6),
% 1.20/0.52    inference(avatar_split_clause,[],[f30,f70])).
% 1.20/0.52  fof(f30,plain,(
% 1.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.20/0.52    inference(cnf_transformation,[],[f22])).
% 1.20/0.52  fof(f68,plain,(
% 1.20/0.52    spl5_5),
% 1.20/0.52    inference(avatar_split_clause,[],[f31,f65])).
% 1.20/0.52  fof(f31,plain,(
% 1.20/0.52    v4_pre_topc(sK1,sK0)),
% 1.20/0.52    inference(cnf_transformation,[],[f22])).
% 1.20/0.52  fof(f63,plain,(
% 1.20/0.52    spl5_4),
% 1.20/0.52    inference(avatar_split_clause,[],[f32,f60])).
% 1.20/0.52  fof(f32,plain,(
% 1.20/0.52    v4_pre_topc(sK2,sK0)),
% 1.20/0.52    inference(cnf_transformation,[],[f22])).
% 1.20/0.52  fof(f58,plain,(
% 1.20/0.52    spl5_3),
% 1.20/0.52    inference(avatar_split_clause,[],[f33,f55])).
% 1.20/0.52  fof(f33,plain,(
% 1.20/0.52    v2_tex_2(sK1,sK0)),
% 1.20/0.52    inference(cnf_transformation,[],[f22])).
% 1.20/0.52  fof(f53,plain,(
% 1.20/0.52    spl5_2),
% 1.20/0.52    inference(avatar_split_clause,[],[f34,f50])).
% 1.20/0.52  fof(f34,plain,(
% 1.20/0.52    v2_tex_2(sK2,sK0)),
% 1.20/0.52    inference(cnf_transformation,[],[f22])).
% 1.20/0.52  fof(f48,plain,(
% 1.20/0.52    ~spl5_1),
% 1.20/0.52    inference(avatar_split_clause,[],[f35,f45])).
% 1.20/0.52  fof(f35,plain,(
% 1.20/0.52    ~v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 1.20/0.52    inference(cnf_transformation,[],[f22])).
% 1.20/0.52  % SZS output end Proof for theBenchmark
% 1.20/0.52  % (1129)------------------------------
% 1.20/0.52  % (1129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (1129)Termination reason: Refutation
% 1.20/0.52  
% 1.20/0.52  % (1129)Memory used [KB]: 10874
% 1.20/0.52  % (1129)Time elapsed: 0.093 s
% 1.20/0.52  % (1129)------------------------------
% 1.20/0.52  % (1129)------------------------------
% 1.20/0.53  % (1120)Success in time 0.167 s
%------------------------------------------------------------------------------
