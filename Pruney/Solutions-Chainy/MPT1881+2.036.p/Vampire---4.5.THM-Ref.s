%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 384 expanded)
%              Number of leaves         :   37 ( 164 expanded)
%              Depth                    :   11
%              Number of atoms          :  595 (1727 expanded)
%              Number of equality atoms :   45 ( 104 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f634,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f82,f87,f92,f97,f102,f107,f129,f186,f220,f383,f388,f428,f433,f453,f459,f460,f510,f511,f513,f518,f555,f578,f579,f587,f632])).

fof(f632,plain,
    ( ~ spl4_26
    | spl4_25
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f629,f569,f400,f405])).

fof(f405,plain,
    ( spl4_26
  <=> r2_hidden(sK3(sK2(sK0,sK1),sK1),sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f400,plain,
    ( spl4_25
  <=> r2_hidden(sK3(sK2(sK0,sK1),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f569,plain,
    ( spl4_27
  <=> m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f629,plain,
    ( ~ r2_hidden(sK3(sK2(sK0,sK1),sK1),sK2(sK0,sK1))
    | spl4_25
    | ~ spl4_27 ),
    inference(unit_resulting_resolution,[],[f570,f402,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f402,plain,
    ( ~ r2_hidden(sK3(sK2(sK0,sK1),sK1),sK1)
    | spl4_25 ),
    inference(avatar_component_clause,[],[f400])).

fof(f570,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f569])).

fof(f587,plain,
    ( spl4_27
    | ~ spl4_9
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f586,f206,f154,f569])).

fof(f154,plain,
    ( spl4_9
  <=> u1_struct_0(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f206,plain,
    ( spl4_15
  <=> m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f586,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl4_9
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f208,f156])).

fof(f156,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f154])).

fof(f208,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f206])).

fof(f579,plain,
    ( spl4_26
    | spl4_19 ),
    inference(avatar_split_clause,[],[f574,f323,f405])).

fof(f323,plain,
    ( spl4_19
  <=> r1_tarski(sK2(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f574,plain,
    ( r2_hidden(sK3(sK2(sK0,sK1),sK1),sK2(sK0,sK1))
    | spl4_19 ),
    inference(unit_resulting_resolution,[],[f325,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f325,plain,
    ( ~ r1_tarski(sK2(sK0,sK1),sK1)
    | spl4_19 ),
    inference(avatar_component_clause,[],[f323])).

fof(f578,plain,
    ( ~ spl4_25
    | spl4_19 ),
    inference(avatar_split_clause,[],[f575,f323,f400])).

fof(f575,plain,
    ( ~ r2_hidden(sK3(sK2(sK0,sK1),sK1),sK1)
    | spl4_19 ),
    inference(unit_resulting_resolution,[],[f325,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f555,plain,
    ( ~ spl4_19
    | ~ spl4_12
    | spl4_13 ),
    inference(avatar_split_clause,[],[f552,f178,f171,f323])).

fof(f171,plain,
    ( spl4_12
  <=> r1_tarski(sK1,sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f178,plain,
    ( spl4_13
  <=> sK1 = sK2(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f552,plain,
    ( ~ r1_tarski(sK2(sK0,sK1),sK1)
    | ~ spl4_12
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f173,f180,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f180,plain,
    ( sK1 != sK2(sK0,sK1)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f178])).

fof(f173,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f171])).

fof(f518,plain,
    ( spl4_9
    | spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f516,f84,f78,f154])).

fof(f78,plain,
    ( spl4_2
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f84,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f516,plain,
    ( u1_struct_0(sK0) = sK1
    | spl4_2
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f86,f79,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f79,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f86,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f513,plain,
    ( spl4_15
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f502,f159,f89,f84,f74,f206])).

fof(f74,plain,
    ( spl4_1
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f89,plain,
    ( spl4_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f159,plain,
    ( spl4_10
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f502,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f91,f161,f86,f76,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK2(X0,X1) != X1
                & r1_tarski(X1,sK2(X0,X1))
                & v2_tex_2(sK2(X0,X1),X0)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK2(X0,X1) != X1
        & r1_tarski(X1,sK2(X0,X1))
        & v2_tex_2(sK2(X0,X1),X0)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(f76,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f161,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f159])).

fof(f91,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f511,plain,
    ( spl4_12
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f504,f159,f89,f84,f74,f171])).

fof(f504,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f91,f161,f86,f76,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | r1_tarski(X1,sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f510,plain,
    ( ~ spl4_13
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f505,f159,f89,f84,f74,f178])).

fof(f505,plain,
    ( sK1 != sK2(sK0,sK1)
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f91,f161,f86,f76,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | sK2(X0,X1) != X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f460,plain,
    ( u1_struct_0(sK0) != sK1
    | v1_subset_1(sK1,sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f459,plain,
    ( ~ spl4_17
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f457,f275,f270])).

fof(f270,plain,
    ( spl4_17
  <=> v1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f275,plain,
    ( spl4_18
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f457,plain,
    ( ~ v1_subset_1(sK1,sK1)
    | ~ spl4_18 ),
    inference(resolution,[],[f277,f70])).

fof(f70,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f277,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f275])).

fof(f453,plain,
    ( spl4_18
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f254,f154,f84,f275])).

fof(f254,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f86,f156])).

fof(f433,plain,
    ( spl4_9
    | ~ spl4_22
    | ~ spl4_8
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f432,f218,f126,f370,f154])).

fof(f370,plain,
    ( spl4_22
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f126,plain,
    ( spl4_8
  <=> v2_tex_2(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f218,plain,
    ( spl4_16
  <=> ! [X0] :
        ( sK1 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ r1_tarski(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f432,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = sK1
    | ~ spl4_8
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f431,f48])).

fof(f48,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f431,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ r1_tarski(sK1,k2_subset_1(u1_struct_0(sK0)))
    | ~ spl4_8
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f430,f128])).

fof(f128,plain,
    ( v2_tex_2(u1_struct_0(sK0),sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f126])).

fof(f430,plain,
    ( ~ v2_tex_2(u1_struct_0(sK0),sK0)
    | u1_struct_0(sK0) = sK1
    | ~ r1_tarski(sK1,k2_subset_1(u1_struct_0(sK0)))
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f364,f48])).

fof(f364,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ v2_tex_2(k2_subset_1(u1_struct_0(sK0)),sK0)
    | ~ r1_tarski(sK1,k2_subset_1(u1_struct_0(sK0)))
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f361,f48])).

fof(f361,plain,
    ( sK1 = k2_subset_1(u1_struct_0(sK0))
    | ~ v2_tex_2(k2_subset_1(u1_struct_0(sK0)),sK0)
    | ~ r1_tarski(sK1,k2_subset_1(u1_struct_0(sK0)))
    | ~ spl4_16 ),
    inference(resolution,[],[f219,f49])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f219,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK1 = X0
        | ~ v2_tex_2(X0,sK0)
        | ~ r1_tarski(sK1,X0) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f218])).

fof(f428,plain,
    ( spl4_23
    | ~ spl4_3
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f423,f385,f84,f380])).

fof(f380,plain,
    ( spl4_23
  <=> r2_hidden(sK3(sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f385,plain,
    ( spl4_24
  <=> r2_hidden(sK3(sK1,u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f423,plain,
    ( r2_hidden(sK3(sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl4_3
    | ~ spl4_24 ),
    inference(resolution,[],[f387,f151])).

fof(f151,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK1)
        | r2_hidden(X2,u1_struct_0(sK0)) )
    | ~ spl4_3 ),
    inference(resolution,[],[f86,f61])).

fof(f387,plain,
    ( r2_hidden(sK3(sK1,u1_struct_0(sK0)),sK1)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f385])).

fof(f388,plain,
    ( spl4_24
    | spl4_22 ),
    inference(avatar_split_clause,[],[f375,f370,f385])).

fof(f375,plain,
    ( r2_hidden(sK3(sK1,u1_struct_0(sK0)),sK1)
    | spl4_22 ),
    inference(unit_resulting_resolution,[],[f372,f66])).

fof(f372,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | spl4_22 ),
    inference(avatar_component_clause,[],[f370])).

fof(f383,plain,
    ( ~ spl4_23
    | spl4_22 ),
    inference(avatar_split_clause,[],[f376,f370,f380])).

fof(f376,plain,
    ( ~ r2_hidden(sK3(sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | spl4_22 ),
    inference(unit_resulting_resolution,[],[f372,f67])).

fof(f220,plain,
    ( ~ spl4_1
    | spl4_16
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f216,f89,f84,f218,f74])).

fof(f216,plain,
    ( ! [X0] :
        ( sK1 = X0
        | ~ r1_tarski(sK1,X0)
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tex_2(sK1,sK0) )
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f144,f91])).

fof(f144,plain,
    ( ! [X0] :
        ( sK1 = X0
        | ~ r1_tarski(sK1,X0)
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tex_2(sK1,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f86,f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( X1 = X3
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f186,plain,
    ( spl4_10
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f185,f104,f99,f94,f89,f84,f159])).

fof(f94,plain,
    ( spl4_5
  <=> v1_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f99,plain,
    ( spl4_6
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f104,plain,
    ( spl4_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f185,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7 ),
    inference(subsumption_resolution,[],[f184,f106])).

fof(f106,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f104])).

fof(f184,plain,
    ( v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f183,f101])).

fof(f101,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f183,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f182,f96])).

fof(f96,plain,
    ( v1_tdlat_3(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f182,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f150,f91])).

fof(f150,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f86,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

fof(f129,plain,
    ( spl4_8
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f124,f104,f99,f94,f89,f126])).

fof(f124,plain,
    ( v2_tex_2(u1_struct_0(sK0),sK0)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7 ),
    inference(forward_demodulation,[],[f120,f48])).

fof(f120,plain,
    ( v2_tex_2(k2_subset_1(u1_struct_0(sK0)),sK0)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7 ),
    inference(unit_resulting_resolution,[],[f91,f101,f96,f49,f106,f56])).

fof(f107,plain,(
    ~ spl4_7 ),
    inference(avatar_split_clause,[],[f41,f104])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( v1_subset_1(sK1,u1_struct_0(sK0))
      | ~ v3_tex_2(sK1,sK0) )
    & ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
      | v3_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v1_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( v1_subset_1(X1,u1_struct_0(X0))
              | ~ v3_tex_2(X1,X0) )
            & ( ~ v1_subset_1(X1,u1_struct_0(X0))
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(sK0))
            | ~ v3_tex_2(X1,sK0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(sK0))
            | v3_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v1_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ( v1_subset_1(X1,u1_struct_0(sK0))
          | ~ v3_tex_2(X1,sK0) )
        & ( ~ v1_subset_1(X1,u1_struct_0(sK0))
          | v3_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( v1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v3_tex_2(sK1,sK0) )
      & ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
        | v3_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

fof(f102,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f42,f99])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f97,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f43,f94])).

fof(f43,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f92,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f44,f89])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f87,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f45,f84])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f82,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f46,f78,f74])).

fof(f46,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f81,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f47,f78,f74])).

fof(f47,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:35:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (27628)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.48  % (27645)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.49  % (27645)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f634,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f81,f82,f87,f92,f97,f102,f107,f129,f186,f220,f383,f388,f428,f433,f453,f459,f460,f510,f511,f513,f518,f555,f578,f579,f587,f632])).
% 0.20/0.51  fof(f632,plain,(
% 0.20/0.51    ~spl4_26 | spl4_25 | ~spl4_27),
% 0.20/0.51    inference(avatar_split_clause,[],[f629,f569,f400,f405])).
% 0.20/0.51  fof(f405,plain,(
% 0.20/0.51    spl4_26 <=> r2_hidden(sK3(sK2(sK0,sK1),sK1),sK2(sK0,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.20/0.51  fof(f400,plain,(
% 0.20/0.51    spl4_25 <=> r2_hidden(sK3(sK2(sK0,sK1),sK1),sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.20/0.51  fof(f569,plain,(
% 0.20/0.51    spl4_27 <=> m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.20/0.51  fof(f629,plain,(
% 0.20/0.51    ~r2_hidden(sK3(sK2(sK0,sK1),sK1),sK2(sK0,sK1)) | (spl4_25 | ~spl4_27)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f570,f402,f61])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.51  fof(f402,plain,(
% 0.20/0.51    ~r2_hidden(sK3(sK2(sK0,sK1),sK1),sK1) | spl4_25),
% 0.20/0.51    inference(avatar_component_clause,[],[f400])).
% 0.20/0.51  fof(f570,plain,(
% 0.20/0.51    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl4_27),
% 0.20/0.51    inference(avatar_component_clause,[],[f569])).
% 0.20/0.51  fof(f587,plain,(
% 0.20/0.51    spl4_27 | ~spl4_9 | ~spl4_15),
% 0.20/0.51    inference(avatar_split_clause,[],[f586,f206,f154,f569])).
% 0.20/0.51  fof(f154,plain,(
% 0.20/0.51    spl4_9 <=> u1_struct_0(sK0) = sK1),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.51  fof(f206,plain,(
% 0.20/0.51    spl4_15 <=> m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.51  fof(f586,plain,(
% 0.20/0.51    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1)) | (~spl4_9 | ~spl4_15)),
% 0.20/0.51    inference(forward_demodulation,[],[f208,f156])).
% 0.20/0.51  fof(f156,plain,(
% 0.20/0.51    u1_struct_0(sK0) = sK1 | ~spl4_9),
% 0.20/0.51    inference(avatar_component_clause,[],[f154])).
% 0.20/0.51  fof(f208,plain,(
% 0.20/0.51    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_15),
% 0.20/0.51    inference(avatar_component_clause,[],[f206])).
% 0.20/0.51  fof(f579,plain,(
% 0.20/0.51    spl4_26 | spl4_19),
% 0.20/0.51    inference(avatar_split_clause,[],[f574,f323,f405])).
% 0.20/0.51  fof(f323,plain,(
% 0.20/0.51    spl4_19 <=> r1_tarski(sK2(sK0,sK1),sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.20/0.51  fof(f574,plain,(
% 0.20/0.51    r2_hidden(sK3(sK2(sK0,sK1),sK1),sK2(sK0,sK1)) | spl4_19),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f325,f66])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(rectify,[],[f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(nnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.51  fof(f325,plain,(
% 0.20/0.51    ~r1_tarski(sK2(sK0,sK1),sK1) | spl4_19),
% 0.20/0.51    inference(avatar_component_clause,[],[f323])).
% 0.20/0.51  fof(f578,plain,(
% 0.20/0.51    ~spl4_25 | spl4_19),
% 0.20/0.51    inference(avatar_split_clause,[],[f575,f323,f400])).
% 0.20/0.51  fof(f575,plain,(
% 0.20/0.51    ~r2_hidden(sK3(sK2(sK0,sK1),sK1),sK1) | spl4_19),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f325,f67])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f40])).
% 0.20/0.51  fof(f555,plain,(
% 0.20/0.51    ~spl4_19 | ~spl4_12 | spl4_13),
% 0.20/0.51    inference(avatar_split_clause,[],[f552,f178,f171,f323])).
% 0.20/0.51  fof(f171,plain,(
% 0.20/0.51    spl4_12 <=> r1_tarski(sK1,sK2(sK0,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.51  fof(f178,plain,(
% 0.20/0.51    spl4_13 <=> sK1 = sK2(sK0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.51  fof(f552,plain,(
% 0.20/0.51    ~r1_tarski(sK2(sK0,sK1),sK1) | (~spl4_12 | spl4_13)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f173,f180,f64])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.51    inference(flattening,[],[f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.51  fof(f180,plain,(
% 0.20/0.51    sK1 != sK2(sK0,sK1) | spl4_13),
% 0.20/0.51    inference(avatar_component_clause,[],[f178])).
% 0.20/0.51  fof(f173,plain,(
% 0.20/0.51    r1_tarski(sK1,sK2(sK0,sK1)) | ~spl4_12),
% 0.20/0.51    inference(avatar_component_clause,[],[f171])).
% 0.20/0.51  fof(f518,plain,(
% 0.20/0.51    spl4_9 | spl4_2 | ~spl4_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f516,f84,f78,f154])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    spl4_2 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    spl4_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.51  fof(f516,plain,(
% 0.20/0.51    u1_struct_0(sK0) = sK1 | (spl4_2 | ~spl4_3)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f86,f79,f60])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(nnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl4_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f78])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f84])).
% 0.20/0.51  fof(f513,plain,(
% 0.20/0.51    spl4_15 | spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_10),
% 0.20/0.51    inference(avatar_split_clause,[],[f502,f159,f89,f84,f74,f206])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    spl4_1 <=> v3_tex_2(sK1,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    spl4_4 <=> l1_pre_topc(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.51  fof(f159,plain,(
% 0.20/0.51    spl4_10 <=> v2_tex_2(sK1,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.51  fof(f502,plain,(
% 0.20/0.51    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_10)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f91,f161,f86,f76,f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v3_tex_2(X1,X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(rectify,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    ~v3_tex_2(sK1,sK0) | spl4_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f74])).
% 0.20/0.51  fof(f161,plain,(
% 0.20/0.51    v2_tex_2(sK1,sK0) | ~spl4_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f159])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    l1_pre_topc(sK0) | ~spl4_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f89])).
% 0.20/0.51  fof(f511,plain,(
% 0.20/0.51    spl4_12 | spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_10),
% 0.20/0.51    inference(avatar_split_clause,[],[f504,f159,f89,f84,f74,f171])).
% 0.20/0.51  fof(f504,plain,(
% 0.20/0.51    r1_tarski(sK1,sK2(sK0,sK1)) | (spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_10)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f91,f161,f86,f76,f54])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v3_tex_2(X1,X0) | r1_tarski(X1,sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f32])).
% 0.20/0.51  fof(f510,plain,(
% 0.20/0.51    ~spl4_13 | spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_10),
% 0.20/0.51    inference(avatar_split_clause,[],[f505,f159,f89,f84,f74,f178])).
% 0.20/0.51  fof(f505,plain,(
% 0.20/0.51    sK1 != sK2(sK0,sK1) | (spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_10)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f91,f161,f86,f76,f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v3_tex_2(X1,X0) | sK2(X0,X1) != X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f32])).
% 0.20/0.51  fof(f460,plain,(
% 0.20/0.51    u1_struct_0(sK0) != sK1 | v1_subset_1(sK1,sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.51  fof(f459,plain,(
% 0.20/0.51    ~spl4_17 | ~spl4_18),
% 0.20/0.51    inference(avatar_split_clause,[],[f457,f275,f270])).
% 0.20/0.51  fof(f270,plain,(
% 0.20/0.51    spl4_17 <=> v1_subset_1(sK1,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.20/0.51  fof(f275,plain,(
% 0.20/0.51    spl4_18 <=> m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.51  fof(f457,plain,(
% 0.20/0.51    ~v1_subset_1(sK1,sK1) | ~spl4_18),
% 0.20/0.51    inference(resolution,[],[f277,f70])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 0.20/0.51    inference(equality_resolution,[],[f59])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f34])).
% 0.20/0.51  fof(f277,plain,(
% 0.20/0.51    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl4_18),
% 0.20/0.51    inference(avatar_component_clause,[],[f275])).
% 0.20/0.51  fof(f453,plain,(
% 0.20/0.51    spl4_18 | ~spl4_3 | ~spl4_9),
% 0.20/0.51    inference(avatar_split_clause,[],[f254,f154,f84,f275])).
% 0.20/0.51  fof(f254,plain,(
% 0.20/0.51    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | (~spl4_3 | ~spl4_9)),
% 0.20/0.51    inference(backward_demodulation,[],[f86,f156])).
% 0.20/0.51  fof(f433,plain,(
% 0.20/0.51    spl4_9 | ~spl4_22 | ~spl4_8 | ~spl4_16),
% 0.20/0.51    inference(avatar_split_clause,[],[f432,f218,f126,f370,f154])).
% 0.20/0.51  fof(f370,plain,(
% 0.20/0.51    spl4_22 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    spl4_8 <=> v2_tex_2(u1_struct_0(sK0),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.51  fof(f218,plain,(
% 0.20/0.51    spl4_16 <=> ! [X0] : (sK1 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~r1_tarski(sK1,X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.51  fof(f432,plain,(
% 0.20/0.51    ~r1_tarski(sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = sK1 | (~spl4_8 | ~spl4_16)),
% 0.20/0.51    inference(forward_demodulation,[],[f431,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.51  fof(f431,plain,(
% 0.20/0.51    u1_struct_0(sK0) = sK1 | ~r1_tarski(sK1,k2_subset_1(u1_struct_0(sK0))) | (~spl4_8 | ~spl4_16)),
% 0.20/0.51    inference(subsumption_resolution,[],[f430,f128])).
% 0.20/0.51  fof(f128,plain,(
% 0.20/0.51    v2_tex_2(u1_struct_0(sK0),sK0) | ~spl4_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f126])).
% 0.20/0.51  fof(f430,plain,(
% 0.20/0.51    ~v2_tex_2(u1_struct_0(sK0),sK0) | u1_struct_0(sK0) = sK1 | ~r1_tarski(sK1,k2_subset_1(u1_struct_0(sK0))) | ~spl4_16),
% 0.20/0.51    inference(forward_demodulation,[],[f364,f48])).
% 0.20/0.51  fof(f364,plain,(
% 0.20/0.51    u1_struct_0(sK0) = sK1 | ~v2_tex_2(k2_subset_1(u1_struct_0(sK0)),sK0) | ~r1_tarski(sK1,k2_subset_1(u1_struct_0(sK0))) | ~spl4_16),
% 0.20/0.51    inference(forward_demodulation,[],[f361,f48])).
% 0.20/0.51  fof(f361,plain,(
% 0.20/0.51    sK1 = k2_subset_1(u1_struct_0(sK0)) | ~v2_tex_2(k2_subset_1(u1_struct_0(sK0)),sK0) | ~r1_tarski(sK1,k2_subset_1(u1_struct_0(sK0))) | ~spl4_16),
% 0.20/0.51    inference(resolution,[],[f219,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.51  fof(f219,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = X0 | ~v2_tex_2(X0,sK0) | ~r1_tarski(sK1,X0)) ) | ~spl4_16),
% 0.20/0.51    inference(avatar_component_clause,[],[f218])).
% 0.20/0.51  fof(f428,plain,(
% 0.20/0.51    spl4_23 | ~spl4_3 | ~spl4_24),
% 0.20/0.51    inference(avatar_split_clause,[],[f423,f385,f84,f380])).
% 0.20/0.51  fof(f380,plain,(
% 0.20/0.51    spl4_23 <=> r2_hidden(sK3(sK1,u1_struct_0(sK0)),u1_struct_0(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.20/0.51  fof(f385,plain,(
% 0.20/0.51    spl4_24 <=> r2_hidden(sK3(sK1,u1_struct_0(sK0)),sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.20/0.51  fof(f423,plain,(
% 0.20/0.51    r2_hidden(sK3(sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | (~spl4_3 | ~spl4_24)),
% 0.20/0.51    inference(resolution,[],[f387,f151])).
% 0.20/0.51  fof(f151,plain,(
% 0.20/0.51    ( ! [X2] : (~r2_hidden(X2,sK1) | r2_hidden(X2,u1_struct_0(sK0))) ) | ~spl4_3),
% 0.20/0.51    inference(resolution,[],[f86,f61])).
% 0.20/0.51  fof(f387,plain,(
% 0.20/0.51    r2_hidden(sK3(sK1,u1_struct_0(sK0)),sK1) | ~spl4_24),
% 0.20/0.51    inference(avatar_component_clause,[],[f385])).
% 0.20/0.51  fof(f388,plain,(
% 0.20/0.51    spl4_24 | spl4_22),
% 0.20/0.51    inference(avatar_split_clause,[],[f375,f370,f385])).
% 0.20/0.51  fof(f375,plain,(
% 0.20/0.51    r2_hidden(sK3(sK1,u1_struct_0(sK0)),sK1) | spl4_22),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f372,f66])).
% 0.20/0.51  fof(f372,plain,(
% 0.20/0.51    ~r1_tarski(sK1,u1_struct_0(sK0)) | spl4_22),
% 0.20/0.51    inference(avatar_component_clause,[],[f370])).
% 0.20/0.51  fof(f383,plain,(
% 0.20/0.51    ~spl4_23 | spl4_22),
% 0.20/0.51    inference(avatar_split_clause,[],[f376,f370,f380])).
% 0.20/0.51  fof(f376,plain,(
% 0.20/0.51    ~r2_hidden(sK3(sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | spl4_22),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f372,f67])).
% 0.20/0.51  fof(f220,plain,(
% 0.20/0.51    ~spl4_1 | spl4_16 | ~spl4_3 | ~spl4_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f216,f89,f84,f218,f74])).
% 0.20/0.51  fof(f216,plain,(
% 0.20/0.51    ( ! [X0] : (sK1 = X0 | ~r1_tarski(sK1,X0) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tex_2(sK1,sK0)) ) | (~spl4_3 | ~spl4_4)),
% 0.20/0.51    inference(subsumption_resolution,[],[f144,f91])).
% 0.20/0.51  fof(f144,plain,(
% 0.20/0.51    ( ! [X0] : (sK1 = X0 | ~r1_tarski(sK1,X0) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)) ) | ~spl4_3),
% 0.20/0.51    inference(resolution,[],[f86,f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f32])).
% 0.20/0.51  fof(f186,plain,(
% 0.20/0.51    spl4_10 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | spl4_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f185,f104,f99,f94,f89,f84,f159])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    spl4_5 <=> v1_tdlat_3(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.51  fof(f99,plain,(
% 0.20/0.51    spl4_6 <=> v2_pre_topc(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.51  fof(f104,plain,(
% 0.20/0.51    spl4_7 <=> v2_struct_0(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.51  fof(f185,plain,(
% 0.20/0.51    v2_tex_2(sK1,sK0) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | spl4_7)),
% 0.20/0.51    inference(subsumption_resolution,[],[f184,f106])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    ~v2_struct_0(sK0) | spl4_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f104])).
% 0.20/0.51  fof(f184,plain,(
% 0.20/0.51    v2_tex_2(sK1,sK0) | v2_struct_0(sK0) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6)),
% 0.20/0.51    inference(subsumption_resolution,[],[f183,f101])).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    v2_pre_topc(sK0) | ~spl4_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f99])).
% 0.20/0.51  fof(f183,plain,(
% 0.20/0.51    v2_tex_2(sK1,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.20/0.51    inference(subsumption_resolution,[],[f182,f96])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    v1_tdlat_3(sK0) | ~spl4_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f94])).
% 0.20/0.51  fof(f182,plain,(
% 0.20/0.51    v2_tex_2(sK1,sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_3 | ~spl4_4)),
% 0.20/0.51    inference(subsumption_resolution,[],[f150,f91])).
% 0.20/0.51  fof(f150,plain,(
% 0.20/0.51    v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_3),
% 0.20/0.51    inference(resolution,[],[f86,f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).
% 0.20/0.51  fof(f129,plain,(
% 0.20/0.51    spl4_8 | ~spl4_4 | ~spl4_5 | ~spl4_6 | spl4_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f124,f104,f99,f94,f89,f126])).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    v2_tex_2(u1_struct_0(sK0),sK0) | (~spl4_4 | ~spl4_5 | ~spl4_6 | spl4_7)),
% 0.20/0.51    inference(forward_demodulation,[],[f120,f48])).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    v2_tex_2(k2_subset_1(u1_struct_0(sK0)),sK0) | (~spl4_4 | ~spl4_5 | ~spl4_6 | spl4_7)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f91,f101,f96,f49,f106,f56])).
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    ~spl4_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f41,f104])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ~v2_struct_0(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ((v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)) & (~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f26,f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK0)) | ~v3_tex_2(X1,sK0)) & (~v1_subset_1(X1,u1_struct_0(sK0)) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ? [X1] : ((v1_subset_1(X1,u1_struct_0(sK0)) | ~v3_tex_2(X1,sK0)) & (~v1_subset_1(X1,u1_struct_0(sK0)) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)) & (~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.20/0.51    inference(negated_conjecture,[],[f10])).
% 0.20/0.51  fof(f10,conjecture,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    spl4_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f42,f99])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    v2_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    spl4_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f43,f94])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    v1_tdlat_3(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    spl4_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f44,f89])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    l1_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    spl4_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f45,f84])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    spl4_1 | ~spl4_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f46,f78,f74])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    ~spl4_1 | spl4_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f47,f78,f74])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (27645)------------------------------
% 0.20/0.51  % (27645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (27645)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (27645)Memory used [KB]: 6524
% 0.20/0.51  % (27645)Time elapsed: 0.083 s
% 0.20/0.51  % (27645)------------------------------
% 0.20/0.51  % (27645)------------------------------
% 0.20/0.51  % (27614)Success in time 0.156 s
%------------------------------------------------------------------------------
