%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 342 expanded)
%              Number of leaves         :   34 ( 148 expanded)
%              Depth                    :   14
%              Number of atoms          :  549 (1320 expanded)
%              Number of equality atoms :   46 ( 151 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f338,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f61,f66,f71,f76,f81,f91,f96,f101,f128,f141,f149,f154,f161,f168,f191,f199,f209,f214,f229,f291,f328,f337])).

fof(f337,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_37
    | ~ spl4_40 ),
    inference(avatar_contradiction_clause,[],[f336])).

fof(f336,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_37
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f335,f55])).

fof(f55,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl4_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f335,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_2
    | ~ spl4_4
    | spl4_37
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f334,f60])).

fof(f60,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl4_2
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f334,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_4
    | spl4_37
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f333,f70])).

fof(f70,plain,
    ( v1_tex_2(sK1,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl4_4
  <=> v1_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f333,plain,
    ( ~ v1_tex_2(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl4_37
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f331,f290])).

fof(f290,plain,
    ( ~ v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | spl4_37 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl4_37
  <=> v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f331,plain,
    ( v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_40 ),
    inference(resolution,[],[f327,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK3(X0,X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f327,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f325])).

fof(f325,plain,
    ( spl4_40
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f328,plain,
    ( spl4_40
    | ~ spl4_16
    | ~ spl4_25
    | ~ spl4_26
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f278,f226,f211,f207,f151,f325])).

fof(f151,plain,
    ( spl4_16
  <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f207,plain,
    ( spl4_25
  <=> ! [X2] :
        ( u1_struct_0(X2) = u1_struct_0(sK2)
        | ~ m1_pre_topc(X2,sK2)
        | ~ m1_pre_topc(sK2,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f211,plain,
    ( spl4_26
  <=> m1_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f226,plain,
    ( spl4_27
  <=> m1_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f278,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_16
    | ~ spl4_25
    | ~ spl4_26
    | ~ spl4_27 ),
    inference(backward_demodulation,[],[f153,f242])).

fof(f242,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl4_25
    | ~ spl4_26
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f239,f213])).

fof(f213,plain,
    ( m1_pre_topc(sK2,sK1)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f211])).

fof(f239,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ spl4_25
    | ~ spl4_27 ),
    inference(resolution,[],[f228,f208])).

fof(f208,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,sK2)
        | u1_struct_0(X2) = u1_struct_0(sK2)
        | ~ m1_pre_topc(sK2,X2) )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f207])).

fof(f228,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f226])).

fof(f153,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f151])).

fof(f291,plain,
    ( ~ spl4_37
    | spl4_13
    | ~ spl4_25
    | ~ spl4_26
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f279,f226,f211,f207,f138,f288])).

fof(f138,plain,
    ( spl4_13
  <=> v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f279,plain,
    ( ~ v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | spl4_13
    | ~ spl4_25
    | ~ spl4_26
    | ~ spl4_27 ),
    inference(backward_demodulation,[],[f140,f242])).

fof(f140,plain,
    ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f138])).

fof(f229,plain,
    ( spl4_27
    | ~ spl4_7
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f223,f197,f88,f226])).

fof(f88,plain,
    ( spl4_7
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f197,plain,
    ( spl4_23
  <=> ! [X1] :
        ( m1_pre_topc(X1,sK2)
        | ~ m1_pre_topc(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f223,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ spl4_7
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f222,f90])).

fof(f90,plain,
    ( l1_pre_topc(sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f88])).

fof(f222,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ l1_pre_topc(sK1)
    | ~ spl4_23 ),
    inference(resolution,[],[f198,f36])).

fof(f36,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f198,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK1)
        | m1_pre_topc(X1,sK2) )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f197])).

fof(f214,plain,
    ( spl4_26
    | ~ spl4_9
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f205,f189,f98,f211])).

fof(f98,plain,
    ( spl4_9
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f189,plain,
    ( spl4_21
  <=> ! [X0] :
        ( m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f205,plain,
    ( m1_pre_topc(sK2,sK1)
    | ~ spl4_9
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f204,f100])).

fof(f100,plain,
    ( l1_pre_topc(sK2)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f98])).

fof(f204,plain,
    ( m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK2)
    | ~ spl4_21 ),
    inference(resolution,[],[f190,f36])).

fof(f190,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | m1_pre_topc(X0,sK1) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f189])).

fof(f209,plain,
    ( spl4_25
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f180,f98,f207])).

fof(f180,plain,
    ( ! [X2] :
        ( u1_struct_0(X2) = u1_struct_0(sK2)
        | ~ m1_pre_topc(X2,sK2)
        | ~ m1_pre_topc(sK2,X2) )
    | ~ spl4_9 ),
    inference(resolution,[],[f164,f100])).

fof(f164,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | u1_struct_0(X0) = u1_struct_0(X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(subsumption_resolution,[],[f162,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X0) = u1_struct_0(X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f86,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1)
      | u1_struct_0(X0) = u1_struct_0(X1) ) ),
    inference(resolution,[],[f40,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f199,plain,
    ( spl4_23
    | ~ spl4_7
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f187,f166,f88,f197])).

fof(f166,plain,
    ( spl4_18
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | m1_pre_topc(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f187,plain,
    ( ! [X1] :
        ( m1_pre_topc(X1,sK2)
        | ~ m1_pre_topc(X1,sK1) )
    | ~ spl4_7
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f185,f90])).

fof(f185,plain,
    ( ! [X1] :
        ( m1_pre_topc(X1,sK2)
        | ~ m1_pre_topc(X1,sK1)
        | ~ l1_pre_topc(sK1) )
    | ~ spl4_18 ),
    inference(resolution,[],[f167,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f37,f39])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f167,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | m1_pre_topc(X0,sK2) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f166])).

fof(f191,plain,
    ( spl4_21
    | ~ spl4_15
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f181,f159,f147,f189])).

fof(f147,plain,
    ( spl4_15
  <=> ! [X0] :
        ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ m1_pre_topc(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f159,plain,
    ( spl4_17
  <=> ! [X1] :
        ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | m1_pre_topc(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f181,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(X0,sK2) )
    | ~ spl4_15
    | ~ spl4_17 ),
    inference(resolution,[],[f160,f148])).

fof(f148,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ m1_pre_topc(X0,sK2) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f147])).

fof(f160,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | m1_pre_topc(X1,sK1) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f159])).

fof(f168,plain,
    ( spl4_18
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f107,f98,f93,f166])).

fof(f93,plain,
    ( spl4_8
  <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | m1_pre_topc(X0,sK2) )
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f105,f95])).

fof(f95,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f93])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
        | m1_pre_topc(X0,sK2) )
    | ~ spl4_9 ),
    inference(resolution,[],[f100,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f161,plain,
    ( spl4_17
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f104,f88,f159])).

fof(f104,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | m1_pre_topc(X1,sK1) )
    | ~ spl4_7 ),
    inference(resolution,[],[f45,f90])).

fof(f154,plain,
    ( spl4_16
    | ~ spl4_1
    | ~ spl4_3
    | spl4_5
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f133,f125,f73,f63,f53,f151])).

fof(f63,plain,
    ( spl4_3
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f73,plain,
    ( spl4_5
  <=> v1_tex_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f125,plain,
    ( spl4_12
  <=> u1_struct_0(sK2) = sK3(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f133,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_1
    | ~ spl4_3
    | spl4_5
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f132,f55])).

fof(f132,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_3
    | spl4_5
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f131,f65])).

fof(f65,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f131,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | spl4_5
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f129,f75])).

fof(f75,plain,
    ( ~ v1_tex_2(sK2,sK0)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f129,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tex_2(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_12 ),
    inference(superposition,[],[f42,f127])).

fof(f127,plain,
    ( u1_struct_0(sK2) = sK3(sK0,sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f125])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f149,plain,
    ( spl4_15
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f114,f98,f93,f147])).

fof(f114,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ m1_pre_topc(X0,sK2) )
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f113,f100])).

fof(f113,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ m1_pre_topc(X0,sK2)
        | ~ l1_pre_topc(sK2) )
    | ~ spl4_8 ),
    inference(superposition,[],[f108,f95])).

fof(f141,plain,
    ( ~ spl4_13
    | ~ spl4_1
    | ~ spl4_3
    | spl4_5
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f136,f125,f73,f63,f53,f138])).

fof(f136,plain,
    ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ spl4_1
    | ~ spl4_3
    | spl4_5
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f135,f55])).

fof(f135,plain,
    ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_3
    | spl4_5
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f134,f65])).

fof(f134,plain,
    ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | spl4_5
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f130,f75])).

fof(f130,plain,
    ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))
    | v1_tex_2(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_12 ),
    inference(superposition,[],[f44,f127])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f128,plain,
    ( spl4_12
    | ~ spl4_1
    | ~ spl4_3
    | spl4_5 ),
    inference(avatar_split_clause,[],[f122,f73,f63,f53,f125])).

fof(f122,plain,
    ( u1_struct_0(sK2) = sK3(sK0,sK2)
    | ~ spl4_1
    | ~ spl4_3
    | spl4_5 ),
    inference(subsumption_resolution,[],[f121,f55])).

fof(f121,plain,
    ( u1_struct_0(sK2) = sK3(sK0,sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_3
    | spl4_5 ),
    inference(subsumption_resolution,[],[f120,f65])).

fof(f120,plain,
    ( u1_struct_0(sK2) = sK3(sK0,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | spl4_5 ),
    inference(resolution,[],[f43,f75])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK3(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f101,plain,
    ( spl4_9
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f84,f79,f63,f98])).

fof(f79,plain,
    ( spl4_6
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f84,plain,
    ( l1_pre_topc(sK2)
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(resolution,[],[f80,f65])).

fof(f80,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f96,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f33,f93])).

fof(f33,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ v1_tex_2(sK2,sK0)
    & v1_tex_2(sK1,sK0)
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    & m1_pre_topc(sK2,sK0)
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f21,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tex_2(X2,X0)
                & v1_tex_2(X1,X0)
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X2,X0) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,sK0)
              & v1_tex_2(X1,sK0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,sK0) )
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v1_tex_2(X2,sK0)
            & v1_tex_2(X1,sK0)
            & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
            & m1_pre_topc(X2,sK0) )
        & m1_pre_topc(X1,sK0) )
   => ( ? [X2] :
          ( ~ v1_tex_2(X2,sK0)
          & v1_tex_2(sK1,sK0)
          & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
          & m1_pre_topc(X2,sK0) )
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( ~ v1_tex_2(X2,sK0)
        & v1_tex_2(sK1,sK0)
        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        & m1_pre_topc(X2,sK0) )
   => ( ~ v1_tex_2(sK2,sK0)
      & v1_tex_2(sK1,sK0)
      & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      & m1_pre_topc(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( ( v1_tex_2(X1,X0)
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                 => v1_tex_2(X2,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( ( v1_tex_2(X1,X0)
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
               => v1_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tex_2)).

fof(f91,plain,
    ( spl4_7
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f83,f79,f58,f88])).

fof(f83,plain,
    ( l1_pre_topc(sK1)
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(resolution,[],[f80,f60])).

fof(f81,plain,
    ( spl4_6
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f77,f53,f79])).

fof(f77,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) )
    | ~ spl4_1 ),
    inference(resolution,[],[f39,f55])).

fof(f76,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f35,f73])).

fof(f35,plain,(
    ~ v1_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f34,f68])).

fof(f34,plain,(
    v1_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f32,f63])).

fof(f32,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f31,f58])).

fof(f31,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f56,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f30,f53])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:22:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.56  % (7211)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.56  % (7216)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.56  % (7210)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.56  % (7209)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.57  % (7215)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.57  % (7208)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.57  % (7212)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.57  % (7209)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f338,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f56,f61,f66,f71,f76,f81,f91,f96,f101,f128,f141,f149,f154,f161,f168,f191,f199,f209,f214,f229,f291,f328,f337])).
% 0.21/0.57  fof(f337,plain,(
% 0.21/0.57    ~spl4_1 | ~spl4_2 | ~spl4_4 | spl4_37 | ~spl4_40),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f336])).
% 0.21/0.57  fof(f336,plain,(
% 0.21/0.57    $false | (~spl4_1 | ~spl4_2 | ~spl4_4 | spl4_37 | ~spl4_40)),
% 0.21/0.57    inference(subsumption_resolution,[],[f335,f55])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    l1_pre_topc(sK0) | ~spl4_1),
% 0.21/0.57    inference(avatar_component_clause,[],[f53])).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    spl4_1 <=> l1_pre_topc(sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.57  fof(f335,plain,(
% 0.21/0.57    ~l1_pre_topc(sK0) | (~spl4_2 | ~spl4_4 | spl4_37 | ~spl4_40)),
% 0.21/0.57    inference(subsumption_resolution,[],[f334,f60])).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    m1_pre_topc(sK1,sK0) | ~spl4_2),
% 0.21/0.57    inference(avatar_component_clause,[],[f58])).
% 0.21/0.57  fof(f58,plain,(
% 0.21/0.57    spl4_2 <=> m1_pre_topc(sK1,sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.57  fof(f334,plain,(
% 0.21/0.57    ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | (~spl4_4 | spl4_37 | ~spl4_40)),
% 0.21/0.57    inference(subsumption_resolution,[],[f333,f70])).
% 0.21/0.57  fof(f70,plain,(
% 0.21/0.57    v1_tex_2(sK1,sK0) | ~spl4_4),
% 0.21/0.57    inference(avatar_component_clause,[],[f68])).
% 0.21/0.57  fof(f68,plain,(
% 0.21/0.57    spl4_4 <=> v1_tex_2(sK1,sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.57  fof(f333,plain,(
% 0.21/0.57    ~v1_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | (spl4_37 | ~spl4_40)),
% 0.21/0.57    inference(subsumption_resolution,[],[f331,f290])).
% 0.21/0.57  fof(f290,plain,(
% 0.21/0.57    ~v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) | spl4_37),
% 0.21/0.57    inference(avatar_component_clause,[],[f288])).
% 0.21/0.57  fof(f288,plain,(
% 0.21/0.57    spl4_37 <=> v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.21/0.57  fof(f331,plain,(
% 0.21/0.57    v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~spl4_40),
% 0.21/0.57    inference(resolution,[],[f327,f49])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.57    inference(equality_resolution,[],[f41])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ( ! [X0,X3,X1] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(rectify,[],[f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(nnf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(flattening,[],[f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).
% 0.21/0.57  fof(f327,plain,(
% 0.21/0.57    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_40),
% 0.21/0.57    inference(avatar_component_clause,[],[f325])).
% 0.21/0.57  fof(f325,plain,(
% 0.21/0.57    spl4_40 <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.21/0.57  fof(f328,plain,(
% 0.21/0.57    spl4_40 | ~spl4_16 | ~spl4_25 | ~spl4_26 | ~spl4_27),
% 0.21/0.57    inference(avatar_split_clause,[],[f278,f226,f211,f207,f151,f325])).
% 0.21/0.57  fof(f151,plain,(
% 0.21/0.57    spl4_16 <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.57  fof(f207,plain,(
% 0.21/0.57    spl4_25 <=> ! [X2] : (u1_struct_0(X2) = u1_struct_0(sK2) | ~m1_pre_topc(X2,sK2) | ~m1_pre_topc(sK2,X2))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.21/0.57  fof(f211,plain,(
% 0.21/0.57    spl4_26 <=> m1_pre_topc(sK2,sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.57  fof(f226,plain,(
% 0.21/0.57    spl4_27 <=> m1_pre_topc(sK1,sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.21/0.57  fof(f278,plain,(
% 0.21/0.57    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_16 | ~spl4_25 | ~spl4_26 | ~spl4_27)),
% 0.21/0.57    inference(backward_demodulation,[],[f153,f242])).
% 0.21/0.57  fof(f242,plain,(
% 0.21/0.57    u1_struct_0(sK1) = u1_struct_0(sK2) | (~spl4_25 | ~spl4_26 | ~spl4_27)),
% 0.21/0.57    inference(subsumption_resolution,[],[f239,f213])).
% 0.21/0.57  fof(f213,plain,(
% 0.21/0.57    m1_pre_topc(sK2,sK1) | ~spl4_26),
% 0.21/0.57    inference(avatar_component_clause,[],[f211])).
% 0.21/0.57  fof(f239,plain,(
% 0.21/0.57    u1_struct_0(sK1) = u1_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | (~spl4_25 | ~spl4_27)),
% 0.21/0.57    inference(resolution,[],[f228,f208])).
% 0.21/0.57  fof(f208,plain,(
% 0.21/0.57    ( ! [X2] : (~m1_pre_topc(X2,sK2) | u1_struct_0(X2) = u1_struct_0(sK2) | ~m1_pre_topc(sK2,X2)) ) | ~spl4_25),
% 0.21/0.57    inference(avatar_component_clause,[],[f207])).
% 0.21/0.57  fof(f228,plain,(
% 0.21/0.57    m1_pre_topc(sK1,sK2) | ~spl4_27),
% 0.21/0.57    inference(avatar_component_clause,[],[f226])).
% 0.21/0.57  fof(f153,plain,(
% 0.21/0.57    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_16),
% 0.21/0.57    inference(avatar_component_clause,[],[f151])).
% 0.21/0.57  fof(f291,plain,(
% 0.21/0.57    ~spl4_37 | spl4_13 | ~spl4_25 | ~spl4_26 | ~spl4_27),
% 0.21/0.57    inference(avatar_split_clause,[],[f279,f226,f211,f207,f138,f288])).
% 0.21/0.57  fof(f138,plain,(
% 0.21/0.57    spl4_13 <=> v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.57  fof(f279,plain,(
% 0.21/0.57    ~v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) | (spl4_13 | ~spl4_25 | ~spl4_26 | ~spl4_27)),
% 0.21/0.57    inference(backward_demodulation,[],[f140,f242])).
% 0.21/0.57  fof(f140,plain,(
% 0.21/0.57    ~v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) | spl4_13),
% 0.21/0.57    inference(avatar_component_clause,[],[f138])).
% 0.21/0.57  fof(f229,plain,(
% 0.21/0.57    spl4_27 | ~spl4_7 | ~spl4_23),
% 0.21/0.57    inference(avatar_split_clause,[],[f223,f197,f88,f226])).
% 0.21/0.57  fof(f88,plain,(
% 0.21/0.57    spl4_7 <=> l1_pre_topc(sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.57  fof(f197,plain,(
% 0.21/0.57    spl4_23 <=> ! [X1] : (m1_pre_topc(X1,sK2) | ~m1_pre_topc(X1,sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.57  fof(f223,plain,(
% 0.21/0.57    m1_pre_topc(sK1,sK2) | (~spl4_7 | ~spl4_23)),
% 0.21/0.57    inference(subsumption_resolution,[],[f222,f90])).
% 0.21/0.57  fof(f90,plain,(
% 0.21/0.57    l1_pre_topc(sK1) | ~spl4_7),
% 0.21/0.57    inference(avatar_component_clause,[],[f88])).
% 0.21/0.57  fof(f222,plain,(
% 0.21/0.57    m1_pre_topc(sK1,sK2) | ~l1_pre_topc(sK1) | ~spl4_23),
% 0.21/0.57    inference(resolution,[],[f198,f36])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,plain,(
% 0.21/0.57    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.21/0.57  fof(f198,plain,(
% 0.21/0.57    ( ! [X1] : (~m1_pre_topc(X1,sK1) | m1_pre_topc(X1,sK2)) ) | ~spl4_23),
% 0.21/0.57    inference(avatar_component_clause,[],[f197])).
% 0.21/0.57  fof(f214,plain,(
% 0.21/0.57    spl4_26 | ~spl4_9 | ~spl4_21),
% 0.21/0.57    inference(avatar_split_clause,[],[f205,f189,f98,f211])).
% 0.21/0.57  fof(f98,plain,(
% 0.21/0.57    spl4_9 <=> l1_pre_topc(sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.57  fof(f189,plain,(
% 0.21/0.57    spl4_21 <=> ! [X0] : (m1_pre_topc(X0,sK1) | ~m1_pre_topc(X0,sK2))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.57  fof(f205,plain,(
% 0.21/0.57    m1_pre_topc(sK2,sK1) | (~spl4_9 | ~spl4_21)),
% 0.21/0.57    inference(subsumption_resolution,[],[f204,f100])).
% 0.21/0.57  fof(f100,plain,(
% 0.21/0.57    l1_pre_topc(sK2) | ~spl4_9),
% 0.21/0.57    inference(avatar_component_clause,[],[f98])).
% 0.21/0.57  fof(f204,plain,(
% 0.21/0.57    m1_pre_topc(sK2,sK1) | ~l1_pre_topc(sK2) | ~spl4_21),
% 0.21/0.57    inference(resolution,[],[f190,f36])).
% 0.21/0.57  fof(f190,plain,(
% 0.21/0.57    ( ! [X0] : (~m1_pre_topc(X0,sK2) | m1_pre_topc(X0,sK1)) ) | ~spl4_21),
% 0.21/0.57    inference(avatar_component_clause,[],[f189])).
% 0.21/0.57  fof(f209,plain,(
% 0.21/0.57    spl4_25 | ~spl4_9),
% 0.21/0.57    inference(avatar_split_clause,[],[f180,f98,f207])).
% 0.21/0.57  fof(f180,plain,(
% 0.21/0.57    ( ! [X2] : (u1_struct_0(X2) = u1_struct_0(sK2) | ~m1_pre_topc(X2,sK2) | ~m1_pre_topc(sK2,X2)) ) | ~spl4_9),
% 0.21/0.57    inference(resolution,[],[f164,f100])).
% 0.21/0.57  fof(f164,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~l1_pre_topc(X1) | u1_struct_0(X0) = u1_struct_0(X1) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(X1,X0)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f162,f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.57  fof(f162,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | u1_struct_0(X0) = u1_struct_0(X1) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1)) )),
% 0.21/0.57    inference(resolution,[],[f86,f40])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.21/0.57  fof(f86,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1) | u1_struct_0(X0) = u1_struct_0(X1)) )),
% 0.21/0.57    inference(resolution,[],[f40,f48])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.57    inference(flattening,[],[f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.57    inference(nnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.57  fof(f199,plain,(
% 0.21/0.57    spl4_23 | ~spl4_7 | ~spl4_18),
% 0.21/0.57    inference(avatar_split_clause,[],[f187,f166,f88,f197])).
% 0.21/0.57  fof(f166,plain,(
% 0.21/0.57    spl4_18 <=> ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(X0,sK2))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.57  fof(f187,plain,(
% 0.21/0.57    ( ! [X1] : (m1_pre_topc(X1,sK2) | ~m1_pre_topc(X1,sK1)) ) | (~spl4_7 | ~spl4_18)),
% 0.21/0.57    inference(subsumption_resolution,[],[f185,f90])).
% 0.21/0.57  fof(f185,plain,(
% 0.21/0.57    ( ! [X1] : (m1_pre_topc(X1,sK2) | ~m1_pre_topc(X1,sK1) | ~l1_pre_topc(sK1)) ) | ~spl4_18),
% 0.21/0.57    inference(resolution,[],[f167,f108])).
% 0.21/0.57  fof(f108,plain,(
% 0.21/0.57    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f37,f39])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(nnf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.21/0.57  fof(f167,plain,(
% 0.21/0.57    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(X0,sK2)) ) | ~spl4_18),
% 0.21/0.57    inference(avatar_component_clause,[],[f166])).
% 0.21/0.57  fof(f191,plain,(
% 0.21/0.57    spl4_21 | ~spl4_15 | ~spl4_17),
% 0.21/0.57    inference(avatar_split_clause,[],[f181,f159,f147,f189])).
% 0.21/0.57  fof(f147,plain,(
% 0.21/0.57    spl4_15 <=> ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_pre_topc(X0,sK2))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.57  fof(f159,plain,(
% 0.21/0.57    spl4_17 <=> ! [X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(X1,sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.57  fof(f181,plain,(
% 0.21/0.57    ( ! [X0] : (m1_pre_topc(X0,sK1) | ~m1_pre_topc(X0,sK2)) ) | (~spl4_15 | ~spl4_17)),
% 0.21/0.57    inference(resolution,[],[f160,f148])).
% 0.21/0.57  fof(f148,plain,(
% 0.21/0.57    ( ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_pre_topc(X0,sK2)) ) | ~spl4_15),
% 0.21/0.57    inference(avatar_component_clause,[],[f147])).
% 0.21/0.57  fof(f160,plain,(
% 0.21/0.57    ( ! [X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(X1,sK1)) ) | ~spl4_17),
% 0.21/0.57    inference(avatar_component_clause,[],[f159])).
% 0.21/0.57  fof(f168,plain,(
% 0.21/0.57    spl4_18 | ~spl4_8 | ~spl4_9),
% 0.21/0.57    inference(avatar_split_clause,[],[f107,f98,f93,f166])).
% 0.21/0.57  fof(f93,plain,(
% 0.21/0.57    spl4_8 <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.57  fof(f107,plain,(
% 0.21/0.57    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(X0,sK2)) ) | (~spl4_8 | ~spl4_9)),
% 0.21/0.57    inference(forward_demodulation,[],[f105,f95])).
% 0.21/0.57  fof(f95,plain,(
% 0.21/0.57    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | ~spl4_8),
% 0.21/0.57    inference(avatar_component_clause,[],[f93])).
% 0.21/0.57  fof(f105,plain,(
% 0.21/0.57    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | m1_pre_topc(X0,sK2)) ) | ~spl4_9),
% 0.21/0.57    inference(resolution,[],[f100,f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).
% 0.21/0.57  fof(f161,plain,(
% 0.21/0.57    spl4_17 | ~spl4_7),
% 0.21/0.57    inference(avatar_split_clause,[],[f104,f88,f159])).
% 0.21/0.57  fof(f104,plain,(
% 0.21/0.57    ( ! [X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(X1,sK1)) ) | ~spl4_7),
% 0.21/0.57    inference(resolution,[],[f45,f90])).
% 0.21/0.57  fof(f154,plain,(
% 0.21/0.57    spl4_16 | ~spl4_1 | ~spl4_3 | spl4_5 | ~spl4_12),
% 0.21/0.57    inference(avatar_split_clause,[],[f133,f125,f73,f63,f53,f151])).
% 0.21/0.57  fof(f63,plain,(
% 0.21/0.57    spl4_3 <=> m1_pre_topc(sK2,sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.57  fof(f73,plain,(
% 0.21/0.57    spl4_5 <=> v1_tex_2(sK2,sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.57  fof(f125,plain,(
% 0.21/0.57    spl4_12 <=> u1_struct_0(sK2) = sK3(sK0,sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.57  fof(f133,plain,(
% 0.21/0.57    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_1 | ~spl4_3 | spl4_5 | ~spl4_12)),
% 0.21/0.57    inference(subsumption_resolution,[],[f132,f55])).
% 0.21/0.57  fof(f132,plain,(
% 0.21/0.57    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl4_3 | spl4_5 | ~spl4_12)),
% 0.21/0.57    inference(subsumption_resolution,[],[f131,f65])).
% 0.21/0.57  fof(f65,plain,(
% 0.21/0.57    m1_pre_topc(sK2,sK0) | ~spl4_3),
% 0.21/0.57    inference(avatar_component_clause,[],[f63])).
% 0.21/0.57  fof(f131,plain,(
% 0.21/0.57    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | (spl4_5 | ~spl4_12)),
% 0.21/0.57    inference(subsumption_resolution,[],[f129,f75])).
% 0.21/0.57  fof(f75,plain,(
% 0.21/0.57    ~v1_tex_2(sK2,sK0) | spl4_5),
% 0.21/0.57    inference(avatar_component_clause,[],[f73])).
% 0.21/0.57  fof(f129,plain,(
% 0.21/0.57    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tex_2(sK2,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~spl4_12),
% 0.21/0.57    inference(superposition,[],[f42,f127])).
% 0.21/0.57  fof(f127,plain,(
% 0.21/0.57    u1_struct_0(sK2) = sK3(sK0,sK2) | ~spl4_12),
% 0.21/0.57    inference(avatar_component_clause,[],[f125])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f27])).
% 0.21/0.57  fof(f149,plain,(
% 0.21/0.57    spl4_15 | ~spl4_8 | ~spl4_9),
% 0.21/0.57    inference(avatar_split_clause,[],[f114,f98,f93,f147])).
% 0.21/0.57  fof(f114,plain,(
% 0.21/0.57    ( ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_pre_topc(X0,sK2)) ) | (~spl4_8 | ~spl4_9)),
% 0.21/0.57    inference(subsumption_resolution,[],[f113,f100])).
% 0.21/0.57  fof(f113,plain,(
% 0.21/0.57    ( ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_pre_topc(X0,sK2) | ~l1_pre_topc(sK2)) ) | ~spl4_8),
% 0.21/0.57    inference(superposition,[],[f108,f95])).
% 0.21/0.57  fof(f141,plain,(
% 0.21/0.57    ~spl4_13 | ~spl4_1 | ~spl4_3 | spl4_5 | ~spl4_12),
% 0.21/0.57    inference(avatar_split_clause,[],[f136,f125,f73,f63,f53,f138])).
% 0.21/0.57  fof(f136,plain,(
% 0.21/0.57    ~v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) | (~spl4_1 | ~spl4_3 | spl4_5 | ~spl4_12)),
% 0.21/0.57    inference(subsumption_resolution,[],[f135,f55])).
% 0.21/0.57  fof(f135,plain,(
% 0.21/0.57    ~v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | (~spl4_3 | spl4_5 | ~spl4_12)),
% 0.21/0.57    inference(subsumption_resolution,[],[f134,f65])).
% 0.21/0.57  fof(f134,plain,(
% 0.21/0.57    ~v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | (spl4_5 | ~spl4_12)),
% 0.21/0.57    inference(subsumption_resolution,[],[f130,f75])).
% 0.21/0.57  fof(f130,plain,(
% 0.21/0.57    ~v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) | v1_tex_2(sK2,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~spl4_12),
% 0.21/0.57    inference(superposition,[],[f44,f127])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f27])).
% 0.21/0.57  fof(f128,plain,(
% 0.21/0.57    spl4_12 | ~spl4_1 | ~spl4_3 | spl4_5),
% 0.21/0.57    inference(avatar_split_clause,[],[f122,f73,f63,f53,f125])).
% 0.21/0.57  fof(f122,plain,(
% 0.21/0.57    u1_struct_0(sK2) = sK3(sK0,sK2) | (~spl4_1 | ~spl4_3 | spl4_5)),
% 0.21/0.57    inference(subsumption_resolution,[],[f121,f55])).
% 0.21/0.57  fof(f121,plain,(
% 0.21/0.57    u1_struct_0(sK2) = sK3(sK0,sK2) | ~l1_pre_topc(sK0) | (~spl4_3 | spl4_5)),
% 0.21/0.57    inference(subsumption_resolution,[],[f120,f65])).
% 0.21/0.57  fof(f120,plain,(
% 0.21/0.57    u1_struct_0(sK2) = sK3(sK0,sK2) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | spl4_5),
% 0.21/0.57    inference(resolution,[],[f43,f75])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK3(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f27])).
% 0.21/0.57  fof(f101,plain,(
% 0.21/0.57    spl4_9 | ~spl4_3 | ~spl4_6),
% 0.21/0.57    inference(avatar_split_clause,[],[f84,f79,f63,f98])).
% 0.21/0.57  fof(f79,plain,(
% 0.21/0.57    spl4_6 <=> ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.57  fof(f84,plain,(
% 0.21/0.57    l1_pre_topc(sK2) | (~spl4_3 | ~spl4_6)),
% 0.21/0.57    inference(resolution,[],[f80,f65])).
% 0.21/0.57  fof(f80,plain,(
% 0.21/0.57    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) ) | ~spl4_6),
% 0.21/0.57    inference(avatar_component_clause,[],[f79])).
% 0.21/0.57  fof(f96,plain,(
% 0.21/0.57    spl4_8),
% 0.21/0.57    inference(avatar_split_clause,[],[f33,f93])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.21/0.57    inference(cnf_transformation,[],[f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ((~v1_tex_2(sK2,sK0) & v1_tex_2(sK1,sK0) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_pre_topc(sK2,sK0)) & m1_pre_topc(sK1,sK0)) & l1_pre_topc(sK0)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f21,f20,f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tex_2(X2,sK0) & v1_tex_2(X1,sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(X1,sK0)) & l1_pre_topc(sK0))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ? [X1] : (? [X2] : (~v1_tex_2(X2,sK0) & v1_tex_2(X1,sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(X1,sK0)) => (? [X2] : (~v1_tex_2(X2,sK0) & v1_tex_2(sK1,sK0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(sK1,sK0))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ? [X2] : (~v1_tex_2(X2,sK0) & v1_tex_2(sK1,sK0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_pre_topc(X2,sK0)) => (~v1_tex_2(sK2,sK0) & v1_tex_2(sK1,sK0) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_pre_topc(sK2,sK0))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f11,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.21/0.57    inference(flattening,[],[f10])).
% 0.21/0.57  fof(f10,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : (? [X2] : ((~v1_tex_2(X2,X0) & (v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,negated_conjecture,(
% 0.21/0.57    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 0.21/0.57    inference(negated_conjecture,[],[f8])).
% 0.21/0.57  fof(f8,conjecture,(
% 0.21/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tex_2)).
% 0.21/0.57  fof(f91,plain,(
% 0.21/0.57    spl4_7 | ~spl4_2 | ~spl4_6),
% 0.21/0.57    inference(avatar_split_clause,[],[f83,f79,f58,f88])).
% 0.21/0.57  fof(f83,plain,(
% 0.21/0.57    l1_pre_topc(sK1) | (~spl4_2 | ~spl4_6)),
% 0.21/0.57    inference(resolution,[],[f80,f60])).
% 0.21/0.57  fof(f81,plain,(
% 0.21/0.57    spl4_6 | ~spl4_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f77,f53,f79])).
% 0.21/0.57  fof(f77,plain,(
% 0.21/0.57    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) ) | ~spl4_1),
% 0.21/0.57    inference(resolution,[],[f39,f55])).
% 0.21/0.57  fof(f76,plain,(
% 0.21/0.57    ~spl4_5),
% 0.21/0.57    inference(avatar_split_clause,[],[f35,f73])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ~v1_tex_2(sK2,sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f22])).
% 0.21/0.57  fof(f71,plain,(
% 0.21/0.57    spl4_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f34,f68])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    v1_tex_2(sK1,sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f22])).
% 0.21/0.57  fof(f66,plain,(
% 0.21/0.57    spl4_3),
% 0.21/0.57    inference(avatar_split_clause,[],[f32,f63])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    m1_pre_topc(sK2,sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f22])).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    spl4_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f31,f58])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    m1_pre_topc(sK1,sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f22])).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    spl4_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f30,f53])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    l1_pre_topc(sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f22])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (7209)------------------------------
% 0.21/0.57  % (7209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (7209)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (7209)Memory used [KB]: 6268
% 0.21/0.57  % (7209)Time elapsed: 0.124 s
% 0.21/0.57  % (7209)------------------------------
% 0.21/0.57  % (7209)------------------------------
% 0.21/0.57  % (7206)Success in time 0.207 s
%------------------------------------------------------------------------------
