%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:57 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 145 expanded)
%              Number of leaves         :   20 (  67 expanded)
%              Depth                    :    7
%              Number of atoms          :  248 ( 530 expanded)
%              Number of equality atoms :   15 (  40 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f491,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f48,f53,f64,f78,f101,f131,f145,f188,f206,f298,f318,f332,f455])).

fof(f455,plain,
    ( ~ spl6_46
    | ~ spl6_41
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f428,f315,f295,f329])).

fof(f329,plain,
    ( spl6_46
  <=> k1_tarski(sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f295,plain,
    ( spl6_41
  <=> v3_pre_topc(sK4(sK0,sK1,k1_tarski(sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f315,plain,
    ( spl6_44
  <=> m1_subset_1(sK4(sK0,sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f428,plain,
    ( ~ v3_pre_topc(sK4(sK0,sK1,k1_tarski(sK2)),sK0)
    | k1_tarski(sK2) != k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k1_tarski(sK2)))
    | ~ spl6_44 ),
    inference(resolution,[],[f317,f14])).

fof(f14,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                              & v3_pre_topc(X3,X0) ) )
                      & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                            & v3_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tex_2)).

fof(f317,plain,
    ( m1_subset_1(sK4(sK0,sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f315])).

fof(f332,plain,
    ( ~ spl6_6
    | spl6_46
    | ~ spl6_14
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f325,f204,f128,f329,f61])).

fof(f61,plain,
    ( spl6_6
  <=> r1_tarski(k1_tarski(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f128,plain,
    ( spl6_14
  <=> m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f204,plain,
    ( spl6_27
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,X3)) = X3
        | ~ r1_tarski(X3,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f325,plain,
    ( k1_tarski(sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k1_tarski(sK2)))
    | ~ r1_tarski(k1_tarski(sK2),sK1)
    | ~ spl6_14
    | ~ spl6_27 ),
    inference(resolution,[],[f205,f130])).

fof(f130,plain,
    ( m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f128])).

fof(f205,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,X3)) = X3
        | ~ r1_tarski(X3,sK1) )
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f204])).

fof(f318,plain,
    ( ~ spl6_6
    | spl6_44
    | ~ spl6_14
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f311,f186,f128,f315,f61])).

fof(f186,plain,
    ( spl6_24
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK4(sK0,sK1,X3),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f311,plain,
    ( m1_subset_1(sK4(sK0,sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tarski(sK2),sK1)
    | ~ spl6_14
    | ~ spl6_24 ),
    inference(resolution,[],[f187,f130])).

fof(f187,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK4(sK0,sK1,X3),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f186])).

fof(f298,plain,
    ( ~ spl6_6
    | spl6_41
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f282,f143,f128,f295,f61])).

fof(f143,plain,
    ( spl6_16
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(sK4(sK0,sK1,X2),sK0)
        | ~ r1_tarski(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f282,plain,
    ( v3_pre_topc(sK4(sK0,sK1,k1_tarski(sK2)),sK0)
    | ~ r1_tarski(k1_tarski(sK2),sK1)
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(resolution,[],[f144,f130])).

fof(f144,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(sK4(sK0,sK1,X2),sK0)
        | ~ r1_tarski(X2,sK1) )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f143])).

fof(f206,plain,
    ( ~ spl6_2
    | spl6_27
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f198,f45,f35,f204,f40])).

fof(f40,plain,
    ( spl6_2
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f35,plain,
    ( spl6_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f45,plain,
    ( spl6_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f198,plain,
    ( ! [X3] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,X3)) = X3
        | ~ v2_tex_2(sK1,sK0) )
    | ~ spl6_3 ),
    inference(resolution,[],[f23,f47])).

fof(f47,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X2)) = X2
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

fof(f188,plain,
    ( ~ spl6_2
    | spl6_24
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f180,f45,f35,f186,f40])).

fof(f180,plain,
    ( ! [X3] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | m1_subset_1(sK4(sK0,sK1,X3),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(sK1,sK0) )
    | ~ spl6_3 ),
    inference(resolution,[],[f21,f47])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f145,plain,
    ( ~ spl6_2
    | spl6_16
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f141,f45,f35,f143,f40])).

fof(f141,plain,
    ( ! [X2] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X2,sK1)
        | v3_pre_topc(sK4(sK0,sK1,X2),sK0)
        | ~ v2_tex_2(sK1,sK0) )
    | ~ spl6_3 ),
    inference(resolution,[],[f22,f47])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | v3_pre_topc(sK4(X0,X1,X2),X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f131,plain,
    ( spl6_14
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f125,f98,f128])).

fof(f98,plain,
    ( spl6_9
  <=> r2_hidden(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f125,plain,
    ( m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_9 ),
    inference(resolution,[],[f100,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f100,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f98])).

fof(f101,plain,
    ( spl6_9
    | ~ spl6_4
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f95,f75,f50,f98])).

fof(f50,plain,
    ( spl6_4
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f75,plain,
    ( spl6_8
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f95,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl6_4
    | ~ spl6_8 ),
    inference(resolution,[],[f87,f77])).

fof(f77,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f75])).

fof(f87,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r2_hidden(sK2,X0) )
    | ~ spl6_4 ),
    inference(resolution,[],[f27,f52])).

fof(f52,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f78,plain,
    ( spl6_8
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f72,f45,f75])).

fof(f72,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl6_3 ),
    inference(resolution,[],[f33,f47])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f64,plain,
    ( spl6_6
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f59,f50,f61])).

fof(f59,plain,
    ( r1_tarski(k1_tarski(sK2),sK1)
    | ~ spl6_4 ),
    inference(resolution,[],[f30,f52])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f53,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f16,f50])).

fof(f16,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f48,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f17,f45])).

fof(f17,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f43,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f18,f40])).

fof(f18,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f38,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f19,f35])).

fof(f19,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:57:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (13479)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.47  % (13487)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.49  % (13487)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f491,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f38,f43,f48,f53,f64,f78,f101,f131,f145,f188,f206,f298,f318,f332,f455])).
% 0.22/0.49  fof(f455,plain,(
% 0.22/0.49    ~spl6_46 | ~spl6_41 | ~spl6_44),
% 0.22/0.49    inference(avatar_split_clause,[],[f428,f315,f295,f329])).
% 0.22/0.49  fof(f329,plain,(
% 0.22/0.49    spl6_46 <=> k1_tarski(sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k1_tarski(sK2)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 0.22/0.49  fof(f295,plain,(
% 0.22/0.49    spl6_41 <=> v3_pre_topc(sK4(sK0,sK1,k1_tarski(sK2)),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 0.22/0.49  fof(f315,plain,(
% 0.22/0.49    spl6_44 <=> m1_subset_1(sK4(sK0,sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 0.22/0.49  fof(f428,plain,(
% 0.22/0.49    ~v3_pre_topc(sK4(sK0,sK1,k1_tarski(sK2)),sK0) | k1_tarski(sK2) != k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k1_tarski(sK2))) | ~spl6_44),
% 0.22/0.49    inference(resolution,[],[f317,f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f8])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,negated_conjecture,(
% 0.22/0.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 0.22/0.49    inference(negated_conjecture,[],[f6])).
% 0.22/0.49  fof(f6,conjecture,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tex_2)).
% 0.22/0.49  fof(f317,plain,(
% 0.22/0.49    m1_subset_1(sK4(sK0,sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_44),
% 0.22/0.49    inference(avatar_component_clause,[],[f315])).
% 0.22/0.49  fof(f332,plain,(
% 0.22/0.49    ~spl6_6 | spl6_46 | ~spl6_14 | ~spl6_27),
% 0.22/0.49    inference(avatar_split_clause,[],[f325,f204,f128,f329,f61])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    spl6_6 <=> r1_tarski(k1_tarski(sK2),sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    spl6_14 <=> m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.22/0.49  fof(f204,plain,(
% 0.22/0.49    spl6_27 <=> ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,X3)) = X3 | ~r1_tarski(X3,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.22/0.49  fof(f325,plain,(
% 0.22/0.49    k1_tarski(sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k1_tarski(sK2))) | ~r1_tarski(k1_tarski(sK2),sK1) | (~spl6_14 | ~spl6_27)),
% 0.22/0.49    inference(resolution,[],[f205,f130])).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_14),
% 0.22/0.49    inference(avatar_component_clause,[],[f128])).
% 0.22/0.49  fof(f205,plain,(
% 0.22/0.49    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,X3)) = X3 | ~r1_tarski(X3,sK1)) ) | ~spl6_27),
% 0.22/0.49    inference(avatar_component_clause,[],[f204])).
% 0.22/0.49  fof(f318,plain,(
% 0.22/0.49    ~spl6_6 | spl6_44 | ~spl6_14 | ~spl6_24),
% 0.22/0.49    inference(avatar_split_clause,[],[f311,f186,f128,f315,f61])).
% 0.22/0.49  fof(f186,plain,(
% 0.22/0.49    spl6_24 <=> ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK4(sK0,sK1,X3),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.22/0.49  fof(f311,plain,(
% 0.22/0.49    m1_subset_1(sK4(sK0,sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_tarski(sK2),sK1) | (~spl6_14 | ~spl6_24)),
% 0.22/0.49    inference(resolution,[],[f187,f130])).
% 0.22/0.49  fof(f187,plain,(
% 0.22/0.49    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK4(sK0,sK1,X3),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1)) ) | ~spl6_24),
% 0.22/0.49    inference(avatar_component_clause,[],[f186])).
% 0.22/0.49  fof(f298,plain,(
% 0.22/0.49    ~spl6_6 | spl6_41 | ~spl6_14 | ~spl6_16),
% 0.22/0.49    inference(avatar_split_clause,[],[f282,f143,f128,f295,f61])).
% 0.22/0.49  fof(f143,plain,(
% 0.22/0.49    spl6_16 <=> ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK4(sK0,sK1,X2),sK0) | ~r1_tarski(X2,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.22/0.49  fof(f282,plain,(
% 0.22/0.49    v3_pre_topc(sK4(sK0,sK1,k1_tarski(sK2)),sK0) | ~r1_tarski(k1_tarski(sK2),sK1) | (~spl6_14 | ~spl6_16)),
% 0.22/0.49    inference(resolution,[],[f144,f130])).
% 0.22/0.50  fof(f144,plain,(
% 0.22/0.50    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK4(sK0,sK1,X2),sK0) | ~r1_tarski(X2,sK1)) ) | ~spl6_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f143])).
% 0.22/0.51  fof(f206,plain,(
% 0.22/0.51    ~spl6_2 | spl6_27 | ~spl6_1 | ~spl6_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f198,f45,f35,f204,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    spl6_2 <=> v2_tex_2(sK1,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    spl6_1 <=> l1_pre_topc(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    spl6_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.51  fof(f198,plain,(
% 0.22/0.51    ( ! [X3] : (~l1_pre_topc(sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,X3)) = X3 | ~v2_tex_2(sK1,sK0)) ) | ~spl6_3),
% 0.22/0.51    inference(resolution,[],[f23,f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f45])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X2)) = X2 | ~v2_tex_2(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).
% 0.22/0.51  fof(f188,plain,(
% 0.22/0.51    ~spl6_2 | spl6_24 | ~spl6_1 | ~spl6_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f180,f45,f35,f186,f40])).
% 0.22/0.51  fof(f180,plain,(
% 0.22/0.51    ( ! [X3] : (~l1_pre_topc(sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | m1_subset_1(sK4(sK0,sK1,X3),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0)) ) | ~spl6_3),
% 0.22/0.51    inference(resolution,[],[f21,f47])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f145,plain,(
% 0.22/0.51    ~spl6_2 | spl6_16 | ~spl6_1 | ~spl6_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f141,f45,f35,f143,f40])).
% 0.22/0.51  fof(f141,plain,(
% 0.22/0.51    ( ! [X2] : (~l1_pre_topc(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X2,sK1) | v3_pre_topc(sK4(sK0,sK1,X2),sK0) | ~v2_tex_2(sK1,sK0)) ) | ~spl6_3),
% 0.22/0.51    inference(resolution,[],[f22,f47])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | v3_pre_topc(sK4(X0,X1,X2),X0) | ~v2_tex_2(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f131,plain,(
% 0.22/0.51    spl6_14 | ~spl6_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f125,f98,f128])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    spl6_9 <=> r2_hidden(sK2,u1_struct_0(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_9),
% 0.22/0.51    inference(resolution,[],[f100,f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    r2_hidden(sK2,u1_struct_0(sK0)) | ~spl6_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f98])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    spl6_9 | ~spl6_4 | ~spl6_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f95,f75,f50,f98])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    spl6_4 <=> r2_hidden(sK2,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    spl6_8 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    r2_hidden(sK2,u1_struct_0(sK0)) | (~spl6_4 | ~spl6_8)),
% 0.22/0.51    inference(resolution,[],[f87,f77])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl6_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f75])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_tarski(sK1,X0) | r2_hidden(sK2,X0)) ) | ~spl6_4),
% 0.22/0.51    inference(resolution,[],[f27,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    r2_hidden(sK2,sK1) | ~spl6_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f50])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    spl6_8 | ~spl6_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f72,f45,f75])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl6_3),
% 0.22/0.51    inference(resolution,[],[f33,f47])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    spl6_6 | ~spl6_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f59,f50,f61])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    r1_tarski(k1_tarski(sK2),sK1) | ~spl6_4),
% 0.22/0.51    inference(resolution,[],[f30,f52])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    spl6_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f16,f50])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    r2_hidden(sK2,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    spl6_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f17,f45])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    spl6_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f18,f40])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    v2_tex_2(sK1,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    spl6_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f19,f35])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    l1_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (13487)------------------------------
% 0.22/0.51  % (13487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (13487)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (13487)Memory used [KB]: 11001
% 0.22/0.51  % (13487)Time elapsed: 0.085 s
% 0.22/0.51  % (13487)------------------------------
% 0.22/0.51  % (13487)------------------------------
% 0.22/0.51  % (13470)Success in time 0.144 s
%------------------------------------------------------------------------------
