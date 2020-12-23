%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 172 expanded)
%              Number of leaves         :   22 (  77 expanded)
%              Depth                    :    8
%              Number of atoms          :  262 ( 570 expanded)
%              Number of equality atoms :   21 (  56 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f474,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f52,f57,f68,f82,f89,f96,f107,f134,f182,f201,f278,f302,f315,f438])).

fof(f438,plain,
    ( ~ spl6_46
    | ~ spl6_40
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f411,f299,f275,f312])).

fof(f312,plain,
    ( spl6_46
  <=> k2_enumset1(sK2,sK2,sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f275,plain,
    ( spl6_40
  <=> v3_pre_topc(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f299,plain,
    ( spl6_44
  <=> m1_subset_1(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f411,plain,
    ( ~ v3_pre_topc(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK0)
    | k2_enumset1(sK2,sK2,sK2,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)))
    | ~ spl6_44 ),
    inference(resolution,[],[f301,f36])).

fof(f36,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | k9_subset_1(u1_struct_0(sK0),sK1,X3) != k2_enumset1(sK2,sK2,sK2,sK2) ) ),
    inference(definition_unfolding,[],[f15,f35])).

fof(f35,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f21,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f21,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f15,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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

fof(f301,plain,
    ( m1_subset_1(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f299])).

fof(f315,plain,
    ( ~ spl6_10
    | spl6_46
    | ~ spl6_9
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f309,f199,f93,f312,f104])).

fof(f104,plain,
    ( spl6_10
  <=> r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f93,plain,
    ( spl6_9
  <=> m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f199,plain,
    ( spl6_27
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,X3)) = X3
        | ~ r1_tarski(X3,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f309,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)))
    | ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1)
    | ~ spl6_9
    | ~ spl6_27 ),
    inference(resolution,[],[f200,f95])).

fof(f95,plain,
    ( m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f93])).

fof(f200,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,X3)) = X3
        | ~ r1_tarski(X3,sK1) )
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f199])).

fof(f302,plain,
    ( ~ spl6_10
    | spl6_44
    | ~ spl6_9
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f291,f180,f93,f299,f104])).

fof(f180,plain,
    ( spl6_24
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK4(sK0,sK1,X3),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f291,plain,
    ( m1_subset_1(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1)
    | ~ spl6_9
    | ~ spl6_24 ),
    inference(resolution,[],[f181,f95])).

fof(f181,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK4(sK0,sK1,X3),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f180])).

fof(f278,plain,
    ( ~ spl6_10
    | spl6_40
    | ~ spl6_9
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f263,f132,f93,f275,f104])).

fof(f132,plain,
    ( spl6_15
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(sK4(sK0,sK1,X2),sK0)
        | ~ r1_tarski(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f263,plain,
    ( v3_pre_topc(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK0)
    | ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1)
    | ~ spl6_9
    | ~ spl6_15 ),
    inference(resolution,[],[f133,f95])).

fof(f133,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(sK4(sK0,sK1,X2),sK0)
        | ~ r1_tarski(X2,sK1) )
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f132])).

fof(f201,plain,
    ( ~ spl6_2
    | spl6_27
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f193,f49,f39,f199,f44])).

fof(f44,plain,
    ( spl6_2
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f39,plain,
    ( spl6_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f49,plain,
    ( spl6_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f193,plain,
    ( ! [X3] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,X3)) = X3
        | ~ v2_tex_2(sK1,sK0) )
    | ~ spl6_3 ),
    inference(resolution,[],[f25,f51])).

fof(f51,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X2)) = X2
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f182,plain,
    ( ~ spl6_2
    | spl6_24
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f174,f49,f39,f180,f44])).

fof(f174,plain,
    ( ! [X3] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | m1_subset_1(sK4(sK0,sK1,X3),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(sK1,sK0) )
    | ~ spl6_3 ),
    inference(resolution,[],[f23,f51])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f134,plain,
    ( ~ spl6_2
    | spl6_15
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f130,f49,f39,f132,f44])).

fof(f130,plain,
    ( ! [X2] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X2,sK1)
        | v3_pre_topc(sK4(sK0,sK1,X2),sK0)
        | ~ v2_tex_2(sK1,sK0) )
    | ~ spl6_3 ),
    inference(resolution,[],[f24,f51])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | v3_pre_topc(sK4(X0,X1,X2),X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f107,plain,
    ( spl6_10
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f102,f79,f104])).

fof(f79,plain,
    ( spl6_7
  <=> m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f102,plain,
    ( r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1)
    | ~ spl6_7 ),
    inference(resolution,[],[f81,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f81,plain,
    ( m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(sK1))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f79])).

fof(f96,plain,
    ( spl6_9
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f90,f86,f93])).

fof(f86,plain,
    ( spl6_8
  <=> r2_hidden(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f90,plain,
    ( m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_8 ),
    inference(resolution,[],[f88,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X1)) ) ),
    inference(definition_unfolding,[],[f29,f35])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f88,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f86])).

fof(f89,plain,
    ( spl6_8
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f83,f65,f54,f86])).

fof(f54,plain,
    ( spl6_4
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f65,plain,
    ( spl6_6
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f83,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(resolution,[],[f73,f67])).

fof(f67,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f73,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r2_hidden(sK2,X0) )
    | ~ spl6_4 ),
    inference(resolution,[],[f30,f56])).

fof(f56,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f82,plain,
    ( spl6_7
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f76,f54,f79])).

fof(f76,plain,
    ( m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(sK1))
    | ~ spl6_4 ),
    inference(resolution,[],[f37,f56])).

fof(f68,plain,
    ( spl6_6
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f63,f49,f65])).

fof(f63,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl6_3 ),
    inference(resolution,[],[f34,f51])).

fof(f57,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f17,f54])).

fof(f17,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f52,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f18,f49])).

fof(f18,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f47,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f19,f44])).

fof(f19,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f20,f39])).

fof(f20,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:55:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.52  % (1462)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (1474)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (1480)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (1474)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.55  % (1480)Refutation not found, incomplete strategy% (1480)------------------------------
% 0.21/0.55  % (1480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (1480)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (1480)Memory used [KB]: 10746
% 0.21/0.55  % (1480)Time elapsed: 0.129 s
% 0.21/0.55  % (1480)------------------------------
% 0.21/0.55  % (1480)------------------------------
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f474,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f42,f47,f52,f57,f68,f82,f89,f96,f107,f134,f182,f201,f278,f302,f315,f438])).
% 0.21/0.55  fof(f438,plain,(
% 0.21/0.55    ~spl6_46 | ~spl6_40 | ~spl6_44),
% 0.21/0.55    inference(avatar_split_clause,[],[f411,f299,f275,f312])).
% 0.21/0.55  fof(f312,plain,(
% 0.21/0.55    spl6_46 <=> k2_enumset1(sK2,sK2,sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 0.21/0.55  fof(f275,plain,(
% 0.21/0.55    spl6_40 <=> v3_pre_topc(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 0.21/0.55  fof(f299,plain,(
% 0.21/0.55    spl6_44 <=> m1_subset_1(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 0.21/0.55  fof(f411,plain,(
% 0.21/0.55    ~v3_pre_topc(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK0) | k2_enumset1(sK2,sK2,sK2,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2))) | ~spl6_44),
% 0.21/0.55    inference(resolution,[],[f301,f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | k9_subset_1(u1_struct_0(sK0),sK1,X3) != k2_enumset1(sK2,sK2,sK2,sK2)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f15,f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f21,f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f9])).
% 0.21/0.55  fof(f9,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,negated_conjecture,(
% 0.21/0.55    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 0.21/0.55    inference(negated_conjecture,[],[f7])).
% 0.21/0.55  fof(f7,conjecture,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tex_2)).
% 0.21/0.55  fof(f301,plain,(
% 0.21/0.55    m1_subset_1(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_44),
% 0.21/0.55    inference(avatar_component_clause,[],[f299])).
% 0.21/0.55  fof(f315,plain,(
% 0.21/0.55    ~spl6_10 | spl6_46 | ~spl6_9 | ~spl6_27),
% 0.21/0.55    inference(avatar_split_clause,[],[f309,f199,f93,f312,f104])).
% 0.21/0.55  fof(f104,plain,(
% 0.21/0.55    spl6_10 <=> r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.55  fof(f93,plain,(
% 0.21/0.55    spl6_9 <=> m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.55  fof(f199,plain,(
% 0.21/0.55    spl6_27 <=> ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,X3)) = X3 | ~r1_tarski(X3,sK1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.21/0.55  fof(f309,plain,(
% 0.21/0.55    k2_enumset1(sK2,sK2,sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2))) | ~r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1) | (~spl6_9 | ~spl6_27)),
% 0.21/0.55    inference(resolution,[],[f200,f95])).
% 0.21/0.55  fof(f95,plain,(
% 0.21/0.55    m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_9),
% 0.21/0.55    inference(avatar_component_clause,[],[f93])).
% 0.21/0.55  fof(f200,plain,(
% 0.21/0.55    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,X3)) = X3 | ~r1_tarski(X3,sK1)) ) | ~spl6_27),
% 0.21/0.55    inference(avatar_component_clause,[],[f199])).
% 0.21/0.55  fof(f302,plain,(
% 0.21/0.55    ~spl6_10 | spl6_44 | ~spl6_9 | ~spl6_24),
% 0.21/0.55    inference(avatar_split_clause,[],[f291,f180,f93,f299,f104])).
% 0.21/0.55  fof(f180,plain,(
% 0.21/0.55    spl6_24 <=> ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK4(sK0,sK1,X3),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.21/0.55  fof(f291,plain,(
% 0.21/0.55    m1_subset_1(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1) | (~spl6_9 | ~spl6_24)),
% 0.21/0.55    inference(resolution,[],[f181,f95])).
% 0.21/0.55  fof(f181,plain,(
% 0.21/0.55    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK4(sK0,sK1,X3),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1)) ) | ~spl6_24),
% 0.21/0.55    inference(avatar_component_clause,[],[f180])).
% 0.21/0.55  fof(f278,plain,(
% 0.21/0.55    ~spl6_10 | spl6_40 | ~spl6_9 | ~spl6_15),
% 0.21/0.55    inference(avatar_split_clause,[],[f263,f132,f93,f275,f104])).
% 0.21/0.55  fof(f132,plain,(
% 0.21/0.55    spl6_15 <=> ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK4(sK0,sK1,X2),sK0) | ~r1_tarski(X2,sK1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.55  fof(f263,plain,(
% 0.21/0.55    v3_pre_topc(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK0) | ~r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1) | (~spl6_9 | ~spl6_15)),
% 0.21/0.55    inference(resolution,[],[f133,f95])).
% 0.21/0.55  fof(f133,plain,(
% 0.21/0.55    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK4(sK0,sK1,X2),sK0) | ~r1_tarski(X2,sK1)) ) | ~spl6_15),
% 0.21/0.55    inference(avatar_component_clause,[],[f132])).
% 0.21/0.55  fof(f201,plain,(
% 0.21/0.55    ~spl6_2 | spl6_27 | ~spl6_1 | ~spl6_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f193,f49,f39,f199,f44])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    spl6_2 <=> v2_tex_2(sK1,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    spl6_1 <=> l1_pre_topc(sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    spl6_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.55  fof(f193,plain,(
% 0.21/0.55    ( ! [X3] : (~l1_pre_topc(sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,X3)) = X3 | ~v2_tex_2(sK1,sK0)) ) | ~spl6_3),
% 0.21/0.55    inference(resolution,[],[f25,f51])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f49])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X2)) = X2 | ~v2_tex_2(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f11])).
% 0.21/0.55  fof(f11,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).
% 0.21/0.55  fof(f182,plain,(
% 0.21/0.55    ~spl6_2 | spl6_24 | ~spl6_1 | ~spl6_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f174,f49,f39,f180,f44])).
% 0.21/0.55  fof(f174,plain,(
% 0.21/0.55    ( ! [X3] : (~l1_pre_topc(sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | m1_subset_1(sK4(sK0,sK1,X3),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0)) ) | ~spl6_3),
% 0.21/0.55    inference(resolution,[],[f23,f51])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f12])).
% 0.21/0.55  fof(f134,plain,(
% 0.21/0.55    ~spl6_2 | spl6_15 | ~spl6_1 | ~spl6_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f130,f49,f39,f132,f44])).
% 0.21/0.55  fof(f130,plain,(
% 0.21/0.55    ( ! [X2] : (~l1_pre_topc(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X2,sK1) | v3_pre_topc(sK4(sK0,sK1,X2),sK0) | ~v2_tex_2(sK1,sK0)) ) | ~spl6_3),
% 0.21/0.55    inference(resolution,[],[f24,f51])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | v3_pre_topc(sK4(X0,X1,X2),X0) | ~v2_tex_2(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f12])).
% 0.21/0.55  fof(f107,plain,(
% 0.21/0.55    spl6_10 | ~spl6_7),
% 0.21/0.55    inference(avatar_split_clause,[],[f102,f79,f104])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    spl6_7 <=> m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(sK1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.55  fof(f102,plain,(
% 0.21/0.55    r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1) | ~spl6_7),
% 0.21/0.55    inference(resolution,[],[f81,f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.55  fof(f81,plain,(
% 0.21/0.55    m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(sK1)) | ~spl6_7),
% 0.21/0.55    inference(avatar_component_clause,[],[f79])).
% 0.21/0.55  fof(f96,plain,(
% 0.21/0.55    spl6_9 | ~spl6_8),
% 0.21/0.55    inference(avatar_split_clause,[],[f90,f86,f93])).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    spl6_8 <=> r2_hidden(sK2,u1_struct_0(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_8),
% 0.21/0.55    inference(resolution,[],[f88,f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X1))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f29,f35])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    r2_hidden(sK2,u1_struct_0(sK0)) | ~spl6_8),
% 0.21/0.55    inference(avatar_component_clause,[],[f86])).
% 0.21/0.55  fof(f89,plain,(
% 0.21/0.55    spl6_8 | ~spl6_4 | ~spl6_6),
% 0.21/0.55    inference(avatar_split_clause,[],[f83,f65,f54,f86])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    spl6_4 <=> r2_hidden(sK2,sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    spl6_6 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.56  fof(f83,plain,(
% 0.21/0.56    r2_hidden(sK2,u1_struct_0(sK0)) | (~spl6_4 | ~spl6_6)),
% 0.21/0.56    inference(resolution,[],[f73,f67])).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl6_6),
% 0.21/0.56    inference(avatar_component_clause,[],[f65])).
% 0.21/0.56  fof(f73,plain,(
% 0.21/0.56    ( ! [X0] : (~r1_tarski(sK1,X0) | r2_hidden(sK2,X0)) ) | ~spl6_4),
% 0.21/0.56    inference(resolution,[],[f30,f56])).
% 0.21/0.56  fof(f56,plain,(
% 0.21/0.56    r2_hidden(sK2,sK1) | ~spl6_4),
% 0.21/0.56    inference(avatar_component_clause,[],[f54])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,plain,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.56  fof(f82,plain,(
% 0.21/0.56    spl6_7 | ~spl6_4),
% 0.21/0.56    inference(avatar_split_clause,[],[f76,f54,f79])).
% 0.21/0.56  fof(f76,plain,(
% 0.21/0.56    m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(sK1)) | ~spl6_4),
% 0.21/0.56    inference(resolution,[],[f37,f56])).
% 0.21/0.56  fof(f68,plain,(
% 0.21/0.56    spl6_6 | ~spl6_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f63,f49,f65])).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl6_3),
% 0.21/0.56    inference(resolution,[],[f34,f51])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    spl6_4),
% 0.21/0.56    inference(avatar_split_clause,[],[f17,f54])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    r2_hidden(sK2,sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f10])).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    spl6_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f18,f49])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.56    inference(cnf_transformation,[],[f10])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    spl6_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f19,f44])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    v2_tex_2(sK1,sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f10])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    spl6_1),
% 0.21/0.56    inference(avatar_split_clause,[],[f20,f39])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    l1_pre_topc(sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f10])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (1474)------------------------------
% 0.21/0.56  % (1474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (1474)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (1474)Memory used [KB]: 11001
% 0.21/0.56  % (1474)Time elapsed: 0.129 s
% 0.21/0.56  % (1474)------------------------------
% 0.21/0.56  % (1474)------------------------------
% 0.21/0.56  % (1449)Success in time 0.197 s
%------------------------------------------------------------------------------
