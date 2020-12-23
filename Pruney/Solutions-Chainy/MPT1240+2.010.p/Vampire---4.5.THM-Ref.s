%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 193 expanded)
%              Number of leaves         :   32 (  88 expanded)
%              Depth                    :    6
%              Number of atoms          :  346 ( 690 expanded)
%              Number of equality atoms :   23 (  25 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (20319)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f884,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f63,f68,f77,f82,f87,f92,f96,f137,f184,f209,f222,f301,f566,f609,f682,f732,f733,f858,f874,f878])).

fof(f878,plain,
    ( spl5_4
    | ~ spl5_5
    | ~ spl5_124 ),
    inference(avatar_split_clause,[],[f875,f837,f74,f70])).

fof(f70,plain,
    ( spl5_4
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f74,plain,
    ( spl5_5
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f837,plain,
    ( spl5_124
  <=> r1_tarski(sK3,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_124])])).

fof(f875,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl5_5
    | ~ spl5_124 ),
    inference(resolution,[],[f838,f121])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK3,X0)
        | r2_hidden(sK1,X0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f49,f76])).

fof(f76,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f74])).

% (20305)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (20317)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (20295)Refutation not found, incomplete strategy% (20295)------------------------------
% (20295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20295)Termination reason: Refutation not found, incomplete strategy

% (20295)Memory used [KB]: 11001
% (20295)Time elapsed: 0.157 s
% (20295)------------------------------
% (20295)------------------------------
fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f838,plain,
    ( r1_tarski(sK3,k1_tops_1(sK0,sK2))
    | ~ spl5_124 ),
    inference(avatar_component_clause,[],[f837])).

fof(f874,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK3) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))
    | sK3 != k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3))
    | k1_tops_1(sK0,sK3) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)))
    | r1_tarski(sK3,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f858,plain,
    ( ~ spl5_6
    | spl5_128
    | ~ spl5_3
    | ~ spl5_43 ),
    inference(avatar_split_clause,[],[f814,f323,f65,f855,f79])).

fof(f79,plain,
    ( spl5_6
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f855,plain,
    ( spl5_128
  <=> r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_128])])).

fof(f65,plain,
    ( spl5_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f323,plain,
    ( spl5_43
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X1))
        | ~ r1_tarski(sK3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f814,plain,
    ( r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))
    | ~ r1_tarski(sK3,sK2)
    | ~ spl5_3
    | ~ spl5_43 ),
    inference(resolution,[],[f324,f67])).

fof(f67,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f324,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X1))
        | ~ r1_tarski(sK3,X1) )
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f323])).

fof(f733,plain,
    ( spl5_19
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f729,f89,f167])).

fof(f167,plain,
    ( spl5_19
  <=> sK3 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f89,plain,
    ( spl5_8
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f729,plain,
    ( sK3 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3))
    | ~ spl5_8 ),
    inference(resolution,[],[f91,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f91,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f89])).

fof(f732,plain,
    ( spl5_43
    | ~ spl5_1
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f726,f89,f55,f323])).

fof(f55,plain,
    ( spl5_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f726,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK3,X0)
        | r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X0)) )
    | ~ spl5_8 ),
    inference(resolution,[],[f91,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f682,plain,
    ( ~ spl5_25
    | ~ spl5_21
    | ~ spl5_4
    | ~ spl5_9
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f651,f219,f94,f70,f181,f206])).

fof(f206,plain,
    ( spl5_25
  <=> v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f181,plain,
    ( spl5_21
  <=> r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f94,plain,
    ( spl5_9
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK1,X3)
        | ~ r1_tarski(X3,sK2)
        | ~ v3_pre_topc(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f219,plain,
    ( spl5_27
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f651,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ spl5_9
    | ~ spl5_27 ),
    inference(resolution,[],[f95,f221])).

fof(f221,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f219])).

fof(f95,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK1,X3)
        | ~ r1_tarski(X3,sK2)
        | ~ v3_pre_topc(X3,sK0) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f94])).

fof(f609,plain,
    ( spl5_79
    | ~ spl5_1
    | ~ spl5_14
    | ~ spl5_7
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f608,f167,f84,f134,f55,f558])).

fof(f558,plain,
    ( spl5_79
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).

fof(f134,plain,
    ( spl5_14
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f84,plain,
    ( spl5_7
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f608,plain,
    ( ~ v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0)
    | ~ spl5_19 ),
    inference(superposition,[],[f42,f169])).

fof(f169,plain,
    ( sK3 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f167])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(f566,plain,
    ( spl5_80
    | ~ spl5_79
    | ~ spl5_1
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f539,f134,f55,f558,f562])).

fof(f562,plain,
    ( spl5_80
  <=> k3_subset_1(u1_struct_0(sK0),sK3) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).

fof(f539,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0)
    | k3_subset_1(u1_struct_0(sK0),sK3) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))
    | ~ spl5_14 ),
    inference(resolution,[],[f136,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f136,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f134])).

fof(f301,plain,
    ( spl5_39
    | ~ spl5_1
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f290,f89,f55,f298])).

fof(f298,plain,
    ( spl5_39
  <=> k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f290,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)))
    | ~ spl5_8 ),
    inference(resolution,[],[f39,f91])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f222,plain,
    ( spl5_27
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f215,f65,f55,f219])).

fof(f215,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_3 ),
    inference(resolution,[],[f48,f67])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f209,plain,
    ( spl5_25
    | ~ spl5_2
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f202,f65,f55,f60,f206])).

fof(f60,plain,
    ( spl5_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f202,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ spl5_3 ),
    inference(resolution,[],[f47,f67])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f184,plain,
    ( spl5_21
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f177,f65,f55,f181])).

fof(f177,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl5_3 ),
    inference(resolution,[],[f38,f67])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f137,plain,
    ( spl5_14
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f125,f89,f134])).

fof(f125,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_8 ),
    inference(resolution,[],[f45,f91])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f96,plain,
    ( ~ spl5_4
    | spl5_9 ),
    inference(avatar_split_clause,[],[f30,f94,f70])).

fof(f30,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK2)
      | ~ r2_hidden(sK1,X3)
      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <~> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <~> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1,X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r2_hidden(X1,k1_tops_1(X0,X2))
            <=> ? [X3] :
                  ( r2_hidden(X1,X3)
                  & r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).

fof(f92,plain,
    ( spl5_4
    | spl5_8 ),
    inference(avatar_split_clause,[],[f31,f89,f70])).

fof(f31,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f87,plain,
    ( spl5_4
    | spl5_7 ),
    inference(avatar_split_clause,[],[f32,f84,f70])).

fof(f32,plain,
    ( v3_pre_topc(sK3,sK0)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f82,plain,
    ( spl5_4
    | spl5_6 ),
    inference(avatar_split_clause,[],[f33,f79,f70])).

fof(f33,plain,
    ( r1_tarski(sK3,sK2)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f77,plain,
    ( spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f34,f74,f70])).

fof(f34,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f68,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f35,f65])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f63,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f36,f60])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f58,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f37,f55])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:58:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (20315)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.51  % (20307)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (20299)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (20297)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (20306)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (20294)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (20293)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (20323)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (20298)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (20309)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (20301)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (20303)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (20296)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (20321)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (20308)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (20302)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (20295)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (20316)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (20318)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (20322)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (20310)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (20320)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (20300)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (20312)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (20313)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.56  % (20304)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (20311)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (20309)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  % (20319)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.56  fof(f884,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f58,f63,f68,f77,f82,f87,f92,f96,f137,f184,f209,f222,f301,f566,f609,f682,f732,f733,f858,f874,f878])).
% 0.22/0.56  fof(f878,plain,(
% 0.22/0.56    spl5_4 | ~spl5_5 | ~spl5_124),
% 0.22/0.56    inference(avatar_split_clause,[],[f875,f837,f74,f70])).
% 0.22/0.56  fof(f70,plain,(
% 0.22/0.56    spl5_4 <=> r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.56  fof(f74,plain,(
% 0.22/0.56    spl5_5 <=> r2_hidden(sK1,sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.56  fof(f837,plain,(
% 0.22/0.56    spl5_124 <=> r1_tarski(sK3,k1_tops_1(sK0,sK2))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_124])])).
% 0.22/0.56  fof(f875,plain,(
% 0.22/0.56    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | (~spl5_5 | ~spl5_124)),
% 0.22/0.56    inference(resolution,[],[f838,f121])).
% 0.22/0.56  fof(f121,plain,(
% 0.22/0.56    ( ! [X0] : (~r1_tarski(sK3,X0) | r2_hidden(sK1,X0)) ) | ~spl5_5),
% 0.22/0.56    inference(resolution,[],[f49,f76])).
% 0.22/0.56  fof(f76,plain,(
% 0.22/0.56    r2_hidden(sK1,sK3) | ~spl5_5),
% 0.22/0.56    inference(avatar_component_clause,[],[f74])).
% 0.22/0.56  % (20305)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.57  % (20317)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.57  % (20295)Refutation not found, incomplete strategy% (20295)------------------------------
% 0.22/0.57  % (20295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (20295)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (20295)Memory used [KB]: 11001
% 0.22/0.57  % (20295)Time elapsed: 0.157 s
% 0.22/0.57  % (20295)------------------------------
% 0.22/0.57  % (20295)------------------------------
% 0.22/0.58  fof(f49,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f29])).
% 0.22/0.58  fof(f29,plain,(
% 0.22/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f1])).
% 0.22/0.58  fof(f1,axiom,(
% 0.22/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.58  fof(f838,plain,(
% 0.22/0.58    r1_tarski(sK3,k1_tops_1(sK0,sK2)) | ~spl5_124),
% 0.22/0.58    inference(avatar_component_clause,[],[f837])).
% 0.22/0.58  fof(f874,plain,(
% 0.22/0.58    k3_subset_1(u1_struct_0(sK0),sK3) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) | sK3 != k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) | k1_tops_1(sK0,sK3) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))) | r1_tarski(sK3,k1_tops_1(sK0,sK2)) | ~r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))),
% 0.22/0.58    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.58  fof(f858,plain,(
% 0.22/0.58    ~spl5_6 | spl5_128 | ~spl5_3 | ~spl5_43),
% 0.22/0.58    inference(avatar_split_clause,[],[f814,f323,f65,f855,f79])).
% 0.22/0.58  fof(f79,plain,(
% 0.22/0.58    spl5_6 <=> r1_tarski(sK3,sK2)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.58  fof(f855,plain,(
% 0.22/0.58    spl5_128 <=> r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_128])])).
% 0.22/0.58  fof(f65,plain,(
% 0.22/0.58    spl5_3 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.58  fof(f323,plain,(
% 0.22/0.58    spl5_43 <=> ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X1)) | ~r1_tarski(sK3,X1))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 0.22/0.58  fof(f814,plain,(
% 0.22/0.58    r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) | ~r1_tarski(sK3,sK2) | (~spl5_3 | ~spl5_43)),
% 0.22/0.58    inference(resolution,[],[f324,f67])).
% 0.22/0.58  fof(f67,plain,(
% 0.22/0.58    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_3),
% 0.22/0.58    inference(avatar_component_clause,[],[f65])).
% 0.22/0.58  fof(f324,plain,(
% 0.22/0.58    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X1)) | ~r1_tarski(sK3,X1)) ) | ~spl5_43),
% 0.22/0.58    inference(avatar_component_clause,[],[f323])).
% 0.22/0.58  fof(f733,plain,(
% 0.22/0.58    spl5_19 | ~spl5_8),
% 0.22/0.58    inference(avatar_split_clause,[],[f729,f89,f167])).
% 0.22/0.58  fof(f167,plain,(
% 0.22/0.58    spl5_19 <=> sK3 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.22/0.58  fof(f89,plain,(
% 0.22/0.58    spl5_8 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.58  fof(f729,plain,(
% 0.22/0.58    sK3 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) | ~spl5_8),
% 0.22/0.58    inference(resolution,[],[f91,f46])).
% 0.22/0.58  fof(f46,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.22/0.58    inference(cnf_transformation,[],[f24])).
% 0.22/0.58  fof(f24,plain,(
% 0.22/0.58    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f3])).
% 0.22/0.58  fof(f3,axiom,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.22/0.58  fof(f91,plain,(
% 0.22/0.58    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_8),
% 0.22/0.58    inference(avatar_component_clause,[],[f89])).
% 0.22/0.58  fof(f732,plain,(
% 0.22/0.58    spl5_43 | ~spl5_1 | ~spl5_8),
% 0.22/0.58    inference(avatar_split_clause,[],[f726,f89,f55,f323])).
% 0.22/0.58  fof(f55,plain,(
% 0.22/0.58    spl5_1 <=> l1_pre_topc(sK0)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.58  fof(f726,plain,(
% 0.22/0.58    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK3,X0) | r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X0))) ) | ~spl5_8),
% 0.22/0.58    inference(resolution,[],[f91,f44])).
% 0.22/0.58  fof(f44,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f22])).
% 0.22/0.58  fof(f22,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.58    inference(flattening,[],[f21])).
% 0.22/0.58  fof(f21,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f11])).
% 0.22/0.58  fof(f11,axiom,(
% 0.22/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 0.22/0.58  fof(f682,plain,(
% 0.22/0.58    ~spl5_25 | ~spl5_21 | ~spl5_4 | ~spl5_9 | ~spl5_27),
% 0.22/0.58    inference(avatar_split_clause,[],[f651,f219,f94,f70,f181,f206])).
% 0.22/0.58  fof(f206,plain,(
% 0.22/0.58    spl5_25 <=> v3_pre_topc(k1_tops_1(sK0,sK2),sK0)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.22/0.58  fof(f181,plain,(
% 0.22/0.58    spl5_21 <=> r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.22/0.58  fof(f94,plain,(
% 0.22/0.58    spl5_9 <=> ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.58  fof(f219,plain,(
% 0.22/0.58    spl5_27 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.22/0.58  fof(f651,plain,(
% 0.22/0.58    ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | (~spl5_9 | ~spl5_27)),
% 0.22/0.58    inference(resolution,[],[f95,f221])).
% 0.22/0.58  fof(f221,plain,(
% 0.22/0.58    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_27),
% 0.22/0.58    inference(avatar_component_clause,[],[f219])).
% 0.22/0.58  fof(f95,plain,(
% 0.22/0.58    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0)) ) | ~spl5_9),
% 0.22/0.58    inference(avatar_component_clause,[],[f94])).
% 0.22/0.58  fof(f609,plain,(
% 0.22/0.58    spl5_79 | ~spl5_1 | ~spl5_14 | ~spl5_7 | ~spl5_19),
% 0.22/0.58    inference(avatar_split_clause,[],[f608,f167,f84,f134,f55,f558])).
% 0.22/0.58  fof(f558,plain,(
% 0.22/0.58    spl5_79 <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).
% 0.22/0.58  fof(f134,plain,(
% 0.22/0.58    spl5_14 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.22/0.58  fof(f84,plain,(
% 0.22/0.58    spl5_7 <=> v3_pre_topc(sK3,sK0)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.58  fof(f608,plain,(
% 0.22/0.58    ~v3_pre_topc(sK3,sK0) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0) | ~spl5_19),
% 0.22/0.58    inference(superposition,[],[f42,f169])).
% 0.22/0.58  fof(f169,plain,(
% 0.22/0.58    sK3 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) | ~spl5_19),
% 0.22/0.58    inference(avatar_component_clause,[],[f167])).
% 0.22/0.58  fof(f42,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v4_pre_topc(X1,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f20])).
% 0.22/0.58  fof(f20,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f9])).
% 0.22/0.58  fof(f9,axiom,(
% 0.22/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).
% 0.22/0.58  fof(f566,plain,(
% 0.22/0.58    spl5_80 | ~spl5_79 | ~spl5_1 | ~spl5_14),
% 0.22/0.58    inference(avatar_split_clause,[],[f539,f134,f55,f558,f562])).
% 0.22/0.58  fof(f562,plain,(
% 0.22/0.58    spl5_80 <=> k3_subset_1(u1_struct_0(sK0),sK3) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).
% 0.22/0.58  fof(f539,plain,(
% 0.22/0.58    ~l1_pre_topc(sK0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0) | k3_subset_1(u1_struct_0(sK0),sK3) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) | ~spl5_14),
% 0.22/0.58    inference(resolution,[],[f136,f41])).
% 0.22/0.58  fof(f41,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 0.22/0.58    inference(cnf_transformation,[],[f19])).
% 0.22/0.58  fof(f19,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.58    inference(flattening,[],[f18])).
% 0.22/0.58  fof(f18,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f5])).
% 0.22/0.58  fof(f5,axiom,(
% 0.22/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.22/0.58  fof(f136,plain,(
% 0.22/0.58    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_14),
% 0.22/0.58    inference(avatar_component_clause,[],[f134])).
% 0.22/0.58  fof(f301,plain,(
% 0.22/0.58    spl5_39 | ~spl5_1 | ~spl5_8),
% 0.22/0.58    inference(avatar_split_clause,[],[f290,f89,f55,f298])).
% 0.22/0.58  fof(f298,plain,(
% 0.22/0.58    spl5_39 <=> k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 0.22/0.58  fof(f290,plain,(
% 0.22/0.58    ~l1_pre_topc(sK0) | k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))) | ~spl5_8),
% 0.22/0.58    inference(resolution,[],[f39,f91])).
% 0.22/0.58  fof(f39,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f17])).
% 0.22/0.58  fof(f17,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f6])).
% 0.22/0.58  fof(f6,axiom,(
% 0.22/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 0.22/0.58  fof(f222,plain,(
% 0.22/0.58    spl5_27 | ~spl5_1 | ~spl5_3),
% 0.22/0.58    inference(avatar_split_clause,[],[f215,f65,f55,f219])).
% 0.22/0.58  fof(f215,plain,(
% 0.22/0.58    ~l1_pre_topc(sK0) | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_3),
% 0.22/0.58    inference(resolution,[],[f48,f67])).
% 0.22/0.58  fof(f48,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f28])).
% 0.22/0.58  fof(f28,plain,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.58    inference(flattening,[],[f27])).
% 0.22/0.58  fof(f27,plain,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f7])).
% 0.22/0.58  fof(f7,axiom,(
% 0.22/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 0.22/0.58  fof(f209,plain,(
% 0.22/0.58    spl5_25 | ~spl5_2 | ~spl5_1 | ~spl5_3),
% 0.22/0.58    inference(avatar_split_clause,[],[f202,f65,f55,f60,f206])).
% 0.22/0.58  fof(f60,plain,(
% 0.22/0.58    spl5_2 <=> v2_pre_topc(sK0)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.58  fof(f202,plain,(
% 0.22/0.58    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~spl5_3),
% 0.22/0.58    inference(resolution,[],[f47,f67])).
% 0.22/0.58  fof(f47,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f26])).
% 0.22/0.58  fof(f26,plain,(
% 0.22/0.58    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.58    inference(flattening,[],[f25])).
% 0.22/0.58  fof(f25,plain,(
% 0.22/0.58    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f8])).
% 0.22/0.58  fof(f8,axiom,(
% 0.22/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.22/0.58  fof(f184,plain,(
% 0.22/0.58    spl5_21 | ~spl5_1 | ~spl5_3),
% 0.22/0.58    inference(avatar_split_clause,[],[f177,f65,f55,f181])).
% 0.22/0.58  fof(f177,plain,(
% 0.22/0.58    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~spl5_3),
% 0.22/0.58    inference(resolution,[],[f38,f67])).
% 0.22/0.58  fof(f38,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f16])).
% 0.22/0.58  fof(f16,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f10])).
% 0.22/0.58  fof(f10,axiom,(
% 0.22/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 0.22/0.58  fof(f137,plain,(
% 0.22/0.58    spl5_14 | ~spl5_8),
% 0.22/0.58    inference(avatar_split_clause,[],[f125,f89,f134])).
% 0.22/0.58  fof(f125,plain,(
% 0.22/0.58    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_8),
% 0.22/0.58    inference(resolution,[],[f45,f91])).
% 0.22/0.58  fof(f45,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f23])).
% 0.22/0.58  fof(f23,plain,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f2])).
% 0.22/0.58  fof(f2,axiom,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.22/0.58  fof(f96,plain,(
% 0.22/0.58    ~spl5_4 | spl5_9),
% 0.22/0.58    inference(avatar_split_clause,[],[f30,f94,f70])).
% 0.22/0.58  fof(f30,plain,(
% 0.22/0.58    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK2) | ~r2_hidden(sK1,X3) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f15])).
% 0.22/0.58  fof(f15,plain,(
% 0.22/0.58    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.58    inference(flattening,[],[f14])).
% 0.22/0.58  fof(f14,plain,(
% 0.22/0.58    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f13])).
% 0.22/0.58  fof(f13,negated_conjecture,(
% 0.22/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.22/0.58    inference(negated_conjecture,[],[f12])).
% 0.22/0.58  fof(f12,conjecture,(
% 0.22/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).
% 0.22/0.58  fof(f92,plain,(
% 0.22/0.58    spl5_4 | spl5_8),
% 0.22/0.58    inference(avatar_split_clause,[],[f31,f89,f70])).
% 0.22/0.58  fof(f31,plain,(
% 0.22/0.58    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 0.22/0.58    inference(cnf_transformation,[],[f15])).
% 0.22/0.58  fof(f87,plain,(
% 0.22/0.58    spl5_4 | spl5_7),
% 0.22/0.58    inference(avatar_split_clause,[],[f32,f84,f70])).
% 0.22/0.58  fof(f32,plain,(
% 0.22/0.58    v3_pre_topc(sK3,sK0) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 0.22/0.58    inference(cnf_transformation,[],[f15])).
% 0.22/0.58  fof(f82,plain,(
% 0.22/0.58    spl5_4 | spl5_6),
% 0.22/0.58    inference(avatar_split_clause,[],[f33,f79,f70])).
% 0.22/0.58  fof(f33,plain,(
% 0.22/0.58    r1_tarski(sK3,sK2) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 0.22/0.58    inference(cnf_transformation,[],[f15])).
% 0.22/0.58  fof(f77,plain,(
% 0.22/0.58    spl5_4 | spl5_5),
% 0.22/0.58    inference(avatar_split_clause,[],[f34,f74,f70])).
% 0.22/0.58  fof(f34,plain,(
% 0.22/0.58    r2_hidden(sK1,sK3) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 0.22/0.58    inference(cnf_transformation,[],[f15])).
% 0.22/0.58  fof(f68,plain,(
% 0.22/0.58    spl5_3),
% 0.22/0.58    inference(avatar_split_clause,[],[f35,f65])).
% 0.22/0.58  fof(f35,plain,(
% 0.22/0.58    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.58    inference(cnf_transformation,[],[f15])).
% 0.22/0.58  fof(f63,plain,(
% 0.22/0.58    spl5_2),
% 0.22/0.58    inference(avatar_split_clause,[],[f36,f60])).
% 0.22/0.58  fof(f36,plain,(
% 0.22/0.58    v2_pre_topc(sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f15])).
% 0.22/0.58  fof(f58,plain,(
% 0.22/0.58    spl5_1),
% 0.22/0.58    inference(avatar_split_clause,[],[f37,f55])).
% 0.22/0.58  fof(f37,plain,(
% 0.22/0.58    l1_pre_topc(sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f15])).
% 0.22/0.58  % SZS output end Proof for theBenchmark
% 0.22/0.58  % (20309)------------------------------
% 0.22/0.58  % (20309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (20309)Termination reason: Refutation
% 0.22/0.58  
% 0.22/0.58  % (20309)Memory used [KB]: 11385
% 0.22/0.58  % (20309)Time elapsed: 0.150 s
% 0.22/0.58  % (20309)------------------------------
% 0.22/0.58  % (20309)------------------------------
% 0.22/0.58  % (20292)Success in time 0.213 s
%------------------------------------------------------------------------------
