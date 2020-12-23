%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow19__t4_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:53 EDT 2019

% Result     : Theorem 7.67s
% Output     : Refutation 7.67s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 618 expanded)
%              Number of leaves         :   24 ( 146 expanded)
%              Depth                    :   10
%              Number of atoms          :  427 (3383 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20793,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f241,f271,f592,f1300,f1310,f4665,f4681,f15615,f15654,f20761])).

fof(f20761,plain,
    ( ~ spl14_0
    | spl14_3
    | spl14_101 ),
    inference(avatar_contradiction_clause,[],[f20737])).

fof(f20737,plain,
    ( $false
    | ~ spl14_0
    | ~ spl14_3
    | ~ spl14_101 ),
    inference(unit_resulting_resolution,[],[f104,f103,f234,f15614,f1355,f1358,f1357,f115])).

fof(f115,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | ~ r2_hidden(X2,X3)
      | r2_hidden(X3,X1)
      | ~ r2_waybel_7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r2_hidden(X2,X3)
                  & v3_pre_topc(X3,X0) )
               => r2_hidden(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t4_yellow19.p',d5_waybel_7)).

fof(f1357,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK3(k1_yellow19(sK0,sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl14_3 ),
    inference(unit_resulting_resolution,[],[f104,f616,f141])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t4_yellow19.p',dt_k1_tops_1)).

fof(f616,plain,
    ( m1_subset_1(sK3(k1_yellow19(sK0,sK1),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl14_3 ),
    inference(unit_resulting_resolution,[],[f102,f103,f104,f101,f600,f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t4_yellow19.p',dt_m1_connsp_2)).

fof(f600,plain,
    ( m1_connsp_2(sK3(k1_yellow19(sK0,sK1),sK2),sK0,sK1)
    | ~ spl14_3 ),
    inference(unit_resulting_resolution,[],[f104,f103,f102,f101,f593,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_yellow19(X0,X1)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t4_yellow19.p',t3_yellow19)).

fof(f593,plain,
    ( r2_hidden(sK3(k1_yellow19(sK0,sK1),sK2),k1_yellow19(sK0,sK1))
    | ~ spl14_3 ),
    inference(unit_resulting_resolution,[],[f237,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t4_yellow19.p',d3_tarski)).

fof(f237,plain,
    ( ~ r1_tarski(k1_yellow19(sK0,sK1),sK2)
    | ~ spl14_3 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl14_3
  <=> ~ r1_tarski(k1_yellow19(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).

fof(f101,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_waybel_7(X0,X2,X1)
              <~> r1_tarski(k1_yellow19(X0,X1),X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_waybel_7(X0,X2,X1)
              <~> r1_tarski(k1_yellow19(X0,X1),X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
               => ( r2_waybel_7(X0,X2,X1)
                <=> r1_tarski(k1_yellow19(X0,X1),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
             => ( r2_waybel_7(X0,X2,X1)
              <=> r1_tarski(k1_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t4_yellow19.p',t4_yellow19)).

fof(f102,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f1358,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK3(k1_yellow19(sK0,sK1),sK2)),sK0)
    | ~ spl14_3 ),
    inference(unit_resulting_resolution,[],[f104,f103,f616,f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t4_yellow19.p',fc9_tops_1)).

fof(f1355,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK3(k1_yellow19(sK0,sK1),sK2)))
    | ~ spl14_3 ),
    inference(unit_resulting_resolution,[],[f104,f102,f103,f101,f600,f616,f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t4_yellow19.p',d1_connsp_2)).

fof(f15614,plain,
    ( ~ r2_hidden(k1_tops_1(sK0,sK3(k1_yellow19(sK0,sK1),sK2)),sK2)
    | ~ spl14_101 ),
    inference(avatar_component_clause,[],[f15613])).

fof(f15613,plain,
    ( spl14_101
  <=> ~ r2_hidden(k1_tops_1(sK0,sK3(k1_yellow19(sK0,sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_101])])).

fof(f234,plain,
    ( r2_waybel_7(sK0,sK2,sK1)
    | ~ spl14_0 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl14_0
  <=> r2_waybel_7(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_0])])).

fof(f103,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f104,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f15654,plain,
    ( spl14_3
    | spl14_99 ),
    inference(avatar_contradiction_clause,[],[f15638])).

fof(f15638,plain,
    ( $false
    | ~ spl14_3
    | ~ spl14_99 ),
    inference(unit_resulting_resolution,[],[f1361,f15608,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t4_yellow19.p',t3_subset)).

fof(f15608,plain,
    ( ~ m1_subset_1(sK3(k1_yellow19(sK0,sK1),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl14_99 ),
    inference(avatar_component_clause,[],[f15607])).

fof(f15607,plain,
    ( spl14_99
  <=> ~ m1_subset_1(sK3(k1_yellow19(sK0,sK1),sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_99])])).

fof(f1361,plain,
    ( r1_tarski(sK3(k1_yellow19(sK0,sK1),sK2),u1_struct_0(sK0))
    | ~ spl14_3 ),
    inference(unit_resulting_resolution,[],[f616,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f15615,plain,
    ( ~ spl14_99
    | ~ spl14_101
    | ~ spl14_74 ),
    inference(avatar_split_clause,[],[f4706,f4663,f15613,f15607])).

fof(f4663,plain,
    ( spl14_74
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK3(k1_yellow19(sK0,sK1),sK2))
        | ~ r2_hidden(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_74])])).

fof(f4706,plain,
    ( ~ r2_hidden(k1_tops_1(sK0,sK3(k1_yellow19(sK0,sK1),sK2)),sK2)
    | ~ m1_subset_1(sK3(k1_yellow19(sK0,sK1),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl14_74 ),
    inference(resolution,[],[f4664,f179])).

fof(f179,plain,(
    ! [X0] :
      ( r1_tarski(k1_tops_1(sK0,X0),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f104,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t4_yellow19.p',t44_tops_1)).

fof(f4664,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK3(k1_yellow19(sK0,sK1),sK2))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl14_74 ),
    inference(avatar_component_clause,[],[f4663])).

fof(f4681,plain,
    ( spl14_3
    | spl14_73 ),
    inference(avatar_contradiction_clause,[],[f4675])).

fof(f4675,plain,
    ( $false
    | ~ spl14_3
    | ~ spl14_73 ),
    inference(unit_resulting_resolution,[],[f616,f4661,f106])).

fof(f4661,plain,
    ( ~ r1_tarski(sK3(k1_yellow19(sK0,sK1),sK2),u1_struct_0(sK0))
    | ~ spl14_73 ),
    inference(avatar_component_clause,[],[f4660])).

fof(f4660,plain,
    ( spl14_73
  <=> ~ r1_tarski(sK3(k1_yellow19(sK0,sK1),sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_73])])).

fof(f4665,plain,
    ( ~ spl14_73
    | spl14_74
    | spl14_3
    | ~ spl14_44 ),
    inference(avatar_split_clause,[],[f1322,f1298,f236,f4663,f4660])).

fof(f1298,plain,
    ( spl14_44
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | r2_hidden(X1,sK2)
        | ~ r2_hidden(X0,sK2)
        | ~ r1_tarski(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_44])])).

fof(f1322,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK3(k1_yellow19(sK0,sK1),sK2))
        | ~ r2_hidden(X0,sK2)
        | ~ r1_tarski(sK3(k1_yellow19(sK0,sK1),sK2),u1_struct_0(sK0)) )
    | ~ spl14_3
    | ~ spl14_44 ),
    inference(resolution,[],[f1299,f594])).

fof(f594,plain,
    ( ~ r2_hidden(sK3(k1_yellow19(sK0,sK1),sK2),sK2)
    | ~ spl14_3 ),
    inference(unit_resulting_resolution,[],[f237,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f1299,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X1,sK2)
        | ~ r1_tarski(X0,X1)
        | ~ r2_hidden(X0,sK2)
        | ~ r1_tarski(X1,u1_struct_0(sK0)) )
    | ~ spl14_44 ),
    inference(avatar_component_clause,[],[f1298])).

fof(f1310,plain,(
    spl14_43 ),
    inference(avatar_contradiction_clause,[],[f1301])).

fof(f1301,plain,
    ( $false
    | ~ spl14_43 ),
    inference(unit_resulting_resolution,[],[f198,f1296])).

fof(f1296,plain,
    ( ~ v13_waybel_0(sK2,k3_yellow_1(u1_struct_0(sK0)))
    | ~ spl14_43 ),
    inference(avatar_component_clause,[],[f1295])).

fof(f1295,plain,
    ( spl14_43
  <=> ~ v13_waybel_0(sK2,k3_yellow_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_43])])).

fof(f198,plain,(
    v13_waybel_0(sK2,k3_yellow_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f191,f99])).

fof(f99,plain,(
    v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f191,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f178,f129])).

fof(f129,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t4_yellow19.p',d3_struct_0)).

fof(f178,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f104,f154])).

fof(f154,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t4_yellow19.p',dt_l1_pre_topc)).

fof(f1300,plain,
    ( ~ spl14_43
    | spl14_44 ),
    inference(avatar_split_clause,[],[f207,f1298,f1295])).

fof(f207,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK2)
      | r2_hidden(X1,sK2)
      | ~ v13_waybel_0(sK2,k3_yellow_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f199,f121])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X3,X0)
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,k3_yellow_1(X0)) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
     => ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,X1)
              & r1_tarski(X3,X0)
              & r1_tarski(X2,X3) )
           => r2_hidden(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t4_yellow19.p',t11_waybel_7)).

fof(f199,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK0))))) ),
    inference(backward_demodulation,[],[f191,f100])).

fof(f100,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f49])).

fof(f592,plain,
    ( spl14_1
    | ~ spl14_2 ),
    inference(avatar_contradiction_clause,[],[f589])).

fof(f589,plain,
    ( $false
    | ~ spl14_1
    | ~ spl14_2 ),
    inference(unit_resulting_resolution,[],[f104,f103,f102,f101,f368,f284,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X2,X0,X1)
      | r2_hidden(X2,k1_yellow19(X0,X1)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f284,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,sK1),k1_yellow19(sK0,sK1))
    | ~ spl14_1
    | ~ spl14_2 ),
    inference(unit_resulting_resolution,[],[f240,f277,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f277,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,sK1),sK2)
    | ~ spl14_1 ),
    inference(unit_resulting_resolution,[],[f104,f103,f231,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_waybel_7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f231,plain,
    ( ~ r2_waybel_7(sK0,sK2,sK1)
    | ~ spl14_1 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl14_1
  <=> ~ r2_waybel_7(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f240,plain,
    ( r1_tarski(k1_yellow19(sK0,sK1),sK2)
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl14_2
  <=> r1_tarski(k1_yellow19(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f368,plain,
    ( m1_connsp_2(sK4(sK0,sK2,sK1),sK0,sK1)
    | ~ spl14_1 ),
    inference(unit_resulting_resolution,[],[f104,f103,f102,f101,f276,f275,f274,f143])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
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
    inference(flattening,[],[f81])).

fof(f81,plain,(
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
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/yellow19__t4_yellow19.p',t5_connsp_2)).

fof(f274,plain,
    ( m1_subset_1(sK4(sK0,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl14_1 ),
    inference(unit_resulting_resolution,[],[f104,f103,f231,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | r2_waybel_7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f275,plain,
    ( v3_pre_topc(sK4(sK0,sK2,sK1),sK0)
    | ~ spl14_1 ),
    inference(unit_resulting_resolution,[],[f104,f103,f231,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(sK4(X0,X1,X2),X0)
      | r2_waybel_7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f276,plain,
    ( r2_hidden(sK1,sK4(sK0,sK2,sK1))
    | ~ spl14_1 ),
    inference(unit_resulting_resolution,[],[f104,f103,f231,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_hidden(X2,sK4(X0,X1,X2))
      | r2_waybel_7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f271,plain,
    ( ~ spl14_1
    | ~ spl14_3 ),
    inference(avatar_split_clause,[],[f98,f236,f230])).

fof(f98,plain,
    ( ~ r1_tarski(k1_yellow19(sK0,sK1),sK2)
    | ~ r2_waybel_7(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f241,plain,
    ( spl14_0
    | spl14_2 ),
    inference(avatar_split_clause,[],[f97,f239,f233])).

fof(f97,plain,
    ( r1_tarski(k1_yellow19(sK0,sK1),sK2)
    | r2_waybel_7(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
