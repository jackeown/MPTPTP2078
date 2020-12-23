%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1127+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:19 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  125 (2680 expanded)
%              Number of leaves         :   18 ( 612 expanded)
%              Depth                    :   14
%              Number of atoms          :  400 (7360 expanded)
%              Number of equality atoms :   17 ( 518 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f280,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f75,f151,f156,f170,f174,f192,f206,f221,f237,f256,f273,f279])).

fof(f279,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f274])).

fof(f274,plain,
    ( $false
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f95,f70])).

fof(f70,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl5_4
  <=> r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f95,plain,(
    r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(backward_demodulation,[],[f91,f83])).

fof(f83,plain,(
    u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(unit_resulting_resolution,[],[f54,f53,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f53,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(unit_resulting_resolution,[],[f49,f50,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f50,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(unit_resulting_resolution,[],[f47,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f47,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f19,f45])).

fof(f45,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f19,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ~ v2_pre_topc(X0)
      & v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ~ v2_pre_topc(X0)
      & v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => v2_pre_topc(X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_pre_topc)).

fof(f49,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(unit_resulting_resolution,[],[f47,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f54,plain,(
    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    inference(unit_resulting_resolution,[],[f50,f45])).

fof(f91,plain,(
    r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0)) ),
    inference(backward_demodulation,[],[f52,f84])).

fof(f84,plain,(
    u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(unit_resulting_resolution,[],[f54,f53,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f52,plain,(
    r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(unit_resulting_resolution,[],[f20,f50,f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f20,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f273,plain,
    ( ~ spl5_2
    | spl5_3
    | ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f269])).

fof(f269,plain,
    ( $false
    | ~ spl5_2
    | spl5_3
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f264,f66,f263,f150])).

fof(f150,plain,
    ( ! [X2] :
        ( r2_hidden(k5_setfam_1(u1_struct_0(sK0),X2),u1_pre_topc(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X2,u1_pre_topc(sK0)) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl5_7
  <=> ! [X2] :
        ( ~ r1_tarski(X2,u1_pre_topc(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | r2_hidden(k5_setfam_1(u1_struct_0(sK0),X2),u1_pre_topc(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f263,plain,
    ( m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f21,f19,f95,f61,f25])).

fof(f25,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK2(X0),sK3(X0)),u1_pre_topc(X0))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f61,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2(sK0),sK3(sK0)),u1_pre_topc(sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl5_2
  <=> r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2(sK0),sK3(sK0)),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f21,plain,(
    ~ v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f66,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK1(sK0)),u1_pre_topc(sK0))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl5_3
  <=> r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK1(sK0)),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f264,plain,
    ( r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f21,f19,f95,f61,f29])).

fof(f29,plain,(
    ! [X0] :
      ( r1_tarski(sK1(X0),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK2(X0),sK3(X0)),u1_pre_topc(X0))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f256,plain,
    ( ~ spl5_7
    | spl5_12 ),
    inference(avatar_contradiction_clause,[],[f252])).

fof(f252,plain,
    ( $false
    | ~ spl5_7
    | spl5_12 ),
    inference(unit_resulting_resolution,[],[f242,f241,f243,f150])).

fof(f243,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK1(sK0)),u1_pre_topc(sK0))
    | spl5_12 ),
    inference(unit_resulting_resolution,[],[f21,f19,f95,f191,f30])).

fof(f30,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK1(X0)),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f191,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl5_12
  <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f241,plain,
    ( m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl5_12 ),
    inference(unit_resulting_resolution,[],[f21,f19,f95,f191,f22])).

fof(f22,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f242,plain,
    ( r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | spl5_12 ),
    inference(unit_resulting_resolution,[],[f21,f19,f95,f191,f26])).

fof(f26,plain,(
    ! [X0] :
      ( r1_tarski(sK1(X0),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f237,plain,
    ( ~ spl5_7
    | spl5_11 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | ~ spl5_7
    | spl5_11 ),
    inference(unit_resulting_resolution,[],[f223,f224,f222,f150])).

fof(f222,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK1(sK0)),u1_pre_topc(sK0))
    | spl5_11 ),
    inference(unit_resulting_resolution,[],[f21,f19,f95,f187,f35])).

fof(f35,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK1(X0)),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f187,plain,
    ( ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl5_11
  <=> m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f224,plain,
    ( m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl5_11 ),
    inference(unit_resulting_resolution,[],[f21,f19,f95,f187,f37])).

fof(f37,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f223,plain,
    ( r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | spl5_11 ),
    inference(unit_resulting_resolution,[],[f21,f19,f95,f187,f36])).

fof(f36,plain,(
    ! [X0] :
      ( r1_tarski(sK1(X0),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f221,plain,
    ( ~ spl5_7
    | spl5_10 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | ~ spl5_7
    | spl5_10 ),
    inference(unit_resulting_resolution,[],[f208,f207,f209,f150])).

fof(f209,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK1(sK0)),u1_pre_topc(sK0))
    | spl5_10 ),
    inference(unit_resulting_resolution,[],[f21,f19,f95,f183,f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK1(X0)),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f183,plain,
    ( ~ r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl5_10
  <=> r2_hidden(sK2(sK0),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f207,plain,
    ( m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl5_10 ),
    inference(unit_resulting_resolution,[],[f21,f19,f95,f183,f23])).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK2(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f208,plain,
    ( r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | spl5_10 ),
    inference(unit_resulting_resolution,[],[f21,f19,f95,f183,f27])).

fof(f27,plain,(
    ! [X0] :
      ( r1_tarski(sK1(X0),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK2(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f206,plain,
    ( ~ spl5_7
    | spl5_9 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | ~ spl5_7
    | spl5_9 ),
    inference(unit_resulting_resolution,[],[f194,f193,f195,f150])).

fof(f195,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK1(sK0)),u1_pre_topc(sK0))
    | spl5_9 ),
    inference(unit_resulting_resolution,[],[f21,f19,f95,f179,f32])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK1(X0)),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f179,plain,
    ( ~ r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl5_9
  <=> r2_hidden(sK3(sK0),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f193,plain,
    ( m1_subset_1(sK1(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl5_9 ),
    inference(unit_resulting_resolution,[],[f21,f19,f95,f179,f24])).

fof(f24,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK3(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f194,plain,
    ( r1_tarski(sK1(sK0),u1_pre_topc(sK0))
    | spl5_9 ),
    inference(unit_resulting_resolution,[],[f21,f19,f95,f179,f28])).

fof(f28,plain,(
    ! [X0] :
      ( r1_tarski(sK1(X0),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK3(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f192,plain,
    ( ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | spl5_2
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f175,f172,f60,f189,f185,f181,f177])).

fof(f172,plain,
    ( spl5_8
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X1,u1_pre_topc(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,u1_pre_topc(sK0))
        | r2_hidden(k9_subset_1(u1_struct_0(sK0),X0,X1),u1_pre_topc(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f175,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | spl5_2
    | ~ spl5_8 ),
    inference(resolution,[],[f173,f62])).

fof(f62,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2(sK0),sK3(sK0)),u1_pre_topc(sK0))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f173,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k9_subset_1(u1_struct_0(sK0),X0,X1),u1_pre_topc(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,u1_pre_topc(sK0))
        | ~ r2_hidden(X1,u1_pre_topc(sK0)) )
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f172])).

fof(f174,plain,
    ( ~ spl5_5
    | ~ spl5_6
    | spl5_8 ),
    inference(avatar_split_clause,[],[f117,f172,f145,f141])).

fof(f141,plain,
    ( spl5_5
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f145,plain,
    ( spl5_6
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,u1_pre_topc(sK0))
      | ~ r2_hidden(X0,u1_pre_topc(sK0))
      | r2_hidden(k9_subset_1(u1_struct_0(sK0),X0,X1),u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ) ),
    inference(forward_demodulation,[],[f116,f84])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_pre_topc(sK0))
      | r2_hidden(k9_subset_1(u1_struct_0(sK0),X0,X1),u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ) ),
    inference(forward_demodulation,[],[f115,f84])).

fof(f115,plain,(
    ! [X0,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(sK0),X0,X1),u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
      | ~ r2_hidden(X1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ) ),
    inference(forward_demodulation,[],[f109,f84])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(sK0),X0,X1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
      | ~ r2_hidden(X1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ) ),
    inference(superposition,[],[f34,f83])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ r2_hidden(X2,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f170,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f47,f147,f43])).

fof(f147,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f145])).

fof(f156,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f20,f143])).

fof(f143,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f141])).

fof(f151,plain,
    ( ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f119,f149,f145,f141])).

fof(f119,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,u1_pre_topc(sK0))
      | r2_hidden(k5_setfam_1(u1_struct_0(sK0),X2),u1_pre_topc(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ) ),
    inference(forward_demodulation,[],[f118,f84])).

fof(f118,plain,(
    ! [X2] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(sK0),X2),u1_pre_topc(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ r1_tarski(X2,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ) ),
    inference(forward_demodulation,[],[f112,f84])).

fof(f112,plain,(
    ! [X2] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(sK0),X2),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ r1_tarski(X2,u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ) ),
    inference(superposition,[],[f38,f83])).

fof(f38,plain,(
    ! [X0,X3] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r1_tarski(X3,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

% (22276)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f75,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f19,f58])).

fof(f58,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl5_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f71,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f48,f68,f64,f60,f56])).

fof(f48,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK1(sK0)),u1_pre_topc(sK0))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2(sK0),sK3(sK0)),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f21,f33])).

fof(f33,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK1(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK2(X0),sK3(X0)),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

%------------------------------------------------------------------------------
