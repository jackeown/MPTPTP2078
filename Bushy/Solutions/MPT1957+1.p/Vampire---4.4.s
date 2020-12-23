%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_7__t4_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:07 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   40 (  46 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :   13
%              Number of atoms          :   78 (  87 expanded)
%              Number of equality atoms :   41 (  44 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f155,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f154])).

fof(f154,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | ~ spl1_1 ),
    inference(trivial_inequality_removal,[],[f152])).

fof(f152,plain,
    ( k3_yellow_1(sK0) != k3_yellow_1(sK0)
    | ~ spl1_1 ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,
    ( ! [X0] :
        ( k9_setfam_1(sK0) != k9_setfam_1(X0)
        | k3_yellow_1(sK0) != k3_yellow_1(X0) )
    | ~ spl1_1 ),
    inference(superposition,[],[f65,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k3_yellow_1(X1)) = k9_setfam_1(X0)
      | k3_yellow_1(X0) != k3_yellow_1(X1) ) ),
    inference(superposition,[],[f83,f48])).

fof(f48,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t4_waybel_7.p',t4_yellow_1)).

fof(f83,plain,(
    ! [X0,X1] :
      ( k3_yellow_1(X0) != k2_yellow_1(X1)
      | u1_struct_0(k3_yellow_1(X0)) = X1 ) ),
    inference(subsumption_resolution,[],[f81,f54])).

fof(f54,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t4_waybel_7.p',dt_k3_yellow_1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( k3_yellow_1(X0) != k2_yellow_1(X1)
      | u1_struct_0(k3_yellow_1(X0)) = X1
      | ~ l1_orders_2(k3_yellow_1(X0)) ) ),
    inference(superposition,[],[f79,f68])).

fof(f68,plain,(
    ! [X0] : k3_yellow_1(X0) = g1_orders_2(u1_struct_0(k3_yellow_1(X0)),u1_orders_2(k3_yellow_1(X0))) ),
    inference(subsumption_resolution,[],[f67,f54])).

fof(f67,plain,(
    ! [X0] :
      ( ~ l1_orders_2(k3_yellow_1(X0))
      | k3_yellow_1(X0) = g1_orders_2(u1_struct_0(k3_yellow_1(X0)),u1_orders_2(k3_yellow_1(X0))) ) ),
    inference(resolution,[],[f46,f53])).

fof(f53,plain,(
    ! [X0] : v1_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t4_waybel_7.p',abstractness_v1_orders_2)).

fof(f79,plain,(
    ! [X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k2_yellow_1(X1)
      | u1_struct_0(X0) = X1
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f76,f59])).

fof(f59,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k9_setfam_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(forward_demodulation,[],[f52,f49])).

fof(f49,plain,(
    ! [X0] : k9_setfam_1(X0) = k1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] : k9_setfam_1(X0) = k1_zfmisc_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t4_waybel_7.p',redefinition_k9_setfam_1)).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t4_waybel_7.p',dt_u1_orders_2)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k9_setfam_1(k2_zfmisc_1(X1,X1)))
      | g1_orders_2(X1,X2) != k2_yellow_1(X0)
      | X0 = X1 ) ),
    inference(superposition,[],[f56,f47])).

fof(f47,plain,(
    ! [X0] : g1_orders_2(X0,k1_yellow_1(X0)) = k2_yellow_1(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : g1_orders_2(X0,k1_yellow_1(X0)) = k2_yellow_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t4_waybel_7.p',d1_yellow_1)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k9_setfam_1(k2_zfmisc_1(X0,X0)))
      | X0 = X2 ) ),
    inference(forward_demodulation,[],[f44,f49])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t4_waybel_7.p',free_g1_orders_2)).

fof(f65,plain,
    ( u1_struct_0(k3_yellow_1(sK0)) != k9_setfam_1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl1_1
  <=> u1_struct_0(k3_yellow_1(sK0)) != k9_setfam_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f66,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f42,f64])).

fof(f42,plain,(
    u1_struct_0(k3_yellow_1(sK0)) != k9_setfam_1(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ? [X0] : u1_struct_0(k3_yellow_1(X0)) != k9_setfam_1(X0) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] : u1_struct_0(k3_yellow_1(X0)) = k9_setfam_1(X0) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] : u1_struct_0(k3_yellow_1(X0)) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t4_waybel_7.p',t4_waybel_7)).
%------------------------------------------------------------------------------
