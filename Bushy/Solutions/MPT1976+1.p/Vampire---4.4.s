%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_7__t25_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:05 EDT 2019

% Result     : Theorem 2.37s
% Output     : Refutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :  268 (1434 expanded)
%              Number of leaves         :   45 ( 445 expanded)
%              Depth                    :   27
%              Number of atoms          : 1219 (5470 expanded)
%              Number of equality atoms :   57 ( 819 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15725,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f240,f247,f254,f258,f763,f4746,f9420,f9429,f10147,f10214,f14786,f15093,f15146,f15151,f15723])).

fof(f15723,plain,
    ( spl7_3
    | spl7_5
    | ~ spl7_6
    | ~ spl7_1626 ),
    inference(avatar_contradiction_clause,[],[f15722])).

fof(f15722,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_1626 ),
    inference(subsumption_resolution,[],[f15721,f239])).

fof(f239,plain,
    ( ~ r2_hidden(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl7_3
  <=> ~ r2_hidden(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f15721,plain,
    ( r2_hidden(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_1626 ),
    inference(subsumption_resolution,[],[f15717,f253])).

fof(f253,plain,
    ( m1_subset_1(sK2,k9_setfam_1(sK0))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl7_6
  <=> m1_subset_1(sK2,k9_setfam_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f15717,plain,
    ( ~ m1_subset_1(sK2,k9_setfam_1(sK0))
    | r2_hidden(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl7_5
    | ~ spl7_1626 ),
    inference(resolution,[],[f15321,f246])).

fof(f246,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl7_5
  <=> ~ r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f15321,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,k9_setfam_1(sK0))
        | r2_hidden(k4_xboole_0(sK0,X0),sK1) )
    | ~ spl7_1626 ),
    inference(duplicate_literal_removal,[],[f15319])).

fof(f15319,plain,
    ( ! [X0] :
        ( r2_hidden(k4_xboole_0(sK0,X0),sK1)
        | ~ m1_subset_1(X0,k9_setfam_1(sK0))
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,k9_setfam_1(sK0)) )
    | ~ spl7_1626 ),
    inference(superposition,[],[f15092,f2908])).

fof(f2908,plain,(
    ! [X0,X1] :
      ( k7_waybel_1(g1_orders_2(k9_setfam_1(X0),k1_wellord2(k9_setfam_1(X0))),X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k9_setfam_1(X0)) ) ),
    inference(backward_demodulation,[],[f2841,f216])).

fof(f216,plain,(
    ! [X0,X1] :
      ( k7_waybel_1(g1_orders_2(k9_setfam_1(X0),k1_wellord2(k9_setfam_1(X0))),X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(k9_setfam_1(X0),k1_wellord2(k9_setfam_1(X0))))) ) ),
    inference(definition_unfolding,[],[f164,f159,f185,f185])).

fof(f185,plain,(
    ! [X0] : k3_yellow_1(X0) = g1_orders_2(k9_setfam_1(X0),k1_wellord2(k9_setfam_1(X0))) ),
    inference(definition_unfolding,[],[f120,f184])).

fof(f184,plain,(
    ! [X0] : g1_orders_2(X0,k1_wellord2(X0)) = k2_yellow_1(X0) ),
    inference(definition_unfolding,[],[f122,f118])).

fof(f118,plain,(
    ! [X0] : k1_yellow_1(X0) = k1_wellord2(X0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] : k1_yellow_1(X0) = k1_wellord2(X0) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t25_waybel_7.p',redefinition_k1_yellow_1)).

fof(f122,plain,(
    ! [X0] : g1_orders_2(X0,k1_yellow_1(X0)) = k2_yellow_1(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : g1_orders_2(X0,k1_yellow_1(X0)) = k2_yellow_1(X0) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t25_waybel_7.p',d1_yellow_1)).

fof(f120,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t25_waybel_7.p',t4_yellow_1)).

fof(f159,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t25_waybel_7.p',redefinition_k6_subset_1)).

fof(f164,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X0,X1) = k7_waybel_1(k3_yellow_1(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X0,X1) = k7_waybel_1(k3_yellow_1(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f50])).

fof(f50,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => k6_subset_1(X0,X1) = k7_waybel_1(k3_yellow_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t25_waybel_7.p',t9_waybel_7)).

fof(f2841,plain,(
    ! [X0] : u1_struct_0(g1_orders_2(X0,k1_wellord2(X0))) = X0 ),
    inference(subsumption_resolution,[],[f2835,f199])).

fof(f199,plain,(
    ! [X0] : m1_subset_1(k1_wellord2(X0),k9_setfam_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f132,f118,f117])).

fof(f117,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t25_waybel_7.p',redefinition_k9_setfam_1)).

fof(f132,plain,(
    ! [X0] : m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k1_yellow_1(X0),X0)
      & v8_relat_2(k1_yellow_1(X0))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t25_waybel_7.p',dt_k1_yellow_1)).

fof(f2835,plain,(
    ! [X0] :
      ( u1_struct_0(g1_orders_2(X0,k1_wellord2(X0))) = X0
      | ~ m1_subset_1(k1_wellord2(X0),k9_setfam_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(equality_resolution,[],[f888])).

fof(f888,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(X1,X2) != g1_orders_2(X0,k1_wellord2(X0))
      | u1_struct_0(g1_orders_2(X0,k1_wellord2(X0))) = X1
      | ~ m1_subset_1(X2,k9_setfam_1(k2_zfmisc_1(X1,X1))) ) ),
    inference(superposition,[],[f220,f409])).

fof(f409,plain,(
    ! [X0] : g1_orders_2(X0,k1_wellord2(X0)) = g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_wellord2(X0))),u1_orders_2(g1_orders_2(X0,k1_wellord2(X0)))) ),
    inference(subsumption_resolution,[],[f407,f206])).

fof(f206,plain,(
    ! [X0] : l1_orders_2(g1_orders_2(X0,k1_wellord2(X0))) ),
    inference(definition_unfolding,[],[f136,f184])).

fof(f136,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t25_waybel_7.p',dt_k2_yellow_1)).

fof(f407,plain,(
    ! [X0] :
      ( g1_orders_2(X0,k1_wellord2(X0)) = g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_wellord2(X0))),u1_orders_2(g1_orders_2(X0,k1_wellord2(X0))))
      | ~ l1_orders_2(g1_orders_2(X0,k1_wellord2(X0))) ) ),
    inference(resolution,[],[f142,f207])).

fof(f207,plain,(
    ! [X0] : v1_orders_2(g1_orders_2(X0,k1_wellord2(X0))) ),
    inference(definition_unfolding,[],[f135,f184])).

fof(f135,plain,(
    ! [X0] : v1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f142,plain,(
    ! [X0] :
      ( ~ v1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
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
    file('/export/starexec/sandbox/benchmark/waybel_7__t25_waybel_7.p',abstractness_v1_orders_2)).

fof(f220,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k9_setfam_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(definition_unfolding,[],[f167,f117])).

fof(f167,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t25_waybel_7.p',free_g1_orders_2)).

fof(f15092,plain,
    ( ! [X0] :
        ( r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),X0),sK1)
        | ~ m1_subset_1(X0,k9_setfam_1(sK0))
        | r2_hidden(X0,sK1) )
    | ~ spl7_1626 ),
    inference(avatar_component_clause,[],[f15091])).

fof(f15091,plain,
    ( spl7_1626
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k9_setfam_1(sK0))
        | r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),X0),sK1)
        | r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1626])])).

fof(f15151,plain,(
    spl7_1625 ),
    inference(avatar_contradiction_clause,[],[f15150])).

fof(f15150,plain,
    ( $false
    | ~ spl7_1625 ),
    inference(subsumption_resolution,[],[f15149,f206])).

fof(f15149,plain,
    ( ~ l1_orders_2(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
    | ~ spl7_1625 ),
    inference(subsumption_resolution,[],[f15148,f198])).

fof(f198,plain,(
    ! [X0] : ~ v2_struct_0(g1_orders_2(k9_setfam_1(X0),k1_wellord2(k9_setfam_1(X0)))) ),
    inference(definition_unfolding,[],[f123,f185])).

fof(f123,plain,(
    ! [X0] : ~ v2_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,axiom,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t25_waybel_7.p',fc7_yellow_1)).

fof(f15148,plain,
    ( v2_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
    | ~ l1_orders_2(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
    | ~ spl7_1625 ),
    inference(subsumption_resolution,[],[f15147,f204])).

fof(f204,plain,(
    ! [X0] : v11_waybel_1(g1_orders_2(k9_setfam_1(X0),k1_wellord2(k9_setfam_1(X0)))) ),
    inference(definition_unfolding,[],[f134,f185])).

fof(f134,plain,(
    ! [X0] : v11_waybel_1(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,axiom,(
    ! [X0] :
      ( v11_waybel_1(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t25_waybel_7.p',fc1_waybel_7)).

fof(f15147,plain,
    ( ~ v11_waybel_1(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
    | v2_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
    | ~ l1_orders_2(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
    | ~ spl7_1625 ),
    inference(resolution,[],[f15089,f148])).

fof(f148,plain,(
    ! [X0] :
      ( v2_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ( v10_waybel_1(X0)
        & v2_waybel_1(X0)
        & v3_yellow_0(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ( v10_waybel_1(X0)
        & v2_waybel_1(X0)
        & v3_yellow_0(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f51])).

fof(f51,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v10_waybel_1(X0)
          & v2_waybel_1(X0)
          & v3_yellow_0(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t25_waybel_7.p',cc8_waybel_1)).

fof(f15089,plain,
    ( ~ v2_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
    | ~ spl7_1625 ),
    inference(avatar_component_clause,[],[f15088])).

fof(f15088,plain,
    ( spl7_1625
  <=> ~ v2_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1625])])).

fof(f15146,plain,(
    spl7_1623 ),
    inference(avatar_contradiction_clause,[],[f15145])).

fof(f15145,plain,
    ( $false
    | ~ spl7_1623 ),
    inference(subsumption_resolution,[],[f15144,f206])).

fof(f15144,plain,
    ( ~ l1_orders_2(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
    | ~ spl7_1623 ),
    inference(subsumption_resolution,[],[f15143,f198])).

fof(f15143,plain,
    ( v2_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
    | ~ l1_orders_2(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
    | ~ spl7_1623 ),
    inference(subsumption_resolution,[],[f15142,f204])).

fof(f15142,plain,
    ( ~ v11_waybel_1(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
    | v2_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
    | ~ l1_orders_2(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
    | ~ spl7_1623 ),
    inference(resolution,[],[f15083,f147])).

fof(f147,plain,(
    ! [X0] :
      ( v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f15083,plain,
    ( ~ v1_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
    | ~ spl7_1623 ),
    inference(avatar_component_clause,[],[f15082])).

fof(f15082,plain,
    ( spl7_1623
  <=> ~ v1_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1623])])).

fof(f15093,plain,
    ( ~ spl7_1623
    | ~ spl7_1625
    | spl7_1626
    | ~ spl7_0 ),
    inference(avatar_split_clause,[],[f15077,f229,f15091,f15088,f15082])).

fof(f229,plain,
    ( spl7_0
  <=> v2_waybel_7(sK1,g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f15077,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k9_setfam_1(sK0))
        | r2_hidden(X0,sK1)
        | r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),X0),sK1)
        | ~ v2_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v1_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))) )
    | ~ spl7_0 ),
    inference(subsumption_resolution,[],[f15076,f2842])).

fof(f2842,plain,(
    m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0))) ),
    inference(backward_demodulation,[],[f2841,f190])).

fof(f190,plain,(
    m1_subset_1(sK1,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))))) ),
    inference(definition_unfolding,[],[f109,f117,f185])).

fof(f109,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,
    ( ( ( ~ r2_hidden(k6_subset_1(sK0,sK2),sK1)
        & ~ r2_hidden(sK2,sK1)
        & m1_subset_1(sK2,k1_zfmisc_1(sK0)) )
      | ~ v2_waybel_7(sK1,k3_yellow_1(sK0)) )
    & ( ! [X3] :
          ( r2_hidden(k6_subset_1(sK0,X3),sK1)
          | r2_hidden(X3,sK1)
          | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) )
      | v2_waybel_7(sK1,k3_yellow_1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    & v13_waybel_0(sK1,k3_yellow_1(sK0))
    & v2_waybel_0(sK1,k3_yellow_1(sK0))
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f91,f93,f92])).

fof(f92,plain,
    ( ? [X0,X1] :
        ( ( ? [X2] :
              ( ~ r2_hidden(k6_subset_1(X0,X2),X1)
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(X0)) )
          | ~ v2_waybel_7(X1,k3_yellow_1(X0)) )
        & ( ! [X3] :
              ( r2_hidden(k6_subset_1(X0,X3),X1)
              | r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          | v2_waybel_7(X1,k3_yellow_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        & v13_waybel_0(X1,k3_yellow_1(X0))
        & v2_waybel_0(X1,k3_yellow_1(X0))
        & ~ v1_xboole_0(X1) )
   => ( ( ? [X2] :
            ( ~ r2_hidden(k6_subset_1(sK0,X2),sK1)
            & ~ r2_hidden(X2,sK1)
            & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
        | ~ v2_waybel_7(sK1,k3_yellow_1(sK0)) )
      & ( ! [X3] :
            ( r2_hidden(k6_subset_1(sK0,X3),sK1)
            | r2_hidden(X3,sK1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) )
        | v2_waybel_7(sK1,k3_yellow_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
      & v13_waybel_0(sK1,k3_yellow_1(sK0))
      & v2_waybel_0(sK1,k3_yellow_1(sK0))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k6_subset_1(X0,X2),X1)
          & ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ~ r2_hidden(k6_subset_1(X0,sK2),X1)
        & ~ r2_hidden(sK2,X1)
        & m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f91,plain,(
    ? [X0,X1] :
      ( ( ? [X2] :
            ( ~ r2_hidden(k6_subset_1(X0,X2),X1)
            & ~ r2_hidden(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        | ~ v2_waybel_7(X1,k3_yellow_1(X0)) )
      & ( ! [X3] :
            ( r2_hidden(k6_subset_1(X0,X3),X1)
            | r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
        | v2_waybel_7(X1,k3_yellow_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0))
      & v2_waybel_0(X1,k3_yellow_1(X0))
      & ~ v1_xboole_0(X1) ) ),
    inference(rectify,[],[f90])).

fof(f90,plain,(
    ? [X0,X1] :
      ( ( ? [X2] :
            ( ~ r2_hidden(k6_subset_1(X0,X2),X1)
            & ~ r2_hidden(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        | ~ v2_waybel_7(X1,k3_yellow_1(X0)) )
      & ( ! [X2] :
            ( r2_hidden(k6_subset_1(X0,X2),X1)
            | r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
        | v2_waybel_7(X1,k3_yellow_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0))
      & v2_waybel_0(X1,k3_yellow_1(X0))
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f89])).

fof(f89,plain,(
    ? [X0,X1] :
      ( ( ? [X2] :
            ( ~ r2_hidden(k6_subset_1(X0,X2),X1)
            & ~ r2_hidden(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        | ~ v2_waybel_7(X1,k3_yellow_1(X0)) )
      & ( ! [X2] :
            ( r2_hidden(k6_subset_1(X0,X2),X1)
            | r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
        | v2_waybel_7(X1,k3_yellow_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0))
      & v2_waybel_0(X1,k3_yellow_1(X0))
      & ~ v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f55,plain,(
    ? [X0,X1] :
      ( ( v2_waybel_7(X1,k3_yellow_1(X0))
      <~> ! [X2] :
            ( r2_hidden(k6_subset_1(X0,X2),X1)
            | r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0))
      & v2_waybel_0(X1,k3_yellow_1(X0))
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ? [X0,X1] :
      ( ( v2_waybel_7(X1,k3_yellow_1(X0))
      <~> ! [X2] :
            ( r2_hidden(k6_subset_1(X0,X2),X1)
            | r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0))
      & v2_waybel_0(X1,k3_yellow_1(X0))
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0))
          & v2_waybel_0(X1,k3_yellow_1(X0))
          & ~ v1_xboole_0(X1) )
       => ( v2_waybel_7(X1,k3_yellow_1(X0))
        <=> ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(X0))
             => ( r2_hidden(k6_subset_1(X0,X2),X1)
                | r2_hidden(X2,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        & v13_waybel_0(X1,k3_yellow_1(X0))
        & v2_waybel_0(X1,k3_yellow_1(X0))
        & ~ v1_xboole_0(X1) )
     => ( v2_waybel_7(X1,k3_yellow_1(X0))
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r2_hidden(k6_subset_1(X0,X2),X1)
              | r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t25_waybel_7.p',t25_waybel_7)).

fof(f15076,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0)))
        | ~ m1_subset_1(X0,k9_setfam_1(sK0))
        | r2_hidden(X0,sK1)
        | r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),X0),sK1)
        | ~ v2_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v1_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))) )
    | ~ spl7_0 ),
    inference(forward_demodulation,[],[f15075,f2841])).

fof(f15075,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k9_setfam_1(sK0))
        | r2_hidden(X0,sK1)
        | r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),X0),sK1)
        | ~ m1_subset_1(sK1,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))))
        | ~ v2_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v1_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))) )
    | ~ spl7_0 ),
    inference(forward_demodulation,[],[f15074,f2841])).

fof(f15074,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))))
        | r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),X0),sK1)
        | ~ m1_subset_1(sK1,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))))
        | ~ v2_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v1_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))) )
    | ~ spl7_0 ),
    inference(subsumption_resolution,[],[f15073,f196])).

fof(f196,plain,(
    ! [X0] : v3_orders_2(g1_orders_2(k9_setfam_1(X0),k1_wellord2(k9_setfam_1(X0)))) ),
    inference(definition_unfolding,[],[f125,f185])).

fof(f125,plain,(
    ! [X0] : v3_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

fof(f15073,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))))
        | r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),X0),sK1)
        | ~ m1_subset_1(sK1,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))))
        | ~ v2_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v1_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v3_orders_2(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))) )
    | ~ spl7_0 ),
    inference(subsumption_resolution,[],[f15072,f195])).

fof(f195,plain,(
    ! [X0] : v4_orders_2(g1_orders_2(k9_setfam_1(X0),k1_wellord2(k9_setfam_1(X0)))) ),
    inference(definition_unfolding,[],[f126,f185])).

fof(f126,plain,(
    ! [X0] : v4_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

fof(f15072,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))))
        | r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),X0),sK1)
        | ~ m1_subset_1(sK1,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))))
        | ~ v2_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v1_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v4_orders_2(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v3_orders_2(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))) )
    | ~ spl7_0 ),
    inference(subsumption_resolution,[],[f15071,f194])).

fof(f194,plain,(
    ! [X0] : v5_orders_2(g1_orders_2(k9_setfam_1(X0),k1_wellord2(k9_setfam_1(X0)))) ),
    inference(definition_unfolding,[],[f127,f185])).

fof(f127,plain,(
    ! [X0] : v5_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

fof(f15071,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))))
        | r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),X0),sK1)
        | ~ m1_subset_1(sK1,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))))
        | ~ v2_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v1_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v5_orders_2(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v4_orders_2(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v3_orders_2(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))) )
    | ~ spl7_0 ),
    inference(subsumption_resolution,[],[f15070,f204])).

fof(f15070,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))))
        | r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),X0),sK1)
        | ~ m1_subset_1(sK1,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))))
        | ~ v2_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v1_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v11_waybel_1(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v5_orders_2(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v4_orders_2(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v3_orders_2(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))) )
    | ~ spl7_0 ),
    inference(subsumption_resolution,[],[f15069,f206])).

fof(f15069,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))))
        | r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),X0),sK1)
        | ~ m1_subset_1(sK1,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))))
        | ~ l1_orders_2(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v2_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v1_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v11_waybel_1(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v5_orders_2(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v4_orders_2(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v3_orders_2(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))) )
    | ~ spl7_0 ),
    inference(subsumption_resolution,[],[f15068,f106])).

fof(f106,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f94])).

fof(f15068,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))))
        | r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),X0),sK1)
        | ~ m1_subset_1(sK1,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))))
        | v1_xboole_0(sK1)
        | ~ l1_orders_2(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v2_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v1_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v11_waybel_1(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v5_orders_2(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v4_orders_2(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v3_orders_2(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))) )
    | ~ spl7_0 ),
    inference(subsumption_resolution,[],[f15067,f192])).

fof(f192,plain,(
    v2_waybel_0(sK1,g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))) ),
    inference(definition_unfolding,[],[f107,f185])).

fof(f107,plain,(
    v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f94])).

fof(f15067,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))))
        | r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),X0),sK1)
        | ~ m1_subset_1(sK1,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))))
        | ~ v2_waybel_0(sK1,g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | v1_xboole_0(sK1)
        | ~ l1_orders_2(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v2_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v1_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v11_waybel_1(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v5_orders_2(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v4_orders_2(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v3_orders_2(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))) )
    | ~ spl7_0 ),
    inference(subsumption_resolution,[],[f15066,f191])).

fof(f191,plain,(
    v13_waybel_0(sK1,g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))) ),
    inference(definition_unfolding,[],[f108,f185])).

fof(f108,plain,(
    v13_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f94])).

fof(f15066,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))))
        | r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),X0),sK1)
        | ~ m1_subset_1(sK1,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))))
        | ~ v13_waybel_0(sK1,g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v2_waybel_0(sK1,g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | v1_xboole_0(sK1)
        | ~ l1_orders_2(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v2_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v1_lattice3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v11_waybel_1(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v5_orders_2(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v4_orders_2(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
        | ~ v3_orders_2(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))) )
    | ~ spl7_0 ),
    inference(resolution,[],[f230,f214])).

fof(f214,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_waybel_7(X1,X0)
      | r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r2_hidden(k7_waybel_1(X0,X3),X1)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(definition_unfolding,[],[f153,f117])).

fof(f153,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k7_waybel_1(X0,X3),X1)
      | r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v2_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              | ( ~ r2_hidden(k7_waybel_1(X0,sK3(X0,X1)),X1)
                & ~ r2_hidden(sK3(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k7_waybel_1(X0,X3),X1)
                  | r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ v2_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f96,f97])).

fof(f97,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k7_waybel_1(X0,X2),X1)
          & ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r2_hidden(k7_waybel_1(X0,sK3(X0,X1)),X1)
        & ~ r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f96,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k7_waybel_1(X0,X2),X1)
                  & ~ r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k7_waybel_1(X0,X3),X1)
                  | r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ v2_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f95])).

fof(f95,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k7_waybel_1(X0,X2),X1)
                  & ~ r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( r2_hidden(k7_waybel_1(X0,X2),X1)
                  | r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v2_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k7_waybel_1(X0,X2),X1)
                | r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k7_waybel_1(X0,X2),X1)
                | r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v11_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(k7_waybel_1(X0,X2),X1)
                  | r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t25_waybel_7.p',t24_waybel_7)).

fof(f230,plain,
    ( v2_waybel_7(sK1,g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f229])).

fof(f14786,plain,
    ( spl7_1
    | ~ spl7_976
    | ~ spl7_1040 ),
    inference(avatar_contradiction_clause,[],[f14785])).

fof(f14785,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_976
    | ~ spl7_1040 ),
    inference(subsumption_resolution,[],[f14784,f9419])).

fof(f9419,plain,
    ( m1_subset_1(sK3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),sK1),k9_setfam_1(sK0))
    | ~ spl7_976 ),
    inference(avatar_component_clause,[],[f9418])).

fof(f9418,plain,
    ( spl7_976
  <=> m1_subset_1(sK3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),sK1),k9_setfam_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_976])])).

fof(f14784,plain,
    ( ~ m1_subset_1(sK3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),sK1),k9_setfam_1(sK0))
    | ~ spl7_1
    | ~ spl7_1040 ),
    inference(subsumption_resolution,[],[f14757,f10136])).

fof(f10136,plain,
    ( r2_hidden(k4_xboole_0(sK0,sK3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),sK1)),sK1)
    | ~ spl7_1040 ),
    inference(avatar_component_clause,[],[f10135])).

fof(f10135,plain,
    ( spl7_1040
  <=> r2_hidden(k4_xboole_0(sK0,sK3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1040])])).

fof(f14757,plain,
    ( ~ r2_hidden(k4_xboole_0(sK0,sK3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),sK1)),sK1)
    | ~ m1_subset_1(sK3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),sK1),k9_setfam_1(sK0))
    | ~ spl7_1 ),
    inference(superposition,[],[f12447,f2908])).

fof(f12447,plain,
    ( ~ r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),sK3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),sK1)),sK1)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f12446,f233])).

fof(f233,plain,
    ( ~ v2_waybel_7(sK1,g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl7_1
  <=> ~ v2_waybel_7(sK1,g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f12446,plain,
    ( v2_waybel_7(sK1,g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
    | ~ r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),sK3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),sK1)),sK1) ),
    inference(subsumption_resolution,[],[f12445,f192])).

fof(f12445,plain,
    ( ~ v2_waybel_0(sK1,g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
    | v2_waybel_7(sK1,g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
    | ~ r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),sK3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),sK1)),sK1) ),
    inference(subsumption_resolution,[],[f12444,f2842])).

fof(f12444,plain,
    ( ~ m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0)))
    | ~ v2_waybel_0(sK1,g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
    | v2_waybel_7(sK1,g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
    | ~ r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),sK3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),sK1)),sK1) ),
    inference(resolution,[],[f4173,f191])).

fof(f4173,plain,(
    ! [X0,X1] :
      ( ~ v13_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | ~ m1_subset_1(X0,k9_setfam_1(k9_setfam_1(X1)))
      | ~ v2_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | v2_waybel_7(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | ~ r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))),sK3(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))),X0)),X0) ) ),
    inference(forward_demodulation,[],[f4172,f2841])).

fof(f4172,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))))
      | ~ v13_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | ~ v2_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | v2_waybel_7(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | ~ r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))),sK3(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))),X0)),X0) ) ),
    inference(subsumption_resolution,[],[f4171,f198])).

fof(f4171,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))))
      | ~ v13_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | ~ v2_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | v2_waybel_7(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | ~ r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))),sK3(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))),X0)),X0)
      | v2_struct_0(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1)))) ) ),
    inference(subsumption_resolution,[],[f4170,f206])).

fof(f4170,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))))
      | ~ v13_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | ~ v2_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | ~ l1_orders_2(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | v2_waybel_7(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | ~ r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))),sK3(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))),X0)),X0)
      | v2_struct_0(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1)))) ) ),
    inference(resolution,[],[f2643,f204])).

fof(f2643,plain,(
    ! [X0,X1] :
      ( ~ v11_waybel_1(X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_waybel_7(X1,X0)
      | ~ r2_hidden(k7_waybel_1(X0,sK3(X0,X1)),X1)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f2642,f147])).

fof(f2642,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k7_waybel_1(X0,sK3(X0,X1)),X1)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_waybel_7(X1,X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f2641,f146])).

fof(f146,plain,(
    ! [X0] :
      ( v5_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f2641,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k7_waybel_1(X0,sK3(X0,X1)),X1)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_waybel_7(X1,X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f2640,f145])).

fof(f145,plain,(
    ! [X0] :
      ( v4_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f2640,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k7_waybel_1(X0,sK3(X0,X1)),X1)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_waybel_7(X1,X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f2639,f144])).

fof(f144,plain,(
    ! [X0] :
      ( v3_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f2639,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k7_waybel_1(X0,sK3(X0,X1)),X1)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_waybel_7(X1,X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f2638])).

fof(f2638,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k7_waybel_1(X0,sK3(X0,X1)),X1)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_waybel_7(X1,X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f2454,f148])).

fof(f2454,plain,(
    ! [X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ r2_hidden(k7_waybel_1(X0,sK3(X0,X1)),X1)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_waybel_7(X1,X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f211,f176])).

fof(f176,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f48])).

fof(f48,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t25_waybel_7.p',t7_boole)).

fof(f211,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | ~ r2_hidden(k7_waybel_1(X0,sK3(X0,X1)),X1)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(definition_unfolding,[],[f156,f117])).

fof(f156,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | ~ r2_hidden(k7_waybel_1(X0,sK3(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f10214,plain,
    ( spl7_1040
    | ~ spl7_977
    | ~ spl7_8
    | spl7_1043 ),
    inference(avatar_split_clause,[],[f10213,f10143,f256,f9415,f10135])).

fof(f9415,plain,
    ( spl7_977
  <=> ~ m1_subset_1(sK3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),sK1),k9_setfam_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_977])])).

fof(f256,plain,
    ( spl7_8
  <=> ! [X3] :
        ( r2_hidden(k4_xboole_0(sK0,X3),sK1)
        | ~ m1_subset_1(X3,k9_setfam_1(sK0))
        | r2_hidden(X3,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f10143,plain,
    ( spl7_1043
  <=> ~ m1_subset_1(sK3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1043])])).

fof(f10213,plain,
    ( ~ m1_subset_1(sK3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),sK1),k9_setfam_1(sK0))
    | r2_hidden(k4_xboole_0(sK0,sK3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),sK1)),sK1)
    | ~ spl7_8
    | ~ spl7_1043 ),
    inference(resolution,[],[f10144,f281])).

fof(f281,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,sK1)
        | ~ m1_subset_1(X0,k9_setfam_1(sK0))
        | r2_hidden(k4_xboole_0(sK0,X0),sK1) )
    | ~ spl7_8 ),
    inference(resolution,[],[f162,f257])).

fof(f257,plain,
    ( ! [X3] :
        ( r2_hidden(X3,sK1)
        | ~ m1_subset_1(X3,k9_setfam_1(sK0))
        | r2_hidden(k4_xboole_0(sK0,X3),sK1) )
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f256])).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t25_waybel_7.p',t1_subset)).

fof(f10144,plain,
    ( ~ m1_subset_1(sK3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),sK1),sK1)
    | ~ spl7_1043 ),
    inference(avatar_component_clause,[],[f10143])).

fof(f10147,plain,
    ( spl7_278
    | ~ spl7_1043
    | spl7_979 ),
    inference(avatar_split_clause,[],[f10127,f9427,f10143,f3017])).

fof(f3017,plain,
    ( spl7_278
  <=> ! [X16] : o_0_0_xboole_0 = k4_xboole_0(sK1,X16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_278])])).

fof(f9427,plain,
    ( spl7_979
  <=> ~ r2_hidden(sK3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_979])])).

fof(f10127,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(sK3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),sK1),sK1)
        | o_0_0_xboole_0 = k4_xboole_0(sK1,X4) )
    | ~ spl7_979 ),
    inference(resolution,[],[f9428,f1320])).

fof(f1320,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1)
      | o_0_0_xboole_0 = k4_xboole_0(X1,X2) ) ),
    inference(resolution,[],[f900,f157])).

fof(f157,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f100])).

fof(f100,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f99])).

fof(f99,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t25_waybel_7.p',existence_m1_subset_1)).

fof(f900,plain,(
    ! [X21,X19,X20,X18] :
      ( ~ m1_subset_1(X20,k4_xboole_0(X19,X21))
      | ~ m1_subset_1(X18,X19)
      | r2_hidden(X18,X19)
      | o_0_0_xboole_0 = k4_xboole_0(X19,X21) ) ),
    inference(resolution,[],[f506,f215])).

fof(f215,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k9_setfam_1(X0)) ),
    inference(definition_unfolding,[],[f158,f159,f117])).

fof(f158,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t25_waybel_7.p',dt_k6_subset_1)).

fof(f506,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k9_setfam_1(X1))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,X1)
      | ~ m1_subset_1(X3,X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(resolution,[],[f294,f287])).

fof(f287,plain,(
    ! [X4,X5] :
      ( r2_hidden(X4,X5)
      | ~ m1_subset_1(X4,X5)
      | o_0_0_xboole_0 = X5 ) ),
    inference(resolution,[],[f163,f260])).

fof(f260,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(backward_demodulation,[],[f259,f152])).

fof(f152,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t25_waybel_7.p',t6_boole)).

fof(f259,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[],[f152,f114])).

fof(f114,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t25_waybel_7.p',dt_o_0_0_xboole_0)).

fof(f163,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t25_waybel_7.p',t2_subset)).

fof(f294,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X2,k9_setfam_1(X3))
      | r2_hidden(X5,X3)
      | ~ m1_subset_1(X5,X3) ) ),
    inference(resolution,[],[f225,f163])).

fof(f225,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k9_setfam_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f179,f117])).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f46,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t25_waybel_7.p',t5_subset)).

fof(f9428,plain,
    ( ~ r2_hidden(sK3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),sK1),sK1)
    | ~ spl7_979 ),
    inference(avatar_component_clause,[],[f9427])).

fof(f9429,plain,
    ( ~ spl7_979
    | spl7_0 ),
    inference(avatar_split_clause,[],[f9422,f229,f9427])).

fof(f9422,plain,
    ( v2_waybel_7(sK1,g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
    | ~ r2_hidden(sK3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),sK1),sK1) ),
    inference(global_subsumption,[],[f192,f9421])).

fof(f9421,plain,
    ( ~ v2_waybel_0(sK1,g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
    | v2_waybel_7(sK1,g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
    | ~ r2_hidden(sK3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),sK1),sK1) ),
    inference(subsumption_resolution,[],[f9410,f2842])).

fof(f9410,plain,
    ( ~ m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0)))
    | ~ v2_waybel_0(sK1,g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
    | v2_waybel_7(sK1,g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
    | ~ r2_hidden(sK3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),sK1),sK1) ),
    inference(resolution,[],[f191,f3970])).

fof(f3970,plain,(
    ! [X0,X1] :
      ( ~ v13_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | ~ m1_subset_1(X0,k9_setfam_1(k9_setfam_1(X1)))
      | ~ v2_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | v2_waybel_7(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | ~ r2_hidden(sK3(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))),X0),X0) ) ),
    inference(forward_demodulation,[],[f3969,f2841])).

fof(f3969,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))))
      | ~ v13_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | ~ v2_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | v2_waybel_7(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | ~ r2_hidden(sK3(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))),X0),X0) ) ),
    inference(subsumption_resolution,[],[f3968,f198])).

fof(f3968,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))))
      | ~ v13_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | ~ v2_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | v2_waybel_7(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | ~ r2_hidden(sK3(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))),X0),X0)
      | v2_struct_0(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1)))) ) ),
    inference(subsumption_resolution,[],[f3967,f206])).

fof(f3967,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))))
      | ~ v13_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | ~ v2_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | ~ l1_orders_2(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | v2_waybel_7(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | ~ r2_hidden(sK3(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))),X0),X0)
      | v2_struct_0(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1)))) ) ),
    inference(resolution,[],[f1975,f204])).

fof(f1975,plain,(
    ! [X0,X1] :
      ( ~ v11_waybel_1(X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_waybel_7(X1,X0)
      | ~ r2_hidden(sK3(X0,X1),X1)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f1974,f147])).

fof(f1974,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_waybel_7(X1,X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f1973,f146])).

fof(f1973,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_waybel_7(X1,X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f1972,f145])).

fof(f1972,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_waybel_7(X1,X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f1971,f144])).

fof(f1971,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_waybel_7(X1,X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f1970])).

fof(f1970,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_waybel_7(X1,X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f1810,f148])).

fof(f1810,plain,(
    ! [X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ r2_hidden(sK3(X0,X1),X1)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_waybel_7(X1,X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f212,f176])).

fof(f212,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | ~ r2_hidden(sK3(X0,X1),X1)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(definition_unfolding,[],[f155,f117])).

fof(f155,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | ~ r2_hidden(sK3(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f9420,plain,
    ( spl7_0
    | spl7_976 ),
    inference(avatar_split_clause,[],[f9413,f9418,f229])).

fof(f9413,plain,
    ( m1_subset_1(sK3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),sK1),k9_setfam_1(sK0))
    | v2_waybel_7(sK1,g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))) ),
    inference(global_subsumption,[],[f192,f9412])).

fof(f9412,plain,
    ( m1_subset_1(sK3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),sK1),k9_setfam_1(sK0))
    | ~ v2_waybel_0(sK1,g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
    | v2_waybel_7(sK1,g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))) ),
    inference(subsumption_resolution,[],[f9411,f106])).

fof(f9411,plain,
    ( m1_subset_1(sK3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),sK1),k9_setfam_1(sK0))
    | ~ v2_waybel_0(sK1,g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
    | v1_xboole_0(sK1)
    | v2_waybel_7(sK1,g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))) ),
    inference(subsumption_resolution,[],[f9409,f2842])).

fof(f9409,plain,
    ( ~ m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0)))
    | m1_subset_1(sK3(g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))),sK1),k9_setfam_1(sK0))
    | ~ v2_waybel_0(sK1,g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0))))
    | v1_xboole_0(sK1)
    | v2_waybel_7(sK1,g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))) ),
    inference(resolution,[],[f191,f4377])).

fof(f4377,plain,(
    ! [X0,X1] :
      ( ~ v13_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | ~ m1_subset_1(X0,k9_setfam_1(k9_setfam_1(X1)))
      | m1_subset_1(sK3(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))),X0),k9_setfam_1(X1))
      | ~ v2_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | v1_xboole_0(X0)
      | v2_waybel_7(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1)))) ) ),
    inference(forward_demodulation,[],[f4376,f2841])).

fof(f4376,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k9_setfam_1(k9_setfam_1(X1)))
      | ~ v13_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | ~ v2_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | v1_xboole_0(X0)
      | v2_waybel_7(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | m1_subset_1(sK3(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))),X0),u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))) ) ),
    inference(forward_demodulation,[],[f4375,f2841])).

fof(f4375,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))))
      | ~ v13_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | ~ v2_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | v1_xboole_0(X0)
      | v2_waybel_7(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | m1_subset_1(sK3(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))),X0),u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))) ) ),
    inference(subsumption_resolution,[],[f4374,f198])).

fof(f4374,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))))
      | ~ v13_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | ~ v2_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | v1_xboole_0(X0)
      | v2_waybel_7(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | m1_subset_1(sK3(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))),X0),u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1)))))
      | v2_struct_0(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1)))) ) ),
    inference(subsumption_resolution,[],[f4373,f206])).

fof(f4373,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))))
      | ~ v13_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | ~ v2_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | v1_xboole_0(X0)
      | ~ l1_orders_2(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | v2_waybel_7(X0,g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))))
      | m1_subset_1(sK3(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1))),X0),u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1)))))
      | v2_struct_0(g1_orders_2(k9_setfam_1(X1),k1_wellord2(k9_setfam_1(X1)))) ) ),
    inference(resolution,[],[f2184,f204])).

fof(f2184,plain,(
    ! [X0,X1] :
      ( ~ v11_waybel_1(X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | v2_waybel_7(X1,X0)
      | m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f2183,f147])).

fof(f2183,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | v2_waybel_7(X1,X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f2182,f146])).

fof(f2182,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | v2_waybel_7(X1,X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f2181,f145])).

fof(f2181,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | v2_waybel_7(X1,X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f2180,f144])).

fof(f2180,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | v2_waybel_7(X1,X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f2179])).

fof(f2179,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | v2_waybel_7(X1,X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f213,f148])).

fof(f213,plain,(
    ! [X0,X1] :
      ( ~ v2_lattice3(X0)
      | m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | v2_waybel_7(X1,X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(definition_unfolding,[],[f154,f117])).

fof(f154,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f4746,plain,
    ( spl7_47
    | ~ spl7_278 ),
    inference(avatar_contradiction_clause,[],[f4745])).

fof(f4745,plain,
    ( $false
    | ~ spl7_47
    | ~ spl7_278 ),
    inference(subsumption_resolution,[],[f4728,f436])).

fof(f436,plain,
    ( o_0_0_xboole_0 != sK1
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f435])).

fof(f435,plain,
    ( spl7_47
  <=> o_0_0_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f4728,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl7_278 ),
    inference(superposition,[],[f262,f3018])).

fof(f3018,plain,
    ( ! [X16] : o_0_0_xboole_0 = k4_xboole_0(sK1,X16)
    | ~ spl7_278 ),
    inference(avatar_component_clause,[],[f3017])).

fof(f262,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f259,f116])).

fof(f116,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t25_waybel_7.p',t3_boole)).

fof(f763,plain,(
    ~ spl7_46 ),
    inference(avatar_contradiction_clause,[],[f762])).

fof(f762,plain,
    ( $false
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f742,f283])).

fof(f283,plain,(
    ! [X1] : m1_subset_1(X1,k9_setfam_1(X1)) ),
    inference(superposition,[],[f215,f262])).

fof(f742,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k9_setfam_1(o_0_0_xboole_0))
    | ~ spl7_46 ),
    inference(backward_demodulation,[],[f439,f296])).

fof(f296,plain,(
    ~ m1_subset_1(sK1,k9_setfam_1(o_0_0_xboole_0)) ),
    inference(resolution,[],[f293,f289])).

fof(f289,plain,(
    r2_hidden(sK4(sK1),sK1) ),
    inference(resolution,[],[f285,f157])).

fof(f285,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f163,f106])).

fof(f293,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X0,k9_setfam_1(o_0_0_xboole_0)) ) ),
    inference(resolution,[],[f225,f114])).

fof(f439,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f438])).

fof(f438,plain,
    ( spl7_46
  <=> o_0_0_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f258,plain,
    ( spl7_0
    | spl7_8 ),
    inference(avatar_split_clause,[],[f189,f256,f229])).

fof(f189,plain,(
    ! [X3] :
      ( r2_hidden(k4_xboole_0(sK0,X3),sK1)
      | r2_hidden(X3,sK1)
      | ~ m1_subset_1(X3,k9_setfam_1(sK0))
      | v2_waybel_7(sK1,g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))) ) ),
    inference(definition_unfolding,[],[f110,f159,f117,f185])).

fof(f110,plain,(
    ! [X3] :
      ( r2_hidden(k6_subset_1(sK0,X3),sK1)
      | r2_hidden(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | v2_waybel_7(sK1,k3_yellow_1(sK0)) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f254,plain,
    ( ~ spl7_1
    | spl7_6 ),
    inference(avatar_split_clause,[],[f188,f252,f232])).

fof(f188,plain,
    ( m1_subset_1(sK2,k9_setfam_1(sK0))
    | ~ v2_waybel_7(sK1,g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))) ),
    inference(definition_unfolding,[],[f111,f117,f185])).

fof(f111,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ v2_waybel_7(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f94])).

fof(f247,plain,
    ( ~ spl7_1
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f187,f245,f232])).

fof(f187,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ v2_waybel_7(sK1,g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))) ),
    inference(definition_unfolding,[],[f112,f185])).

fof(f112,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ v2_waybel_7(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f94])).

fof(f240,plain,
    ( ~ spl7_1
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f186,f238,f232])).

fof(f186,plain,
    ( ~ r2_hidden(k4_xboole_0(sK0,sK2),sK1)
    | ~ v2_waybel_7(sK1,g1_orders_2(k9_setfam_1(sK0),k1_wellord2(k9_setfam_1(sK0)))) ),
    inference(definition_unfolding,[],[f113,f159,f185])).

fof(f113,plain,
    ( ~ r2_hidden(k6_subset_1(sK0,sK2),sK1)
    | ~ v2_waybel_7(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f94])).
%------------------------------------------------------------------------------
