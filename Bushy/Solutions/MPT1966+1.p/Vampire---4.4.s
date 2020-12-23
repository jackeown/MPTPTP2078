%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_7__t15_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:03 EDT 2019

% Result     : Theorem 97.88s
% Output     : Refutation 97.88s
% Verified   : 
% Statistics : Number of formulae       :  240 ( 761 expanded)
%              Number of leaves         :   54 ( 290 expanded)
%              Depth                    :   17
%              Number of atoms          : 1024 (3140 expanded)
%              Number of equality atoms :   92 ( 337 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24417,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f214,f221,f242,f255,f271,f283,f419,f563,f886,f1744,f1781,f2019,f2180,f21501,f22532,f22557,f22603,f22634,f22654,f22695,f23226,f23319,f23321,f23463,f23516,f23520,f24415,f24416])).

fof(f24416,plain,
    ( k1_xboole_0 != sK2
    | ~ r1_tarski(sK2,sK1)
    | r1_tarski(k1_xboole_0,sK1) ),
    introduced(theory_axiom,[])).

fof(f24415,plain,
    ( ~ spl8_38
    | ~ spl8_252
    | spl8_325 ),
    inference(avatar_contradiction_clause,[],[f24414])).

fof(f24414,plain,
    ( $false
    | ~ spl8_38
    | ~ spl8_252
    | ~ spl8_325 ),
    inference(subsumption_resolution,[],[f17588,f23534])).

fof(f23534,plain,
    ( k8_setfam_1(sK0,k1_xboole_0) = sK0
    | ~ spl8_38
    | ~ spl8_252 ),
    inference(subsumption_resolution,[],[f2029,f12243])).

fof(f12243,plain,
    ( r1_tarski(k1_xboole_0,sK1)
    | ~ spl8_252 ),
    inference(avatar_component_clause,[],[f12242])).

fof(f12242,plain,
    ( spl8_252
  <=> r1_tarski(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_252])])).

fof(f2029,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | k8_setfam_1(sK0,k1_xboole_0) = sK0
    | ~ spl8_38 ),
    inference(resolution,[],[f567,f397])).

fof(f397,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,u1_struct_0(k3_yellow_1(X0)))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f207,f203])).

fof(f203,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f172,f180])).

fof(f180,plain,(
    ! [X0] : u1_struct_0(k3_yellow_1(X0)) = k1_zfmisc_1(X0) ),
    inference(definition_unfolding,[],[f117,f118])).

fof(f118,plain,(
    ! [X0] : u1_struct_0(k3_yellow_1(X0)) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0] : u1_struct_0(k3_yellow_1(X0)) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t15_waybel_7.p',t4_waybel_7)).

fof(f117,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t15_waybel_7.p',redefinition_k9_setfam_1)).

fof(f172,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t15_waybel_7.p',t3_subset)).

fof(f207,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0)))))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(equality_resolution,[],[f196])).

fof(f196,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0))))) ) ),
    inference(definition_unfolding,[],[f165,f180,f180])).

fof(f165,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t15_waybel_7.p',d10_setfam_1)).

fof(f567,plain,
    ( ! [X0] :
        ( r1_tarski(X0,u1_struct_0(k3_yellow_1(sK0)))
        | ~ r1_tarski(X0,sK1) )
    | ~ spl8_38 ),
    inference(resolution,[],[f562,f175])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f83])).

fof(f83,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t15_waybel_7.p',t1_xboole_1)).

fof(f562,plain,
    ( r1_tarski(sK1,u1_struct_0(k3_yellow_1(sK0)))
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f561])).

fof(f561,plain,
    ( spl8_38
  <=> r1_tarski(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f17588,plain,
    ( k8_setfam_1(sK0,k1_xboole_0) != sK0
    | ~ spl8_325 ),
    inference(avatar_component_clause,[],[f17587])).

fof(f17587,plain,
    ( spl8_325
  <=> k8_setfam_1(sK0,k1_xboole_0) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_325])])).

fof(f23520,plain,
    ( ~ spl8_540
    | spl8_547 ),
    inference(avatar_contradiction_clause,[],[f23519])).

fof(f23519,plain,
    ( $false
    | ~ spl8_540
    | ~ spl8_547 ),
    inference(subsumption_resolution,[],[f23219,f23469])).

fof(f23469,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl8_547 ),
    inference(unit_resulting_resolution,[],[f23309,f149])).

fof(f149,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t15_waybel_7.p',t6_boole)).

fof(f23309,plain,
    ( k1_xboole_0 != sK2
    | ~ spl8_547 ),
    inference(avatar_component_clause,[],[f23308])).

fof(f23308,plain,
    ( spl8_547
  <=> k1_xboole_0 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_547])])).

fof(f23219,plain,
    ( v1_xboole_0(sK2)
    | ~ spl8_540 ),
    inference(avatar_component_clause,[],[f23218])).

fof(f23218,plain,
    ( spl8_540
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_540])])).

fof(f23516,plain,
    ( spl8_1
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_528
    | ~ spl8_542
    | spl8_547
    | spl8_551 ),
    inference(avatar_contradiction_clause,[],[f23515])).

fof(f23515,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_528
    | ~ spl8_542
    | ~ spl8_547
    | ~ spl8_551 ),
    inference(subsumption_resolution,[],[f23514,f23462])).

fof(f23462,plain,
    ( ~ r2_hidden(k1_setfam_1(sK2),sK1)
    | ~ spl8_551 ),
    inference(avatar_component_clause,[],[f23461])).

fof(f23461,plain,
    ( spl8_551
  <=> ~ r2_hidden(k1_setfam_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_551])])).

fof(f23514,plain,
    ( r2_hidden(k1_setfam_1(sK2),sK1)
    | ~ spl8_1
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_528
    | ~ spl8_542
    | ~ spl8_547 ),
    inference(forward_demodulation,[],[f23466,f23225])).

fof(f23225,plain,
    ( k2_yellow_0(k3_yellow_1(sK0),sK2) = k1_setfam_1(sK2)
    | ~ spl8_542 ),
    inference(avatar_component_clause,[],[f23224])).

fof(f23224,plain,
    ( spl8_542
  <=> k2_yellow_0(k3_yellow_1(sK0),sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_542])])).

fof(f23466,plain,
    ( r2_hidden(k2_yellow_0(k3_yellow_1(sK0),sK2),sK1)
    | ~ spl8_1
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_528
    | ~ spl8_547 ),
    inference(unit_resulting_resolution,[],[f254,f213,f241,f245,f22694,f270,f23309,f539])).

fof(f539,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_finset_1(X0)
      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | k1_xboole_0 = X0
      | ~ v2_waybel_0(X1,k3_yellow_1(X2))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X2)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X2))
      | v1_xboole_0(X1)
      | r2_hidden(k2_yellow_0(k3_yellow_1(X2),X0),X1) ) ),
    inference(subsumption_resolution,[],[f538,f122])).

fof(f122,plain,(
    ! [X0] : v3_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t15_waybel_7.p',fc7_yellow_1)).

fof(f538,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ v1_finset_1(X0)
      | ~ v2_waybel_0(X1,k3_yellow_1(X2))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X2)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X2))
      | v1_xboole_0(X1)
      | r2_hidden(k2_yellow_0(k3_yellow_1(X2),X0),X1)
      | ~ v3_orders_2(k3_yellow_1(X2)) ) ),
    inference(subsumption_resolution,[],[f537,f123])).

fof(f123,plain,(
    ! [X0] : v4_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f537,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ v1_finset_1(X0)
      | ~ v2_waybel_0(X1,k3_yellow_1(X2))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X2)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X2))
      | v1_xboole_0(X1)
      | r2_hidden(k2_yellow_0(k3_yellow_1(X2),X0),X1)
      | ~ v4_orders_2(k3_yellow_1(X2))
      | ~ v3_orders_2(k3_yellow_1(X2)) ) ),
    inference(subsumption_resolution,[],[f536,f124])).

fof(f124,plain,(
    ! [X0] : v5_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f536,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ v1_finset_1(X0)
      | ~ v2_waybel_0(X1,k3_yellow_1(X2))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X2)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X2))
      | v1_xboole_0(X1)
      | r2_hidden(k2_yellow_0(k3_yellow_1(X2),X0),X1)
      | ~ v5_orders_2(k3_yellow_1(X2))
      | ~ v4_orders_2(k3_yellow_1(X2))
      | ~ v3_orders_2(k3_yellow_1(X2)) ) ),
    inference(subsumption_resolution,[],[f533,f128])).

fof(f128,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t15_waybel_7.p',dt_k3_yellow_1)).

fof(f533,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ v1_finset_1(X0)
      | ~ v2_waybel_0(X1,k3_yellow_1(X2))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X2)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X2))
      | v1_xboole_0(X1)
      | ~ l1_orders_2(k3_yellow_1(X2))
      | r2_hidden(k2_yellow_0(k3_yellow_1(X2),X0),X1)
      | ~ v5_orders_2(k3_yellow_1(X2))
      | ~ v4_orders_2(k3_yellow_1(X2))
      | ~ v3_orders_2(k3_yellow_1(X2)) ) ),
    inference(resolution,[],[f318,f192])).

fof(f192,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_lattice3(X0)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))
      | ~ v1_finset_1(X3)
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | ~ v13_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | r2_hidden(k2_yellow_0(X0,X3),X1)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(definition_unfolding,[],[f151,f180,f180])).

fof(f151,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k2_yellow_0(X0,X3),X1)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X3)
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              | ( ~ r2_hidden(k2_yellow_0(X0,sK4(X0,X1)),X1)
                & k1_xboole_0 != sK4(X0,X1)
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(X1))
                & v1_finset_1(sK4(X0,X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k2_yellow_0(X0,X3),X1)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              | ~ v2_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f97,f98])).

fof(f98,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k2_yellow_0(X0,X2),X1)
          & k1_xboole_0 != X2
          & m1_subset_1(X2,k1_zfmisc_1(X1))
          & v1_finset_1(X2) )
     => ( ~ r2_hidden(k2_yellow_0(X0,sK4(X0,X1)),X1)
        & k1_xboole_0 != sK4(X0,X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(X1))
        & v1_finset_1(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f97,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k2_yellow_0(X0,X2),X1)
                  & k1_xboole_0 != X2
                  & m1_subset_1(X2,k1_zfmisc_1(X1))
                  & v1_finset_1(X2) ) )
            & ( ! [X3] :
                  ( r2_hidden(k2_yellow_0(X0,X3),X1)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              | ~ v2_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f96])).

fof(f96,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k2_yellow_0(X0,X2),X1)
                  & k1_xboole_0 != X2
                  & m1_subset_1(X2,k1_zfmisc_1(X1))
                  & v1_finset_1(X2) ) )
            & ( ! [X2] :
                  ( r2_hidden(k2_yellow_0(X0,X2),X1)
                  | k1_xboole_0 = X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X2) )
              | ~ v2_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k2_yellow_0(X0,X2),X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k2_yellow_0(X0,X2),X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
                  & v1_finset_1(X2) )
               => ( k1_xboole_0 != X2
                 => r2_hidden(k2_yellow_0(X0,X2),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t15_waybel_7.p',t43_waybel_0)).

fof(f318,plain,(
    ! [X0] : v2_lattice3(k3_yellow_1(X0)) ),
    inference(unit_resulting_resolution,[],[f128,f120,f126,f145])).

fof(f145,plain,(
    ! [X0] :
      ( ~ v11_waybel_1(X0)
      | v2_lattice3(X0)
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
    inference(ennf_transformation,[],[f45])).

fof(f45,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/waybel_7__t15_waybel_7.p',cc8_waybel_1)).

fof(f126,plain,(
    ! [X0] : v11_waybel_1(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,axiom,(
    ! [X0] :
      ( v11_waybel_1(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t15_waybel_7.p',fc1_waybel_7)).

fof(f120,plain,(
    ! [X0] : ~ v2_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f270,plain,
    ( m1_subset_1(sK1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK0)))))
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl8_16
  <=> m1_subset_1(sK1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f22694,plain,
    ( m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK1)))
    | ~ spl8_528 ),
    inference(avatar_component_clause,[],[f22693])).

fof(f22693,plain,
    ( spl8_528
  <=> m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_528])])).

fof(f245,plain,
    ( v2_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl8_10
  <=> v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f241,plain,
    ( v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl8_8
  <=> v13_waybel_0(sK1,k3_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f213,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl8_1
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f254,plain,
    ( v1_finset_1(sK2)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl8_12
  <=> v1_finset_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f23463,plain,
    ( ~ spl8_551
    | spl8_523
    | ~ spl8_548 ),
    inference(avatar_split_clause,[],[f23323,f23317,f22601,f23461])).

fof(f22601,plain,
    ( spl8_523
  <=> ~ r2_hidden(k8_setfam_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_523])])).

fof(f23317,plain,
    ( spl8_548
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_548])])).

fof(f23323,plain,
    ( ~ r2_hidden(k1_setfam_1(sK2),sK1)
    | ~ spl8_523
    | ~ spl8_548 ),
    inference(backward_demodulation,[],[f23318,f22602])).

fof(f22602,plain,
    ( ~ r2_hidden(k8_setfam_1(sK0,sK2),sK1)
    | ~ spl8_523 ),
    inference(avatar_component_clause,[],[f22601])).

fof(f23318,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl8_548 ),
    inference(avatar_component_clause,[],[f23317])).

fof(f23321,plain,
    ( k1_xboole_0 != sK2
    | k8_setfam_1(sK0,k1_xboole_0) != sK0
    | ~ r2_hidden(sK0,sK1)
    | r2_hidden(k8_setfam_1(sK0,sK2),sK1) ),
    introduced(theory_axiom,[])).

fof(f23319,plain,
    ( spl8_546
    | spl8_548
    | ~ spl8_526 ),
    inference(avatar_split_clause,[],[f22684,f22652,f23317,f23311])).

fof(f23311,plain,
    ( spl8_546
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_546])])).

fof(f22652,plain,
    ( spl8_526
  <=> m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_526])])).

fof(f22684,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl8_526 ),
    inference(forward_demodulation,[],[f22665,f22655])).

fof(f22655,plain,
    ( k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl8_526 ),
    inference(unit_resulting_resolution,[],[f22653,f193])).

fof(f193,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0)))))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(definition_unfolding,[],[f161,f180,f180])).

fof(f161,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t15_waybel_7.p',redefinition_k6_setfam_1)).

fof(f22653,plain,
    ( m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK0)))))
    | ~ spl8_526 ),
    inference(avatar_component_clause,[],[f22652])).

fof(f22665,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2)
    | ~ spl8_526 ),
    inference(resolution,[],[f22653,f197])).

fof(f197,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0)))))
      | k1_xboole_0 = X1
      | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f164,f180,f180])).

fof(f164,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f23226,plain,
    ( spl8_540
    | spl8_542
    | ~ spl8_526 ),
    inference(avatar_split_clause,[],[f22666,f22652,f23224,f23218])).

fof(f22666,plain,
    ( k2_yellow_0(k3_yellow_1(sK0),sK2) = k1_setfam_1(sK2)
    | v1_xboole_0(sK2)
    | ~ spl8_526 ),
    inference(resolution,[],[f22653,f202])).

fof(f202,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0)))))
      | k2_yellow_0(k3_yellow_1(X0),X1) = k1_setfam_1(X1)
      | v1_xboole_0(X1) ) ),
    inference(definition_unfolding,[],[f170,f180])).

fof(f170,plain,(
    ! [X0,X1] :
      ( k2_yellow_0(k3_yellow_1(X0),X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k2_yellow_0(k3_yellow_1(X0),X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k2_yellow_0(k3_yellow_1(X0),X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        & ~ v1_xboole_0(X1) )
     => k2_yellow_0(k3_yellow_1(X0),X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t15_waybel_7.p',t20_yellow_1)).

fof(f22695,plain,
    ( spl8_528
    | ~ spl8_520 ),
    inference(avatar_split_clause,[],[f22594,f22555,f22693])).

fof(f22555,plain,
    ( spl8_520
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_520])])).

fof(f22594,plain,
    ( m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK1)))
    | ~ spl8_520 ),
    inference(unit_resulting_resolution,[],[f22556,f203])).

fof(f22556,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl8_520 ),
    inference(avatar_component_clause,[],[f22555])).

fof(f22654,plain,
    ( ~ spl8_11
    | spl8_526 ),
    inference(avatar_split_clause,[],[f181,f22652,f247])).

fof(f247,plain,
    ( spl8_11
  <=> ~ v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f181,plain,
    ( m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK0)))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(definition_unfolding,[],[f112,f180,f180])).

fof(f112,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,
    ( ( ( ~ r2_hidden(k8_setfam_1(sK0,sK2),sK1)
        & r1_tarski(sK2,sK1)
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        & v1_finset_1(sK2) )
      | ~ v2_waybel_0(sK1,k3_yellow_1(sK0)) )
    & ( ! [X3] :
          ( r2_hidden(k8_setfam_1(sK0,X3),sK1)
          | ~ r1_tarski(X3,sK1)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0)))
          | ~ v1_finset_1(X3) )
      | v2_waybel_0(sK1,k3_yellow_1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    & v13_waybel_0(sK1,k3_yellow_1(sK0))
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f90,f92,f91])).

fof(f91,plain,
    ( ? [X0,X1] :
        ( ( ? [X2] :
              ( ~ r2_hidden(k8_setfam_1(X0,X2),X1)
              & r1_tarski(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v1_finset_1(X2) )
          | ~ v2_waybel_0(X1,k3_yellow_1(X0)) )
        & ( ! [X3] :
              ( r2_hidden(k8_setfam_1(X0,X3),X1)
              | ~ r1_tarski(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
              | ~ v1_finset_1(X3) )
          | v2_waybel_0(X1,k3_yellow_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        & v13_waybel_0(X1,k3_yellow_1(X0))
        & ~ v1_xboole_0(X1) )
   => ( ( ? [X2] :
            ( ~ r2_hidden(k8_setfam_1(sK0,X2),sK1)
            & r1_tarski(X2,sK1)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
            & v1_finset_1(X2) )
        | ~ v2_waybel_0(sK1,k3_yellow_1(sK0)) )
      & ( ! [X3] :
            ( r2_hidden(k8_setfam_1(sK0,X3),sK1)
            | ~ r1_tarski(X3,sK1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0)))
            | ~ v1_finset_1(X3) )
        | v2_waybel_0(sK1,k3_yellow_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
      & v13_waybel_0(sK1,k3_yellow_1(sK0))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k8_setfam_1(X0,X2),X1)
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
          & v1_finset_1(X2) )
     => ( ~ r2_hidden(k8_setfam_1(X0,sK2),X1)
        & r1_tarski(sK2,X1)
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X0)))
        & v1_finset_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f90,plain,(
    ? [X0,X1] :
      ( ( ? [X2] :
            ( ~ r2_hidden(k8_setfam_1(X0,X2),X1)
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
            & v1_finset_1(X2) )
        | ~ v2_waybel_0(X1,k3_yellow_1(X0)) )
      & ( ! [X3] :
            ( r2_hidden(k8_setfam_1(X0,X3),X1)
            | ~ r1_tarski(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
            | ~ v1_finset_1(X3) )
        | v2_waybel_0(X1,k3_yellow_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0))
      & ~ v1_xboole_0(X1) ) ),
    inference(rectify,[],[f89])).

fof(f89,plain,(
    ? [X0,X1] :
      ( ( ? [X2] :
            ( ~ r2_hidden(k8_setfam_1(X0,X2),X1)
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
            & v1_finset_1(X2) )
        | ~ v2_waybel_0(X1,k3_yellow_1(X0)) )
      & ( ! [X2] :
            ( r2_hidden(k8_setfam_1(X0,X2),X1)
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
            | ~ v1_finset_1(X2) )
        | v2_waybel_0(X1,k3_yellow_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0))
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f88])).

fof(f88,plain,(
    ? [X0,X1] :
      ( ( ? [X2] :
            ( ~ r2_hidden(k8_setfam_1(X0,X2),X1)
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
            & v1_finset_1(X2) )
        | ~ v2_waybel_0(X1,k3_yellow_1(X0)) )
      & ( ! [X2] :
            ( r2_hidden(k8_setfam_1(X0,X2),X1)
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
            | ~ v1_finset_1(X2) )
        | v2_waybel_0(X1,k3_yellow_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0))
      & ~ v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
    ? [X0,X1] :
      ( ( v2_waybel_0(X1,k3_yellow_1(X0))
      <~> ! [X2] :
            ( r2_hidden(k8_setfam_1(X0,X2),X1)
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
            | ~ v1_finset_1(X2) ) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0))
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ? [X0,X1] :
      ( ( v2_waybel_0(X1,k3_yellow_1(X0))
      <~> ! [X2] :
            ( r2_hidden(k8_setfam_1(X0,X2),X1)
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
            | ~ v1_finset_1(X2) ) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0))
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0))
          & ~ v1_xboole_0(X1) )
       => ( v2_waybel_0(X1,k3_yellow_1(X0))
        <=> ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
                & v1_finset_1(X2) )
             => ( r1_tarski(X2,X1)
               => r2_hidden(k8_setfam_1(X0,X2),X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        & v13_waybel_0(X1,k3_yellow_1(X0))
        & ~ v1_xboole_0(X1) )
     => ( v2_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v1_finset_1(X2) )
           => ( r1_tarski(X2,X1)
             => r2_hidden(k8_setfam_1(X0,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t15_waybel_7.p',t15_waybel_7)).

fof(f22634,plain,
    ( spl8_1
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_16
    | spl8_257 ),
    inference(avatar_contradiction_clause,[],[f22633])).

fof(f22633,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_16
    | ~ spl8_257 ),
    inference(subsumption_resolution,[],[f22632,f12656])).

fof(f12656,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl8_257 ),
    inference(avatar_component_clause,[],[f12655])).

fof(f12655,plain,
    ( spl8_257
  <=> ~ r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_257])])).

fof(f22632,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl8_1
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_16 ),
    inference(forward_demodulation,[],[f22631,f116])).

fof(f116,plain,(
    ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t15_waybel_7.p',t19_yellow_1)).

fof(f22631,plain,
    ( r2_hidden(k4_yellow_0(k3_yellow_1(sK0)),sK1)
    | ~ spl8_1
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f213,f120,f122,f123,f124,f523,f128,f241,f270,f245,f187])).

fof(f187,plain,(
    ! [X0,X1] :
      ( ~ v2_yellow_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | r2_hidden(k4_yellow_0(X0),X1)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f150,f180])).

fof(f150,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(k4_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(k4_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => r2_hidden(k4_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t15_waybel_7.p',t22_waybel_4)).

fof(f523,plain,(
    ! [X0] : v2_yellow_0(k3_yellow_1(X0)) ),
    inference(unit_resulting_resolution,[],[f128,f120,f301,f137])).

fof(f137,plain,(
    ! [X0] :
      ( ~ v9_waybel_1(X0)
      | v2_yellow_0(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v9_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v9_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v9_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_yellow_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t15_waybel_7.p',cc7_waybel_1)).

fof(f301,plain,(
    ! [X0] : v9_waybel_1(k3_yellow_1(X0)) ),
    inference(unit_resulting_resolution,[],[f128,f120,f126,f139])).

fof(f139,plain,(
    ! [X0] :
      ( v9_waybel_1(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ( v9_waybel_1(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ( v9_waybel_1(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_waybel_1(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t15_waybel_7.p',cc10_waybel_1)).

fof(f22603,plain,
    ( ~ spl8_11
    | ~ spl8_523 ),
    inference(avatar_split_clause,[],[f114,f22601,f247])).

fof(f114,plain,
    ( ~ r2_hidden(k8_setfam_1(sK0,sK2),sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f93])).

fof(f22557,plain,
    ( ~ spl8_11
    | spl8_520 ),
    inference(avatar_split_clause,[],[f113,f22555,f247])).

fof(f113,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f93])).

fof(f22532,plain,
    ( ~ spl8_28
    | ~ spl8_70
    | spl8_113
    | ~ spl8_120
    | spl8_135
    | spl8_147
    | ~ spl8_464 ),
    inference(avatar_contradiction_clause,[],[f22531])).

fof(f22531,plain,
    ( $false
    | ~ spl8_28
    | ~ spl8_70
    | ~ spl8_113
    | ~ spl8_120
    | ~ spl8_135
    | ~ spl8_147
    | ~ spl8_464 ),
    inference(subsumption_resolution,[],[f22530,f22522])).

fof(f22522,plain,
    ( ~ r2_hidden(k1_setfam_1(sK4(k3_yellow_1(sK0),sK1)),sK1)
    | ~ spl8_135
    | ~ spl8_147
    | ~ spl8_464 ),
    inference(backward_demodulation,[],[f22481,f2179])).

fof(f2179,plain,
    ( ~ r2_hidden(k2_yellow_0(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1)),sK1)
    | ~ spl8_147 ),
    inference(avatar_component_clause,[],[f2178])).

fof(f2178,plain,
    ( spl8_147
  <=> ~ r2_hidden(k2_yellow_0(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_147])])).

fof(f22481,plain,
    ( k2_yellow_0(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1)) = k1_setfam_1(sK4(k3_yellow_1(sK0),sK1))
    | ~ spl8_135
    | ~ spl8_464 ),
    inference(unit_resulting_resolution,[],[f2018,f21500,f459])).

fof(f459,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,u1_struct_0(k3_yellow_1(X0)))
      | v1_xboole_0(X1)
      | k2_yellow_0(k3_yellow_1(X0),X1) = k1_setfam_1(X1) ) ),
    inference(resolution,[],[f202,f203])).

fof(f21500,plain,
    ( r1_tarski(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ spl8_464 ),
    inference(avatar_component_clause,[],[f21499])).

fof(f21499,plain,
    ( spl8_464
  <=> r1_tarski(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_464])])).

fof(f2018,plain,
    ( ~ v1_xboole_0(sK4(k3_yellow_1(sK0),sK1))
    | ~ spl8_135 ),
    inference(avatar_component_clause,[],[f2017])).

fof(f2017,plain,
    ( spl8_135
  <=> ~ v1_xboole_0(sK4(k3_yellow_1(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_135])])).

fof(f22530,plain,
    ( r2_hidden(k1_setfam_1(sK4(k3_yellow_1(sK0),sK1)),sK1)
    | ~ spl8_28
    | ~ spl8_70
    | ~ spl8_113
    | ~ spl8_120
    | ~ spl8_464 ),
    inference(forward_demodulation,[],[f22479,f22523])).

fof(f22523,plain,
    ( k8_setfam_1(sK0,sK4(k3_yellow_1(sK0),sK1)) = k1_setfam_1(sK4(k3_yellow_1(sK0),sK1))
    | ~ spl8_113
    | ~ spl8_464 ),
    inference(backward_demodulation,[],[f22480,f22482])).

fof(f22482,plain,
    ( k8_setfam_1(sK0,sK4(k3_yellow_1(sK0),sK1)) = k6_setfam_1(sK0,sK4(k3_yellow_1(sK0),sK1))
    | ~ spl8_113
    | ~ spl8_464 ),
    inference(unit_resulting_resolution,[],[f1743,f21500,f472])).

fof(f472,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,u1_struct_0(k3_yellow_1(X1)))
      | k8_setfam_1(X1,X0) = k6_setfam_1(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f197,f203])).

fof(f1743,plain,
    ( k1_xboole_0 != sK4(k3_yellow_1(sK0),sK1)
    | ~ spl8_113 ),
    inference(avatar_component_clause,[],[f1742])).

fof(f1742,plain,
    ( spl8_113
  <=> k1_xboole_0 != sK4(k3_yellow_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_113])])).

fof(f22480,plain,
    ( k6_setfam_1(sK0,sK4(k3_yellow_1(sK0),sK1)) = k1_setfam_1(sK4(k3_yellow_1(sK0),sK1))
    | ~ spl8_464 ),
    inference(unit_resulting_resolution,[],[f21500,f407])).

fof(f407,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,u1_struct_0(k3_yellow_1(X0)))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(resolution,[],[f193,f203])).

fof(f22479,plain,
    ( r2_hidden(k8_setfam_1(sK0,sK4(k3_yellow_1(sK0),sK1)),sK1)
    | ~ spl8_28
    | ~ spl8_70
    | ~ spl8_120
    | ~ spl8_464 ),
    inference(unit_resulting_resolution,[],[f885,f1780,f21500,f420])).

fof(f420,plain,
    ( ! [X0] :
        ( r2_hidden(k8_setfam_1(sK0,X0),sK1)
        | ~ v1_finset_1(X0)
        | ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(X0,u1_struct_0(k3_yellow_1(sK0))) )
    | ~ spl8_28 ),
    inference(resolution,[],[f418,f203])).

fof(f418,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK0)))))
        | ~ v1_finset_1(X3)
        | r2_hidden(k8_setfam_1(sK0,X3),sK1)
        | ~ r1_tarski(X3,sK1) )
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f417])).

fof(f417,plain,
    ( spl8_28
  <=> ! [X3] :
        ( r2_hidden(k8_setfam_1(sK0,X3),sK1)
        | ~ v1_finset_1(X3)
        | ~ m1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK0)))))
        | ~ r1_tarski(X3,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f1780,plain,
    ( r1_tarski(sK4(k3_yellow_1(sK0),sK1),sK1)
    | ~ spl8_120 ),
    inference(avatar_component_clause,[],[f1779])).

fof(f1779,plain,
    ( spl8_120
  <=> r1_tarski(sK4(k3_yellow_1(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_120])])).

fof(f885,plain,
    ( v1_finset_1(sK4(k3_yellow_1(sK0),sK1))
    | ~ spl8_70 ),
    inference(avatar_component_clause,[],[f884])).

fof(f884,plain,
    ( spl8_70
  <=> v1_finset_1(sK4(k3_yellow_1(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_70])])).

fof(f21501,plain,
    ( spl8_464
    | ~ spl8_38
    | ~ spl8_120 ),
    inference(avatar_split_clause,[],[f1834,f1779,f561,f21499])).

fof(f1834,plain,
    ( r1_tarski(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ spl8_38
    | ~ spl8_120 ),
    inference(unit_resulting_resolution,[],[f562,f1780,f175])).

fof(f2180,plain,
    ( ~ spl8_147
    | spl8_1
    | ~ spl8_8
    | spl8_11
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f530,f269,f247,f240,f212,f2178])).

fof(f530,plain,
    ( ~ r2_hidden(k2_yellow_0(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1)),sK1)
    | ~ spl8_1
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f213,f122,f123,f124,f128,f248,f241,f270,f318,f188])).

fof(f188,plain,(
    ! [X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ r2_hidden(k2_yellow_0(X0,sK4(X0,X1)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | ~ v13_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | v2_waybel_0(X1,X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(definition_unfolding,[],[f155,f180])).

fof(f155,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X1,X0)
      | ~ r2_hidden(k2_yellow_0(X0,sK4(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f99])).

fof(f248,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f247])).

fof(f2019,plain,
    ( ~ spl8_135
    | ~ spl8_18
    | spl8_113 ),
    inference(avatar_split_clause,[],[f1823,f1742,f281,f2017])).

fof(f281,plain,
    ( spl8_18
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f1823,plain,
    ( ~ v1_xboole_0(sK4(k3_yellow_1(sK0),sK1))
    | ~ spl8_18
    | ~ spl8_113 ),
    inference(unit_resulting_resolution,[],[f282,f1743,f173])).

fof(f173,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t15_waybel_7.p',t8_boole)).

fof(f282,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f281])).

fof(f1781,plain,
    ( spl8_120
    | spl8_1
    | ~ spl8_8
    | spl8_11
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f1565,f269,f247,f240,f212,f1779])).

fof(f1565,plain,
    ( r1_tarski(sK4(k3_yellow_1(sK0),sK1),sK1)
    | ~ spl8_1
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f213,f318,f122,f123,f124,f128,f248,f241,f270,f505])).

fof(f505,plain,(
    ! [X4,X3] :
      ( ~ v2_lattice3(X4)
      | ~ m1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X4))))
      | ~ v13_waybel_0(X3,X4)
      | v1_xboole_0(X3)
      | ~ l1_orders_2(X4)
      | v2_waybel_0(X3,X4)
      | ~ v5_orders_2(X4)
      | ~ v4_orders_2(X4)
      | ~ v3_orders_2(X4)
      | r1_tarski(sK4(X4,X3),X3) ) ),
    inference(resolution,[],[f190,f204])).

fof(f204,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f171,f180])).

fof(f171,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f190,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),u1_struct_0(k3_yellow_1(X1)))
      | v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | ~ v13_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(definition_unfolding,[],[f153,f180,f180])).

fof(f153,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X1,X0)
      | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f99])).

fof(f1744,plain,
    ( ~ spl8_113
    | spl8_1
    | ~ spl8_8
    | spl8_11
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f531,f269,f247,f240,f212,f1742])).

fof(f531,plain,
    ( k1_xboole_0 != sK4(k3_yellow_1(sK0),sK1)
    | ~ spl8_1
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f213,f122,f123,f124,f128,f248,f241,f270,f318,f189])).

fof(f189,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != sK4(X0,X1)
      | v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | ~ v13_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(definition_unfolding,[],[f154,f180])).

fof(f154,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X1,X0)
      | k1_xboole_0 != sK4(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f99])).

fof(f886,plain,
    ( spl8_70
    | spl8_1
    | ~ spl8_8
    | spl8_11
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f532,f269,f247,f240,f212,f884])).

fof(f532,plain,
    ( v1_finset_1(sK4(k3_yellow_1(sK0),sK1))
    | ~ spl8_1
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f213,f122,f123,f124,f128,f248,f241,f270,f318,f191])).

fof(f191,plain,(
    ! [X0,X1] :
      ( ~ v2_lattice3(X0)
      | v1_finset_1(sK4(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | ~ v13_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | v2_waybel_0(X1,X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(definition_unfolding,[],[f152,f180])).

fof(f152,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X1,X0)
      | v1_finset_1(sK4(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f99])).

fof(f563,plain,
    ( spl8_38
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f334,f269,f561])).

fof(f334,plain,
    ( r1_tarski(sK1,u1_struct_0(k3_yellow_1(sK0)))
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f270,f204])).

fof(f419,plain,
    ( spl8_10
    | spl8_28 ),
    inference(avatar_split_clause,[],[f182,f417,f244])).

fof(f182,plain,(
    ! [X3] :
      ( r2_hidden(k8_setfam_1(sK0,X3),sK1)
      | ~ r1_tarski(X3,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK0)))))
      | ~ v1_finset_1(X3)
      | v2_waybel_0(sK1,k3_yellow_1(sK0)) ) ),
    inference(definition_unfolding,[],[f110,f180,f180])).

fof(f110,plain,(
    ! [X3] :
      ( r2_hidden(k8_setfam_1(sK0,X3),sK1)
      | ~ r1_tarski(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ v1_finset_1(X3)
      | v2_waybel_0(sK1,k3_yellow_1(sK0)) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f283,plain,
    ( spl8_18
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f276,f219,f281])).

fof(f219,plain,
    ( spl8_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f276,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_2 ),
    inference(backward_demodulation,[],[f274,f220])).

fof(f220,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f219])).

fof(f274,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f220,f149])).

fof(f271,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f183,f269])).

fof(f183,plain,(
    m1_subset_1(sK1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK0))))) ),
    inference(definition_unfolding,[],[f109,f180])).

fof(f109,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))) ),
    inference(cnf_transformation,[],[f93])).

fof(f255,plain,
    ( ~ spl8_11
    | spl8_12 ),
    inference(avatar_split_clause,[],[f111,f253,f247])).

fof(f111,plain,
    ( v1_finset_1(sK2)
    | ~ v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f93])).

fof(f242,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f108,f240])).

fof(f108,plain,(
    v13_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f93])).

fof(f221,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f115,f219])).

fof(f115,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t15_waybel_7.p',dt_o_0_0_xboole_0)).

fof(f214,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f107,f212])).

fof(f107,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f93])).
%------------------------------------------------------------------------------
