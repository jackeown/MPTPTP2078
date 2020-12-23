%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1784+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:32 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 239 expanded)
%              Number of leaves         :   32 ( 103 expanded)
%              Depth                    :   12
%              Number of atoms          :  445 ( 797 expanded)
%              Number of equality atoms :   48 (  57 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f964,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f89,f94,f99,f104,f119,f133,f191,f203,f208,f245,f671,f700,f860,f934,f963])).

fof(f963,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK1)
    | sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)) != k4_subset_1(u1_struct_0(sK0),sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),k1_xboole_0)
    | r2_hidden(sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),k5_tmap_1(sK0,sK1))
    | ~ r2_hidden(k4_subset_1(u1_struct_0(sK0),sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),k3_xboole_0(k1_xboole_0,sK1)),k5_tmap_1(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f934,plain,
    ( spl5_54
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_15
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f929,f495,f242,f205,f184,f130,f101,f96,f91,f86,f931])).

fof(f931,plain,
    ( spl5_54
  <=> r2_hidden(k4_subset_1(u1_struct_0(sK0),sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),k3_xboole_0(k1_xboole_0,sK1)),k5_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f86,plain,
    ( spl5_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f91,plain,
    ( spl5_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f96,plain,
    ( spl5_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f101,plain,
    ( spl5_5
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f130,plain,
    ( spl5_7
  <=> r2_hidden(k1_xboole_0,u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f184,plain,
    ( spl5_10
  <=> k5_tmap_1(sK0,sK1) = a_2_0_tmap_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f205,plain,
    ( spl5_12
  <=> r2_hidden(sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f242,plain,
    ( spl5_15
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f495,plain,
    ( spl5_27
  <=> m1_subset_1(sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f929,plain,
    ( r2_hidden(k4_subset_1(u1_struct_0(sK0),sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),k3_xboole_0(k1_xboole_0,sK1)),k5_tmap_1(sK0,sK1))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_15
    | ~ spl5_27 ),
    inference(forward_demodulation,[],[f928,f148])).

fof(f148,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f88,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f88,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f928,plain,
    ( r2_hidden(k4_subset_1(u1_struct_0(sK0),sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),k9_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)),k5_tmap_1(sK0,sK1))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_15
    | ~ spl5_27 ),
    inference(forward_demodulation,[],[f770,f186])).

fof(f186,plain,
    ( k5_tmap_1(sK0,sK1) = a_2_0_tmap_1(sK0,sK1)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f184])).

fof(f770,plain,
    ( r2_hidden(k4_subset_1(u1_struct_0(sK0),sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),k9_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)),a_2_0_tmap_1(sK0,sK1))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_15
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f103,f98,f93,f88,f132,f244,f207,f497,f79])).

fof(f79,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)),a_2_0_tmap_1(X1,X2))
      | ~ r2_hidden(X4,u1_pre_topc(X1))
      | ~ r2_hidden(X3,u1_pre_topc(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
      | ~ r2_hidden(X4,u1_pre_topc(X1))
      | ~ r2_hidden(X3,u1_pre_topc(X1))
      | k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) != X0
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
          | ! [X3,X4] :
              ( ~ r2_hidden(X4,u1_pre_topc(X1))
              | ~ r2_hidden(X3,u1_pre_topc(X1))
              | k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) != X0
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ( r2_hidden(sK4(X0,X1,X2),u1_pre_topc(X1))
            & r2_hidden(sK3(X0,X1,X2),u1_pre_topc(X1))
            & k4_subset_1(u1_struct_0(X1),sK3(X0,X1,X2),k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),X2)) = X0
            & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
            & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_0_tmap_1(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f47,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X5,X6] :
          ( r2_hidden(X6,u1_pre_topc(X1))
          & r2_hidden(X5,u1_pre_topc(X1))
          & k4_subset_1(u1_struct_0(X1),X5,k9_subset_1(u1_struct_0(X1),X6,X2)) = X0
          & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( r2_hidden(sK4(X0,X1,X2),u1_pre_topc(X1))
        & r2_hidden(sK3(X0,X1,X2),u1_pre_topc(X1))
        & k4_subset_1(u1_struct_0(X1),sK3(X0,X1,X2),k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),X2)) = X0
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
          | ! [X3,X4] :
              ( ~ r2_hidden(X4,u1_pre_topc(X1))
              | ~ r2_hidden(X3,u1_pre_topc(X1))
              | k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) != X0
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ? [X5,X6] :
              ( r2_hidden(X6,u1_pre_topc(X1))
              & r2_hidden(X5,u1_pre_topc(X1))
              & k4_subset_1(u1_struct_0(X1),X5,k9_subset_1(u1_struct_0(X1),X6,X2)) = X0
              & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_0_tmap_1(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
          | ! [X3,X4] :
              ( ~ r2_hidden(X4,u1_pre_topc(X1))
              | ~ r2_hidden(X3,u1_pre_topc(X1))
              | k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) != X0
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ? [X3,X4] :
              ( r2_hidden(X4,u1_pre_topc(X1))
              & r2_hidden(X3,u1_pre_topc(X1))
              & k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) = X0
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_0_tmap_1(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
      <=> ? [X3,X4] :
            ( r2_hidden(X4,u1_pre_topc(X1))
            & r2_hidden(X3,u1_pre_topc(X1))
            & k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) = X0
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
      <=> ? [X3,X4] :
            ( r2_hidden(X4,u1_pre_topc(X1))
            & r2_hidden(X3,u1_pre_topc(X1))
            & k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) = X0
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
      <=> ? [X3,X4] :
            ( r2_hidden(X4,u1_pre_topc(X1))
            & r2_hidden(X3,u1_pre_topc(X1))
            & k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) = X0
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_tmap_1)).

fof(f497,plain,
    ( m1_subset_1(sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f495])).

fof(f207,plain,
    ( r2_hidden(sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),u1_pre_topc(sK0))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f205])).

fof(f244,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f242])).

fof(f132,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(sK0))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f130])).

fof(f93,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f98,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f103,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f860,plain,
    ( spl5_43
    | ~ spl5_15
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f855,f495,f242,f857])).

fof(f857,plain,
    ( spl5_43
  <=> sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f855,plain,
    ( sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),k1_xboole_0)
    | ~ spl5_15
    | ~ spl5_27 ),
    inference(forward_demodulation,[],[f798,f56])).

fof(f56,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f798,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),k1_xboole_0) = k2_xboole_0(sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),k1_xboole_0)
    | ~ spl5_15
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f244,f497,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f700,plain,
    ( spl5_30
    | ~ spl5_2
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f686,f242,f86,f696])).

fof(f696,plain,
    ( spl5_30
  <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f686,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1)
    | ~ spl5_2
    | ~ spl5_15 ),
    inference(superposition,[],[f507,f313])).

fof(f313,plain,
    ( ! [X0] : k1_xboole_0 = k9_subset_1(u1_struct_0(sK0),X0,k1_xboole_0)
    | ~ spl5_15 ),
    inference(forward_demodulation,[],[f260,f55])).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f260,plain,
    ( ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k9_subset_1(u1_struct_0(sK0),X0,k1_xboole_0)
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f244,f68])).

fof(f507,plain,
    ( ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f149,f148])).

fof(f149,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f88,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f671,plain,
    ( spl5_27
    | ~ spl5_6
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f666,f205,f116,f495])).

fof(f116,plain,
    ( spl5_6
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f666,plain,
    ( m1_subset_1(sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_6
    | ~ spl5_12 ),
    inference(resolution,[],[f230,f207])).

fof(f230,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,u1_pre_topc(sK0))
        | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_6 ),
    inference(resolution,[],[f118,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f118,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f116])).

fof(f245,plain,
    ( spl5_15
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f221,f130,f116,f242])).

fof(f221,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f132,f118,f76])).

fof(f208,plain,
    ( spl5_12
    | spl5_1 ),
    inference(avatar_split_clause,[],[f194,f81,f205])).

fof(f81,plain,
    ( spl5_1
  <=> r1_tarski(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f194,plain,
    ( r2_hidden(sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),u1_pre_topc(sK0))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f83,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f83,plain,
    ( ~ r1_tarski(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f203,plain,
    ( ~ spl5_11
    | spl5_1 ),
    inference(avatar_split_clause,[],[f195,f81,f200])).

fof(f200,plain,
    ( spl5_11
  <=> r2_hidden(sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),k5_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f195,plain,
    ( ~ r2_hidden(sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),k5_tmap_1(sK0,sK1))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f83,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f191,plain,
    ( spl5_10
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f190,f101,f96,f91,f86,f184])).

fof(f190,plain,
    ( k5_tmap_1(sK0,sK1) = a_2_0_tmap_1(sK0,sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5 ),
    inference(subsumption_resolution,[],[f189,f103])).

fof(f189,plain,
    ( k5_tmap_1(sK0,sK1) = a_2_0_tmap_1(sK0,sK1)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f188,f98])).

fof(f188,plain,
    ( k5_tmap_1(sK0,sK1) = a_2_0_tmap_1(sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f154,f93])).

fof(f154,plain,
    ( k5_tmap_1(sK0,sK1) = a_2_0_tmap_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f88,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tmap_1)).

fof(f133,plain,
    ( spl5_7
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f120,f96,f91,f130])).

fof(f120,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(sK0))
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f93,f98,f59])).

fof(f59,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_pre_topc)).

fof(f119,plain,
    ( spl5_6
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f105,f91,f116])).

fof(f105,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f93,f57])).

fof(f57,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f104,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f50,f101])).

fof(f50,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ~ r1_tarski(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(u1_pre_topc(sK0),k5_tmap_1(sK0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ~ r1_tarski(u1_pre_topc(sK0),k5_tmap_1(sK0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_tmap_1)).

fof(f99,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f51,f96])).

fof(f51,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f94,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f52,f91])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f89,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f53,f86])).

fof(f53,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f84,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f54,f81])).

fof(f54,plain,(
    ~ r1_tarski(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f40])).

%------------------------------------------------------------------------------
