%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  206 ( 478 expanded)
%              Number of leaves         :   47 ( 224 expanded)
%              Depth                    :   12
%              Number of atoms          :  897 (1878 expanded)
%              Number of equality atoms :   21 (  27 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f782,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f113,f118,f123,f128,f133,f138,f186,f190,f219,f266,f289,f301,f368,f375,f378,f389,f390,f420,f462,f471,f513,f703,f719,f731,f737,f779])).

fof(f779,plain,
    ( ~ spl6_36
    | spl6_41 ),
    inference(avatar_contradiction_clause,[],[f778])).

fof(f778,plain,
    ( $false
    | ~ spl6_36
    | spl6_41 ),
    inference(subsumption_resolution,[],[f763,f461])).

fof(f461,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f459])).

fof(f459,plain,
    ( spl6_36
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f763,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl6_41 ),
    inference(resolution,[],[f508,f102])).

fof(f102,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k2_tarski(X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f87,f76])).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f87,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & ~ r2_hidden(sK5(X0,X1,X2),X0) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( r2_hidden(sK5(X0,X1,X2),X1)
            | r2_hidden(sK5(X0,X1,X2),X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f58,f59])).

fof(f59,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & ~ r2_hidden(sK5(X0,X1,X2),X0) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( r2_hidden(sK5(X0,X1,X2),X1)
          | r2_hidden(sK5(X0,X1,X2),X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f508,plain,
    ( ~ r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3)))
    | spl6_41 ),
    inference(avatar_component_clause,[],[f506])).

fof(f506,plain,
    ( spl6_41
  <=> r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f737,plain,
    ( k3_tarski(k2_tarski(sK2,sK3)) != k4_subset_1(u1_struct_0(sK0),sK2,sK3)
    | m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f731,plain,
    ( spl6_42
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_29
    | ~ spl6_30
    | ~ spl6_33
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f661,f468,f417,f372,f365,f130,f125,f510])).

fof(f510,plain,
    ( spl6_42
  <=> v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f125,plain,
    ( spl6_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f130,plain,
    ( spl6_6
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f365,plain,
    ( spl6_29
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f372,plain,
    ( spl6_30
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f417,plain,
    ( spl6_33
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f468,plain,
    ( spl6_37
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f661,plain,
    ( v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_29
    | ~ spl6_30
    | ~ spl6_33
    | ~ spl6_37 ),
    inference(unit_resulting_resolution,[],[f132,f127,f470,f419,f367,f374,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k3_tarski(k2_tarski(X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f82,f76])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_tops_1)).

fof(f374,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f372])).

fof(f367,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f365])).

fof(f419,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f417])).

fof(f470,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f468])).

fof(f127,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f125])).

fof(f132,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f130])).

fof(f719,plain,
    ( spl6_59
    | ~ spl6_29
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f668,f372,f365,f716])).

fof(f716,plain,
    ( spl6_59
  <=> k3_tarski(k2_tarski(sK2,sK3)) = k4_subset_1(u1_struct_0(sK0),sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f668,plain,
    ( k3_tarski(k2_tarski(sK2,sK3)) = k4_subset_1(u1_struct_0(sK0),sK2,sK3)
    | ~ spl6_29
    | ~ spl6_30 ),
    inference(unit_resulting_resolution,[],[f367,f374,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f85,f76])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f703,plain,
    ( spl6_56
    | ~ spl6_29
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f672,f372,f365,f700])).

fof(f700,plain,
    ( spl6_56
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

% (14248)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f672,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_29
    | ~ spl6_30 ),
    inference(unit_resulting_resolution,[],[f367,f374,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f513,plain,
    ( ~ spl6_40
    | ~ spl6_41
    | ~ spl6_42
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_24 ),
    inference(avatar_split_clause,[],[f500,f297,f135,f130,f125,f120,f510,f506,f502])).

fof(f502,plain,
    ( spl6_40
  <=> m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f120,plain,
    ( spl6_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f135,plain,
    ( spl6_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f297,plain,
    ( spl6_24
  <=> r2_hidden(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f500,plain,
    ( ~ v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0)
    | ~ r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_24 ),
    inference(subsumption_resolution,[],[f499,f137])).

fof(f137,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f135])).

fof(f499,plain,
    ( ~ v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0)
    | ~ r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_24 ),
    inference(subsumption_resolution,[],[f498,f132])).

fof(f498,plain,
    ( ~ v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0)
    | ~ r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_5
    | spl6_24 ),
    inference(subsumption_resolution,[],[f497,f127])).

fof(f497,plain,
    ( ~ v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0)
    | ~ r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_4
    | spl6_24 ),
    inference(subsumption_resolution,[],[f483,f122])).

fof(f122,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f483,plain,
    ( ~ v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0)
    | ~ r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_24 ),
    inference(resolution,[],[f299,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v3_pre_topc(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
                  | ~ v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X1,X2) )
                & ( ( v3_pre_topc(X2,X0)
                    & r2_hidden(X1,X2) )
                  | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
                  | ~ v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X1,X2) )
                & ( ( v3_pre_topc(X2,X0)
                    & r2_hidden(X1,X2) )
                  | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_6)).

fof(f299,plain,
    ( ~ r2_hidden(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))
    | spl6_24 ),
    inference(avatar_component_clause,[],[f297])).

fof(f471,plain,
    ( ~ spl6_30
    | spl6_37
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f466,f278,f135,f130,f125,f120,f468,f372])).

fof(f278,plain,
    ( spl6_22
  <=> r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f466,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f465,f137])).

fof(f465,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f464,f132])).

fof(f464,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f463,f127])).

fof(f463,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f447,f122])).

fof(f447,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_22 ),
    inference(resolution,[],[f280,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f280,plain,
    ( r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f278])).

fof(f462,plain,
    ( ~ spl6_30
    | spl6_36
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f457,f278,f135,f130,f125,f120,f459,f372])).

fof(f457,plain,
    ( r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f456,f137])).

fof(f456,plain,
    ( r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f455,f132])).

fof(f455,plain,
    ( r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f454,f127])).

fof(f454,plain,
    ( r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f446,f122])).

fof(f446,plain,
    ( r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_22 ),
    inference(resolution,[],[f280,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f420,plain,
    ( ~ spl6_29
    | spl6_33
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f415,f243,f135,f130,f125,f120,f417,f365])).

fof(f243,plain,
    ( spl6_18
  <=> r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f415,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f414,f137])).

fof(f414,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f413,f132])).

fof(f413,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f412,f127])).

fof(f412,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f396,f122])).

fof(f396,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_18 ),
    inference(resolution,[],[f245,f71])).

fof(f245,plain,
    ( r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f243])).

fof(f390,plain,
    ( spl6_18
    | ~ spl6_2
    | spl6_17 ),
    inference(avatar_split_clause,[],[f379,f239,f110,f243])).

fof(f110,plain,
    ( spl6_2
  <=> m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f239,plain,
    ( spl6_17
  <=> v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f379,plain,
    ( r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl6_2
    | spl6_17 ),
    inference(unit_resulting_resolution,[],[f112,f240,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f240,plain,
    ( ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))
    | spl6_17 ),
    inference(avatar_component_clause,[],[f239])).

fof(f112,plain,
    ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f110])).

fof(f389,plain,
    ( spl6_22
    | ~ spl6_3
    | spl6_17 ),
    inference(avatar_split_clause,[],[f380,f239,f115,f278])).

fof(f115,plain,
    ( spl6_3
  <=> m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f380,plain,
    ( r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl6_3
    | spl6_17 ),
    inference(unit_resulting_resolution,[],[f117,f240,f78])).

fof(f117,plain,
    ( m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f115])).

fof(f378,plain,
    ( ~ spl6_17
    | spl6_9
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f376,f285,f179,f239])).

fof(f179,plain,
    ( spl6_9
  <=> v2_struct_0(k9_yellow_6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f285,plain,
    ( spl6_23
  <=> l1_struct_0(k9_yellow_6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f376,plain,
    ( ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))
    | spl6_9
    | ~ spl6_23 ),
    inference(unit_resulting_resolution,[],[f181,f287,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f287,plain,
    ( l1_struct_0(k9_yellow_6(sK0,sK1))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f285])).

fof(f181,plain,
    ( ~ v2_struct_0(k9_yellow_6(sK0,sK1))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f179])).

fof(f375,plain,
    ( spl6_30
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f369,f258,f135,f130,f125,f120,f372])).

fof(f258,plain,
    ( spl6_19
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f369,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_19 ),
    inference(unit_resulting_resolution,[],[f137,f132,f127,f122,f260,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f260,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f258])).

fof(f368,plain,
    ( spl6_29
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f362,f211,f135,f130,f125,f120,f365])).

fof(f211,plain,
    ( spl6_12
  <=> m1_connsp_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f362,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f137,f132,f127,f122,f213,f81])).

fof(f213,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f211])).

fof(f301,plain,
    ( ~ spl6_24
    | spl6_1 ),
    inference(avatar_split_clause,[],[f292,f105,f297])).

fof(f105,plain,
    ( spl6_1
  <=> m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f292,plain,
    ( ~ r2_hidden(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))
    | spl6_1 ),
    inference(resolution,[],[f107,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f107,plain,
    ( ~ m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f105])).

fof(f289,plain,
    ( spl6_23
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f283,f174,f285])).

fof(f174,plain,
    ( spl6_8
  <=> l1_orders_2(k9_yellow_6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f283,plain,
    ( l1_struct_0(k9_yellow_6(sK0,sK1))
    | ~ spl6_8 ),
    inference(resolution,[],[f176,f68])).

fof(f68,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f176,plain,
    ( l1_orders_2(k9_yellow_6(sK0,sK1))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f174])).

fof(f266,plain,
    ( spl6_19
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7 ),
    inference(avatar_split_clause,[],[f265,f135,f130,f125,f120,f115,f258])).

fof(f265,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7 ),
    inference(subsumption_resolution,[],[f264,f137])).

fof(f264,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f263,f132])).

fof(f263,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f262,f127])).

fof(f262,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f248,f122])).

fof(f248,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3 ),
    inference(resolution,[],[f117,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_waybel_9)).

fof(f219,plain,
    ( spl6_12
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7 ),
    inference(avatar_split_clause,[],[f218,f135,f130,f125,f120,f110,f211])).

fof(f218,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7 ),
    inference(subsumption_resolution,[],[f217,f137])).

fof(f217,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f216,f132])).

fof(f216,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f215,f127])).

fof(f215,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f201,f122])).

fof(f201,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_2 ),
    inference(resolution,[],[f112,f73])).

fof(f190,plain,
    ( spl6_8
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7 ),
    inference(avatar_split_clause,[],[f189,f135,f130,f125,f120,f174])).

fof(f189,plain,
    ( l1_orders_2(k9_yellow_6(sK0,sK1))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7 ),
    inference(subsumption_resolution,[],[f188,f137])).

fof(f188,plain,
    ( l1_orders_2(k9_yellow_6(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f187,f132])).

fof(f187,plain,
    ( l1_orders_2(k9_yellow_6(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f170,f127])).

fof(f170,plain,
    ( l1_orders_2(k9_yellow_6(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_4 ),
    inference(resolution,[],[f122,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( l1_orders_2(k9_yellow_6(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( l1_orders_2(k9_yellow_6(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( l1_orders_2(k9_yellow_6(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => l1_orders_2(k9_yellow_6(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_yellow_6)).

fof(f186,plain,
    ( ~ spl6_9
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7 ),
    inference(avatar_split_clause,[],[f185,f135,f130,f125,f120,f179])).

fof(f185,plain,
    ( ~ v2_struct_0(k9_yellow_6(sK0,sK1))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7 ),
    inference(subsumption_resolution,[],[f184,f137])).

fof(f184,plain,
    ( ~ v2_struct_0(k9_yellow_6(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f183,f132])).

fof(f183,plain,
    ( ~ v2_struct_0(k9_yellow_6(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f169,f127])).

fof(f169,plain,
    ( ~ v2_struct_0(k9_yellow_6(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_4 ),
    inference(resolution,[],[f122,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k9_yellow_6(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k9_yellow_6(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k9_yellow_6(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ~ v2_struct_0(k9_yellow_6(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc20_yellow_6)).

fof(f138,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f61,f135])).

fof(f61,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))
    & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    & m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f48,f47,f46,f45])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                    & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
                & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,X1))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,X1)))
                & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,X1))) )
            & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,X1))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,sK1)))
              & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1))) )
          & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,sK1))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,sK1)))
            & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1))) )
        & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,sK1))) )
   => ( ? [X3] :
          ( ~ m1_subset_1(k2_xboole_0(sK2,X3),u1_struct_0(k9_yellow_6(sK0,sK1)))
          & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1))) )
      & m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X3] :
        ( ~ m1_subset_1(k2_xboole_0(sK2,X3),u1_struct_0(k9_yellow_6(sK0,sK1)))
        & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1))) )
   => ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))
      & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
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
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                   => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                 => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_waybel_9)).

fof(f133,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f62,f130])).

fof(f62,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f128,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f63,f125])).

fof(f63,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f123,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f64,f120])).

fof(f64,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f118,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f65,f115])).

fof(f65,plain,(
    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f113,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f66,f110])).

fof(f66,plain,(
    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f108,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f92,f105])).

fof(f92,plain,(
    ~ m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(definition_unfolding,[],[f67,f76])).

fof(f67,plain,(
    ~ m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:35:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (14236)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (14239)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (14259)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.52  % (14238)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (14243)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (14243)Refutation not found, incomplete strategy% (14243)------------------------------
% 0.22/0.52  % (14243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (14243)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (14243)Memory used [KB]: 10618
% 0.22/0.52  % (14243)Time elapsed: 0.107 s
% 0.22/0.52  % (14243)------------------------------
% 0.22/0.52  % (14243)------------------------------
% 0.22/0.53  % (14259)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f782,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f108,f113,f118,f123,f128,f133,f138,f186,f190,f219,f266,f289,f301,f368,f375,f378,f389,f390,f420,f462,f471,f513,f703,f719,f731,f737,f779])).
% 0.22/0.53  fof(f779,plain,(
% 0.22/0.53    ~spl6_36 | spl6_41),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f778])).
% 0.22/0.53  fof(f778,plain,(
% 0.22/0.53    $false | (~spl6_36 | spl6_41)),
% 0.22/0.53    inference(subsumption_resolution,[],[f763,f461])).
% 0.22/0.53  fof(f461,plain,(
% 0.22/0.53    r2_hidden(sK1,sK2) | ~spl6_36),
% 0.22/0.53    inference(avatar_component_clause,[],[f459])).
% 0.22/0.53  fof(f459,plain,(
% 0.22/0.53    spl6_36 <=> r2_hidden(sK1,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.22/0.53  fof(f763,plain,(
% 0.22/0.53    ~r2_hidden(sK1,sK2) | spl6_41),
% 0.22/0.53    inference(resolution,[],[f508,f102])).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k2_tarski(X0,X1))) | ~r2_hidden(X4,X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f99])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k2_tarski(X0,X1)) != X2) )),
% 0.22/0.53    inference(definition_unfolding,[],[f87,f76])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f60])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK5(X0,X1,X2),X1) & ~r2_hidden(sK5(X0,X1,X2),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f58,f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK5(X0,X1,X2),X1) & ~r2_hidden(sK5(X0,X1,X2),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.53    inference(rectify,[],[f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.53    inference(flattening,[],[f56])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.53    inference(nnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.22/0.53  fof(f508,plain,(
% 0.22/0.53    ~r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3))) | spl6_41),
% 0.22/0.53    inference(avatar_component_clause,[],[f506])).
% 0.22/0.53  fof(f506,plain,(
% 0.22/0.53    spl6_41 <=> r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 0.22/0.53  fof(f737,plain,(
% 0.22/0.53    k3_tarski(k2_tarski(sK2,sK3)) != k4_subset_1(u1_struct_0(sK0),sK2,sK3) | m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.53  fof(f731,plain,(
% 0.22/0.53    spl6_42 | ~spl6_5 | ~spl6_6 | ~spl6_29 | ~spl6_30 | ~spl6_33 | ~spl6_37),
% 0.22/0.53    inference(avatar_split_clause,[],[f661,f468,f417,f372,f365,f130,f125,f510])).
% 0.22/0.53  fof(f510,plain,(
% 0.22/0.53    spl6_42 <=> v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 0.22/0.53  fof(f125,plain,(
% 0.22/0.53    spl6_5 <=> l1_pre_topc(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.53  fof(f130,plain,(
% 0.22/0.53    spl6_6 <=> v2_pre_topc(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.53  fof(f365,plain,(
% 0.22/0.53    spl6_29 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.22/0.53  fof(f372,plain,(
% 0.22/0.53    spl6_30 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.22/0.53  fof(f417,plain,(
% 0.22/0.53    spl6_33 <=> v3_pre_topc(sK3,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.22/0.53  fof(f468,plain,(
% 0.22/0.53    spl6_37 <=> v3_pre_topc(sK2,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 0.22/0.53  fof(f661,plain,(
% 0.22/0.53    v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0) | (~spl6_5 | ~spl6_6 | ~spl6_29 | ~spl6_30 | ~spl6_33 | ~spl6_37)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f132,f127,f470,f419,f367,f374,f93])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v3_pre_topc(k3_tarski(k2_tarski(X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f82,f76])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_xboole_0(X1,X2),X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_tops_1)).
% 0.22/0.53  fof(f374,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_30),
% 0.22/0.53    inference(avatar_component_clause,[],[f372])).
% 0.22/0.53  fof(f367,plain,(
% 0.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_29),
% 0.22/0.53    inference(avatar_component_clause,[],[f365])).
% 0.22/0.53  fof(f419,plain,(
% 0.22/0.53    v3_pre_topc(sK3,sK0) | ~spl6_33),
% 0.22/0.53    inference(avatar_component_clause,[],[f417])).
% 0.22/0.53  fof(f470,plain,(
% 0.22/0.53    v3_pre_topc(sK2,sK0) | ~spl6_37),
% 0.22/0.53    inference(avatar_component_clause,[],[f468])).
% 0.22/0.53  fof(f127,plain,(
% 0.22/0.53    l1_pre_topc(sK0) | ~spl6_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f125])).
% 0.22/0.53  fof(f132,plain,(
% 0.22/0.53    v2_pre_topc(sK0) | ~spl6_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f130])).
% 0.22/0.53  fof(f719,plain,(
% 0.22/0.53    spl6_59 | ~spl6_29 | ~spl6_30),
% 0.22/0.53    inference(avatar_split_clause,[],[f668,f372,f365,f716])).
% 0.22/0.53  fof(f716,plain,(
% 0.22/0.53    spl6_59 <=> k3_tarski(k2_tarski(sK2,sK3)) = k4_subset_1(u1_struct_0(sK0),sK2,sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).
% 0.22/0.53  fof(f668,plain,(
% 0.22/0.53    k3_tarski(k2_tarski(sK2,sK3)) = k4_subset_1(u1_struct_0(sK0),sK2,sK3) | (~spl6_29 | ~spl6_30)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f367,f374,f94])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f85,f76])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(flattening,[],[f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.22/0.53  fof(f703,plain,(
% 0.22/0.53    spl6_56 | ~spl6_29 | ~spl6_30),
% 0.22/0.53    inference(avatar_split_clause,[],[f672,f372,f365,f700])).
% 0.22/0.53  fof(f700,plain,(
% 0.22/0.53    spl6_56 <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).
% 0.22/0.53  % (14248)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  fof(f672,plain,(
% 0.22/0.53    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_29 | ~spl6_30)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f367,f374,f84])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(flattening,[],[f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 0.22/0.53  fof(f513,plain,(
% 0.22/0.53    ~spl6_40 | ~spl6_41 | ~spl6_42 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_24),
% 0.22/0.53    inference(avatar_split_clause,[],[f500,f297,f135,f130,f125,f120,f510,f506,f502])).
% 0.22/0.53  fof(f502,plain,(
% 0.22/0.53    spl6_40 <=> m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 0.22/0.53  fof(f120,plain,(
% 0.22/0.53    spl6_4 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.53  fof(f135,plain,(
% 0.22/0.53    spl6_7 <=> v2_struct_0(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.53  fof(f297,plain,(
% 0.22/0.53    spl6_24 <=> r2_hidden(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.22/0.53  fof(f500,plain,(
% 0.22/0.53    ~v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0) | ~r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3))) | ~m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_24)),
% 0.22/0.53    inference(subsumption_resolution,[],[f499,f137])).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    ~v2_struct_0(sK0) | spl6_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f135])).
% 0.22/0.53  fof(f499,plain,(
% 0.22/0.53    ~v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0) | ~r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3))) | ~m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_24)),
% 0.22/0.53    inference(subsumption_resolution,[],[f498,f132])).
% 0.22/0.53  fof(f498,plain,(
% 0.22/0.53    ~v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0) | ~r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3))) | ~m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_4 | ~spl6_5 | spl6_24)),
% 0.22/0.53    inference(subsumption_resolution,[],[f497,f127])).
% 0.22/0.53  fof(f497,plain,(
% 0.22/0.53    ~v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0) | ~r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3))) | ~m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_4 | spl6_24)),
% 0.22/0.53    inference(subsumption_resolution,[],[f483,f122])).
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl6_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f120])).
% 0.22/0.53  fof(f483,plain,(
% 0.22/0.53    ~v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0) | ~r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3))) | ~m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_24),
% 0.22/0.53    inference(resolution,[],[f299,f72])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2)) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | (~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2))) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_6)).
% 0.22/0.53  fof(f299,plain,(
% 0.22/0.53    ~r2_hidden(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) | spl6_24),
% 0.22/0.53    inference(avatar_component_clause,[],[f297])).
% 0.22/0.53  fof(f471,plain,(
% 0.22/0.53    ~spl6_30 | spl6_37 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_22),
% 0.22/0.53    inference(avatar_split_clause,[],[f466,f278,f135,f130,f125,f120,f468,f372])).
% 0.22/0.53  fof(f278,plain,(
% 0.22/0.53    spl6_22 <=> r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.22/0.53  fof(f466,plain,(
% 0.22/0.53    v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_22)),
% 0.22/0.53    inference(subsumption_resolution,[],[f465,f137])).
% 0.22/0.53  fof(f465,plain,(
% 0.22/0.53    v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_22)),
% 0.22/0.53    inference(subsumption_resolution,[],[f464,f132])).
% 0.22/0.53  fof(f464,plain,(
% 0.22/0.53    v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_4 | ~spl6_5 | ~spl6_22)),
% 0.22/0.53    inference(subsumption_resolution,[],[f463,f127])).
% 0.22/0.53  fof(f463,plain,(
% 0.22/0.53    v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_4 | ~spl6_22)),
% 0.22/0.53    inference(subsumption_resolution,[],[f447,f122])).
% 0.22/0.53  fof(f447,plain,(
% 0.22/0.53    v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_22),
% 0.22/0.53    inference(resolution,[],[f280,f71])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f51])).
% 0.22/0.53  fof(f280,plain,(
% 0.22/0.53    r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl6_22),
% 0.22/0.53    inference(avatar_component_clause,[],[f278])).
% 0.22/0.53  fof(f462,plain,(
% 0.22/0.53    ~spl6_30 | spl6_36 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_22),
% 0.22/0.53    inference(avatar_split_clause,[],[f457,f278,f135,f130,f125,f120,f459,f372])).
% 0.22/0.53  fof(f457,plain,(
% 0.22/0.53    r2_hidden(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_22)),
% 0.22/0.53    inference(subsumption_resolution,[],[f456,f137])).
% 0.22/0.53  fof(f456,plain,(
% 0.22/0.53    r2_hidden(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_22)),
% 0.22/0.53    inference(subsumption_resolution,[],[f455,f132])).
% 0.22/0.53  fof(f455,plain,(
% 0.22/0.53    r2_hidden(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_4 | ~spl6_5 | ~spl6_22)),
% 0.22/0.53    inference(subsumption_resolution,[],[f454,f127])).
% 0.22/0.53  fof(f454,plain,(
% 0.22/0.53    r2_hidden(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_4 | ~spl6_22)),
% 0.22/0.53    inference(subsumption_resolution,[],[f446,f122])).
% 0.22/0.53  fof(f446,plain,(
% 0.22/0.53    r2_hidden(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_22),
% 0.22/0.53    inference(resolution,[],[f280,f70])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f51])).
% 0.22/0.53  fof(f420,plain,(
% 0.22/0.53    ~spl6_29 | spl6_33 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_18),
% 0.22/0.53    inference(avatar_split_clause,[],[f415,f243,f135,f130,f125,f120,f417,f365])).
% 0.22/0.53  fof(f243,plain,(
% 0.22/0.53    spl6_18 <=> r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.22/0.53  fof(f415,plain,(
% 0.22/0.53    v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_18)),
% 0.22/0.53    inference(subsumption_resolution,[],[f414,f137])).
% 0.22/0.53  fof(f414,plain,(
% 0.22/0.53    v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_18)),
% 0.22/0.53    inference(subsumption_resolution,[],[f413,f132])).
% 0.22/0.53  fof(f413,plain,(
% 0.22/0.53    v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_4 | ~spl6_5 | ~spl6_18)),
% 0.22/0.53    inference(subsumption_resolution,[],[f412,f127])).
% 0.22/0.53  fof(f412,plain,(
% 0.22/0.53    v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_4 | ~spl6_18)),
% 0.22/0.53    inference(subsumption_resolution,[],[f396,f122])).
% 0.22/0.53  fof(f396,plain,(
% 0.22/0.53    v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_18),
% 0.22/0.53    inference(resolution,[],[f245,f71])).
% 0.22/0.53  fof(f245,plain,(
% 0.22/0.53    r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl6_18),
% 0.22/0.53    inference(avatar_component_clause,[],[f243])).
% 0.22/0.53  fof(f390,plain,(
% 0.22/0.53    spl6_18 | ~spl6_2 | spl6_17),
% 0.22/0.53    inference(avatar_split_clause,[],[f379,f239,f110,f243])).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    spl6_2 <=> m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.53  fof(f239,plain,(
% 0.22/0.53    spl6_17 <=> v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.22/0.53  fof(f379,plain,(
% 0.22/0.53    r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) | (~spl6_2 | spl6_17)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f112,f240,f78])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.53    inference(flattening,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.53  fof(f240,plain,(
% 0.22/0.53    ~v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) | spl6_17),
% 0.22/0.53    inference(avatar_component_clause,[],[f239])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl6_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f110])).
% 0.22/0.53  fof(f389,plain,(
% 0.22/0.53    spl6_22 | ~spl6_3 | spl6_17),
% 0.22/0.53    inference(avatar_split_clause,[],[f380,f239,f115,f278])).
% 0.22/0.53  fof(f115,plain,(
% 0.22/0.53    spl6_3 <=> m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.53  fof(f380,plain,(
% 0.22/0.53    r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | (~spl6_3 | spl6_17)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f117,f240,f78])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl6_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f115])).
% 0.22/0.53  fof(f378,plain,(
% 0.22/0.53    ~spl6_17 | spl6_9 | ~spl6_23),
% 0.22/0.53    inference(avatar_split_clause,[],[f376,f285,f179,f239])).
% 0.22/0.53  fof(f179,plain,(
% 0.22/0.53    spl6_9 <=> v2_struct_0(k9_yellow_6(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.53  fof(f285,plain,(
% 0.22/0.53    spl6_23 <=> l1_struct_0(k9_yellow_6(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.22/0.53  fof(f376,plain,(
% 0.22/0.53    ~v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) | (spl6_9 | ~spl6_23)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f181,f287,f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.53  fof(f287,plain,(
% 0.22/0.53    l1_struct_0(k9_yellow_6(sK0,sK1)) | ~spl6_23),
% 0.22/0.53    inference(avatar_component_clause,[],[f285])).
% 0.22/0.53  fof(f181,plain,(
% 0.22/0.53    ~v2_struct_0(k9_yellow_6(sK0,sK1)) | spl6_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f179])).
% 0.22/0.53  fof(f375,plain,(
% 0.22/0.53    spl6_30 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_19),
% 0.22/0.53    inference(avatar_split_clause,[],[f369,f258,f135,f130,f125,f120,f372])).
% 0.22/0.53  fof(f258,plain,(
% 0.22/0.53    spl6_19 <=> m1_connsp_2(sK2,sK0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.22/0.53  fof(f369,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_19)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f137,f132,f127,f122,f260,f81])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.22/0.53  fof(f260,plain,(
% 0.22/0.53    m1_connsp_2(sK2,sK0,sK1) | ~spl6_19),
% 0.22/0.53    inference(avatar_component_clause,[],[f258])).
% 0.22/0.53  fof(f368,plain,(
% 0.22/0.53    spl6_29 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_12),
% 0.22/0.53    inference(avatar_split_clause,[],[f362,f211,f135,f130,f125,f120,f365])).
% 0.22/0.53  fof(f211,plain,(
% 0.22/0.53    spl6_12 <=> m1_connsp_2(sK3,sK0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.53  fof(f362,plain,(
% 0.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_12)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f137,f132,f127,f122,f213,f81])).
% 0.22/0.53  fof(f213,plain,(
% 0.22/0.53    m1_connsp_2(sK3,sK0,sK1) | ~spl6_12),
% 0.22/0.53    inference(avatar_component_clause,[],[f211])).
% 0.22/0.53  fof(f301,plain,(
% 0.22/0.53    ~spl6_24 | spl6_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f292,f105,f297])).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    spl6_1 <=> m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.53  fof(f292,plain,(
% 0.22/0.53    ~r2_hidden(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) | spl6_1),
% 0.22/0.53    inference(resolution,[],[f107,f77])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    ~m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) | spl6_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f105])).
% 0.22/0.53  fof(f289,plain,(
% 0.22/0.53    spl6_23 | ~spl6_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f283,f174,f285])).
% 0.22/0.53  fof(f174,plain,(
% 0.22/0.53    spl6_8 <=> l1_orders_2(k9_yellow_6(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.53  fof(f283,plain,(
% 0.22/0.53    l1_struct_0(k9_yellow_6(sK0,sK1)) | ~spl6_8),
% 0.22/0.53    inference(resolution,[],[f176,f68])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.22/0.53  fof(f176,plain,(
% 0.22/0.53    l1_orders_2(k9_yellow_6(sK0,sK1)) | ~spl6_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f174])).
% 0.22/0.53  fof(f266,plain,(
% 0.22/0.53    spl6_19 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f265,f135,f130,f125,f120,f115,f258])).
% 0.22/0.53  fof(f265,plain,(
% 0.22/0.53    m1_connsp_2(sK2,sK0,sK1) | (~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7)),
% 0.22/0.53    inference(subsumption_resolution,[],[f264,f137])).
% 0.22/0.53  fof(f264,plain,(
% 0.22/0.53    m1_connsp_2(sK2,sK0,sK1) | v2_struct_0(sK0) | (~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6)),
% 0.22/0.53    inference(subsumption_resolution,[],[f263,f132])).
% 0.22/0.53  fof(f263,plain,(
% 0.22/0.53    m1_connsp_2(sK2,sK0,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_3 | ~spl6_4 | ~spl6_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f262,f127])).
% 0.22/0.53  fof(f262,plain,(
% 0.22/0.53    m1_connsp_2(sK2,sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_3 | ~spl6_4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f248,f122])).
% 0.22/0.53  fof(f248,plain,(
% 0.22/0.53    m1_connsp_2(sK2,sK0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_3),
% 0.22/0.53    inference(resolution,[],[f117,f73])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => m1_connsp_2(X2,X0,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_waybel_9)).
% 0.22/0.53  fof(f219,plain,(
% 0.22/0.53    spl6_12 | ~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f218,f135,f130,f125,f120,f110,f211])).
% 0.22/0.53  fof(f218,plain,(
% 0.22/0.53    m1_connsp_2(sK3,sK0,sK1) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7)),
% 0.22/0.53    inference(subsumption_resolution,[],[f217,f137])).
% 0.22/0.53  fof(f217,plain,(
% 0.22/0.53    m1_connsp_2(sK3,sK0,sK1) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6)),
% 0.22/0.53    inference(subsumption_resolution,[],[f216,f132])).
% 0.22/0.53  fof(f216,plain,(
% 0.22/0.53    m1_connsp_2(sK3,sK0,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_4 | ~spl6_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f215,f127])).
% 0.22/0.53  fof(f215,plain,(
% 0.22/0.53    m1_connsp_2(sK3,sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f201,f122])).
% 0.22/0.53  fof(f201,plain,(
% 0.22/0.53    m1_connsp_2(sK3,sK0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_2),
% 0.22/0.53    inference(resolution,[],[f112,f73])).
% 0.22/0.53  fof(f190,plain,(
% 0.22/0.53    spl6_8 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f189,f135,f130,f125,f120,f174])).
% 0.22/0.53  fof(f189,plain,(
% 0.22/0.53    l1_orders_2(k9_yellow_6(sK0,sK1)) | (~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7)),
% 0.22/0.53    inference(subsumption_resolution,[],[f188,f137])).
% 0.22/0.53  fof(f188,plain,(
% 0.22/0.53    l1_orders_2(k9_yellow_6(sK0,sK1)) | v2_struct_0(sK0) | (~spl6_4 | ~spl6_5 | ~spl6_6)),
% 0.22/0.53    inference(subsumption_resolution,[],[f187,f132])).
% 0.22/0.53  fof(f187,plain,(
% 0.22/0.53    l1_orders_2(k9_yellow_6(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_4 | ~spl6_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f170,f127])).
% 0.22/0.53  fof(f170,plain,(
% 0.22/0.53    l1_orders_2(k9_yellow_6(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_4),
% 0.22/0.53    inference(resolution,[],[f122,f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ( ! [X0,X1] : (l1_orders_2(k9_yellow_6(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0,X1] : (l1_orders_2(k9_yellow_6(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0,X1] : (l1_orders_2(k9_yellow_6(X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,axiom,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => l1_orders_2(k9_yellow_6(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_yellow_6)).
% 0.22/0.53  fof(f186,plain,(
% 0.22/0.53    ~spl6_9 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f185,f135,f130,f125,f120,f179])).
% 0.22/0.53  fof(f185,plain,(
% 0.22/0.53    ~v2_struct_0(k9_yellow_6(sK0,sK1)) | (~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7)),
% 0.22/0.53    inference(subsumption_resolution,[],[f184,f137])).
% 0.22/0.53  fof(f184,plain,(
% 0.22/0.53    ~v2_struct_0(k9_yellow_6(sK0,sK1)) | v2_struct_0(sK0) | (~spl6_4 | ~spl6_5 | ~spl6_6)),
% 0.22/0.53    inference(subsumption_resolution,[],[f183,f132])).
% 0.22/0.53  fof(f183,plain,(
% 0.22/0.53    ~v2_struct_0(k9_yellow_6(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_4 | ~spl6_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f169,f127])).
% 0.22/0.53  fof(f169,plain,(
% 0.22/0.53    ~v2_struct_0(k9_yellow_6(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_4),
% 0.22/0.53    inference(resolution,[],[f122,f79])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v2_struct_0(k9_yellow_6(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0,X1] : (~v2_struct_0(k9_yellow_6(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0,X1] : (~v2_struct_0(k9_yellow_6(X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,axiom,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ~v2_struct_0(k9_yellow_6(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc20_yellow_6)).
% 0.22/0.53  fof(f138,plain,(
% 0.22/0.53    ~spl6_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f61,f135])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ~v2_struct_0(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    (((~m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f48,f47,f46,f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,X1)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,X1)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,sK1)))) => (? [X3] : (~m1_subset_1(k2_xboole_0(sK2,X3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ? [X3] : (~m1_subset_1(k2_xboole_0(sK2,X3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1)))) => (~m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 0.22/0.53    inference(negated_conjecture,[],[f17])).
% 0.22/0.53  fof(f17,conjecture,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_waybel_9)).
% 0.22/0.53  fof(f133,plain,(
% 0.22/0.53    spl6_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f62,f130])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    v2_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f49])).
% 0.22/0.53  fof(f128,plain,(
% 0.22/0.53    spl6_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f63,f125])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    l1_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f49])).
% 0.22/0.53  fof(f123,plain,(
% 0.22/0.53    spl6_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f64,f120])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.53    inference(cnf_transformation,[],[f49])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    spl6_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f65,f115])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.22/0.53    inference(cnf_transformation,[],[f49])).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    spl6_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f66,f110])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.22/0.53    inference(cnf_transformation,[],[f49])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    ~spl6_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f92,f105])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    ~m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.22/0.53    inference(definition_unfolding,[],[f67,f76])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ~m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.22/0.53    inference(cnf_transformation,[],[f49])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (14259)------------------------------
% 0.22/0.53  % (14259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (14259)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (14259)Memory used [KB]: 6652
% 0.22/0.53  % (14259)Time elapsed: 0.118 s
% 0.22/0.53  % (14259)------------------------------
% 0.22/0.53  % (14259)------------------------------
% 0.22/0.54  % (14233)Success in time 0.173 s
%------------------------------------------------------------------------------
