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
% DateTime   : Thu Dec  3 13:23:10 EST 2020

% Result     : Theorem 1.70s
% Output     : Refutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 459 expanded)
%              Number of leaves         :   45 ( 217 expanded)
%              Depth                    :   12
%              Number of atoms          :  854 (1854 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1325,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f105,f110,f115,f120,f125,f130,f192,f226,f258,f283,f291,f432,f440,f482,f668,f691,f696,f731,f813,f1080,f1108,f1126,f1138,f1322])).

fof(f1322,plain,
    ( ~ spl5_32
    | spl5_45 ),
    inference(avatar_contradiction_clause,[],[f1321])).

fof(f1321,plain,
    ( $false
    | ~ spl5_32
    | spl5_45 ),
    inference(subsumption_resolution,[],[f1305,f506])).

fof(f506,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f504])).

fof(f504,plain,
    ( spl5_32
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f1305,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl5_45 ),
    inference(resolution,[],[f726,f94])).

fof(f94,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k2_tarski(X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f78,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & ~ r2_hidden(sK4(X0,X1,X2),X0) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f49,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & ~ r2_hidden(sK4(X0,X1,X2),X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f726,plain,
    ( ~ r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3)))
    | spl5_45 ),
    inference(avatar_component_clause,[],[f724])).

fof(f724,plain,
    ( spl5_45
  <=> r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f1138,plain,
    ( k3_tarski(k2_tarski(sK2,sK3)) != k4_subset_1(u1_struct_0(sK0),sK2,sK3)
    | m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1126,plain,
    ( spl5_46
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_20
    | ~ spl5_21
    | ~ spl5_23
    | ~ spl5_33 ),
    inference(avatar_split_clause,[],[f1023,f513,f328,f288,f280,f122,f117,f728])).

fof(f728,plain,
    ( spl5_46
  <=> v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f117,plain,
    ( spl5_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f122,plain,
    ( spl5_6
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f280,plain,
    ( spl5_20
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f288,plain,
    ( spl5_21
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f328,plain,
    ( spl5_23
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f513,plain,
    ( spl5_33
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f1023,plain,
    ( v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0)
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_20
    | ~ spl5_21
    | ~ spl5_23
    | ~ spl5_33 ),
    inference(unit_resulting_resolution,[],[f124,f119,f515,f330,f282,f290,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k3_tarski(k2_tarski(X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f73,f66])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_tops_1)).

fof(f290,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f288])).

fof(f282,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f280])).

fof(f330,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f328])).

fof(f515,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f513])).

fof(f119,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f117])).

fof(f124,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f122])).

fof(f1108,plain,
    ( spl5_80
    | ~ spl5_20
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f1033,f288,f280,f1105])).

fof(f1105,plain,
    ( spl5_80
  <=> k3_tarski(k2_tarski(sK2,sK3)) = k4_subset_1(u1_struct_0(sK0),sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).

fof(f1033,plain,
    ( k3_tarski(k2_tarski(sK2,sK3)) = k4_subset_1(u1_struct_0(sK0),sK2,sK3)
    | ~ spl5_20
    | ~ spl5_21 ),
    inference(unit_resulting_resolution,[],[f282,f290,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f76,f66])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f1080,plain,
    ( spl5_75
    | ~ spl5_20
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f1039,f288,f280,f1077])).

fof(f1077,plain,
    ( spl5_75
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).

fof(f1039,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_20
    | ~ spl5_21 ),
    inference(unit_resulting_resolution,[],[f282,f290,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f813,plain,
    ( ~ spl5_21
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_15
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f792,f233,f218,f127,f122,f117,f112,f288])).

fof(f112,plain,
    ( spl5_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f127,plain,
    ( spl5_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f218,plain,
    ( spl5_15
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f233,plain,
    ( spl5_17
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f792,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_15
    | ~ spl5_17 ),
    inference(unit_resulting_resolution,[],[f129,f124,f119,f220,f114,f422,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).

fof(f422,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl5_17 ),
    inference(forward_demodulation,[],[f397,f59])).

fof(f59,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f397,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_subset_1(sK2))
    | ~ spl5_17 ),
    inference(unit_resulting_resolution,[],[f60,f235,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f235,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f233])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f114,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f220,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f218])).

fof(f129,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f127])).

fof(f731,plain,
    ( ~ spl5_44
    | ~ spl5_45
    | ~ spl5_46
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | spl5_18 ),
    inference(avatar_split_clause,[],[f718,f252,f127,f122,f117,f112,f728,f724,f720])).

fof(f720,plain,
    ( spl5_44
  <=> m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f252,plain,
    ( spl5_18
  <=> r2_hidden(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f718,plain,
    ( ~ v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0)
    | ~ r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | spl5_18 ),
    inference(subsumption_resolution,[],[f717,f129])).

fof(f717,plain,
    ( ~ v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0)
    | ~ r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_18 ),
    inference(subsumption_resolution,[],[f716,f124])).

fof(f716,plain,
    ( ~ v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0)
    | ~ r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | spl5_18 ),
    inference(subsumption_resolution,[],[f715,f119])).

fof(f715,plain,
    ( ~ v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0)
    | ~ r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | spl5_18 ),
    inference(subsumption_resolution,[],[f700,f114])).

fof(f700,plain,
    ( ~ v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0)
    | ~ r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_18 ),
    inference(resolution,[],[f254,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v3_pre_topc(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_6)).

fof(f254,plain,
    ( ~ r2_hidden(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))
    | spl5_18 ),
    inference(avatar_component_clause,[],[f252])).

fof(f696,plain,
    ( ~ spl5_21
    | spl5_33
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f695,f228,f127,f122,f117,f112,f513,f288])).

fof(f228,plain,
    ( spl5_16
  <=> r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f695,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f694,f129])).

fof(f694,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f693,f124])).

fof(f693,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f692,f119])).

fof(f692,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f678,f114])).

fof(f678,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_16 ),
    inference(resolution,[],[f230,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f230,plain,
    ( r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f228])).

fof(f691,plain,
    ( ~ spl5_21
    | spl5_32
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f690,f228,f127,f122,f117,f112,f504,f288])).

fof(f690,plain,
    ( r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f689,f129])).

fof(f689,plain,
    ( r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f688,f124])).

fof(f688,plain,
    ( r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f687,f119])).

fof(f687,plain,
    ( r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f677,f114])).

fof(f677,plain,
    ( r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_16 ),
    inference(resolution,[],[f230,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f668,plain,
    ( spl5_16
    | ~ spl5_3
    | spl5_12 ),
    inference(avatar_split_clause,[],[f654,f194,f107,f228])).

fof(f107,plain,
    ( spl5_3
  <=> m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f194,plain,
    ( spl5_12
  <=> v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f654,plain,
    ( r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl5_3
    | spl5_12 ),
    inference(unit_resulting_resolution,[],[f109,f195,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f195,plain,
    ( ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f194])).

fof(f109,plain,
    ( m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f482,plain,
    ( ~ spl5_20
    | spl5_23
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f481,f198,f127,f122,f117,f112,f328,f280])).

fof(f198,plain,
    ( spl5_13
  <=> r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f481,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f480,f129])).

fof(f480,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f479,f124])).

fof(f479,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f478,f119])).

fof(f478,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f470,f114])).

fof(f470,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_13 ),
    inference(resolution,[],[f200,f62])).

fof(f200,plain,
    ( r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f198])).

fof(f440,plain,
    ( spl5_13
    | ~ spl5_2
    | spl5_12 ),
    inference(avatar_split_clause,[],[f434,f194,f102,f198])).

fof(f102,plain,
    ( spl5_2
  <=> m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f434,plain,
    ( r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl5_2
    | spl5_12 ),
    inference(unit_resulting_resolution,[],[f104,f195,f67])).

fof(f104,plain,
    ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f432,plain,
    ( ~ spl5_12
    | ~ spl5_3
    | spl5_17 ),
    inference(avatar_split_clause,[],[f428,f233,f107,f194])).

fof(f428,plain,
    ( ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl5_3
    | spl5_17 ),
    inference(unit_resulting_resolution,[],[f109,f234,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f234,plain,
    ( ~ v1_xboole_0(sK2)
    | spl5_17 ),
    inference(avatar_component_clause,[],[f233])).

fof(f291,plain,
    ( spl5_21
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f284,f218,f127,f122,f117,f112,f288])).

fof(f284,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f129,f124,f119,f114,f220,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f283,plain,
    ( spl5_20
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f276,f184,f127,f122,f117,f112,f280])).

fof(f184,plain,
    ( spl5_11
  <=> m1_connsp_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f276,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f129,f124,f119,f114,f186,f72])).

fof(f186,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f184])).

fof(f258,plain,
    ( ~ spl5_18
    | spl5_1 ),
    inference(avatar_split_clause,[],[f245,f97,f252])).

fof(f97,plain,
    ( spl5_1
  <=> m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f245,plain,
    ( ~ r2_hidden(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))
    | spl5_1 ),
    inference(resolution,[],[f99,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f99,plain,
    ( ~ m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f226,plain,
    ( spl5_15
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f225,f127,f122,f117,f112,f107,f218])).

fof(f225,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(subsumption_resolution,[],[f224,f129])).

fof(f224,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | v2_struct_0(sK0)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f223,f124])).

fof(f223,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f222,f119])).

fof(f222,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f208,f114])).

fof(f208,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(resolution,[],[f109,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
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
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_waybel_9)).

fof(f192,plain,
    ( spl5_11
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f191,f127,f122,f117,f112,f102,f184])).

fof(f191,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(subsumption_resolution,[],[f190,f129])).

fof(f190,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f189,f124])).

fof(f189,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f188,f119])).

fof(f188,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f174,f114])).

fof(f174,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f104,f64])).

fof(f130,plain,(
    ~ spl5_7 ),
    inference(avatar_split_clause,[],[f52,f127])).

fof(f52,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))
    & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    & m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f42,f41,f40,f39])).

fof(f39,plain,
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

fof(f40,plain,
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

fof(f41,plain,
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

fof(f42,plain,
    ( ? [X3] :
        ( ~ m1_subset_1(k2_xboole_0(sK2,X3),u1_struct_0(k9_yellow_6(sK0,sK1)))
        & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1))) )
   => ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))
      & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_waybel_9)).

fof(f125,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f53,f122])).

fof(f53,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f120,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f54,f117])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f115,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f55,f112])).

fof(f55,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f110,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f56,f107])).

fof(f56,plain,(
    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f105,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f57,f102])).

fof(f57,plain,(
    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f100,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f84,f97])).

fof(f84,plain,(
    ~ m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(definition_unfolding,[],[f58,f66])).

fof(f58,plain,(
    ~ m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:35:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (20863)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (20854)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (20862)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (20871)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (20855)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (20848)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (20851)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (20866)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (20870)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (20859)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (20859)Refutation not found, incomplete strategy% (20859)------------------------------
% 0.22/0.55  % (20859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (20859)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (20859)Memory used [KB]: 10618
% 0.22/0.55  % (20859)Time elapsed: 0.135 s
% 0.22/0.55  % (20859)------------------------------
% 0.22/0.55  % (20859)------------------------------
% 0.22/0.55  % (20877)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (20861)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (20874)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (20853)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (20872)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (20873)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (20852)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.55  % (20870)Refutation not found, incomplete strategy% (20870)------------------------------
% 0.22/0.55  % (20870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (20870)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (20870)Memory used [KB]: 10874
% 0.22/0.55  % (20870)Time elapsed: 0.140 s
% 0.22/0.55  % (20864)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (20870)------------------------------
% 0.22/0.55  % (20870)------------------------------
% 0.22/0.55  % (20865)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (20876)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (20858)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (20875)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.56  % (20867)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (20850)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.56  % (20860)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (20856)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (20858)Refutation not found, incomplete strategy% (20858)------------------------------
% 0.22/0.56  % (20858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (20858)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (20858)Memory used [KB]: 10618
% 0.22/0.56  % (20858)Time elapsed: 0.148 s
% 0.22/0.56  % (20858)------------------------------
% 0.22/0.56  % (20858)------------------------------
% 0.22/0.56  % (20868)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.59/0.57  % (20869)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.59/0.57  % (20849)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.70/0.58  % (20857)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.70/0.58  % (20865)Refutation not found, incomplete strategy% (20865)------------------------------
% 1.70/0.58  % (20865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.58  % (20865)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.58  
% 1.70/0.58  % (20865)Memory used [KB]: 10618
% 1.70/0.58  % (20865)Time elapsed: 0.133 s
% 1.70/0.58  % (20865)------------------------------
% 1.70/0.58  % (20865)------------------------------
% 1.70/0.61  % (20873)Refutation found. Thanks to Tanya!
% 1.70/0.61  % SZS status Theorem for theBenchmark
% 1.70/0.61  % SZS output start Proof for theBenchmark
% 1.70/0.61  fof(f1325,plain,(
% 1.70/0.61    $false),
% 1.70/0.61    inference(avatar_sat_refutation,[],[f100,f105,f110,f115,f120,f125,f130,f192,f226,f258,f283,f291,f432,f440,f482,f668,f691,f696,f731,f813,f1080,f1108,f1126,f1138,f1322])).
% 1.70/0.61  fof(f1322,plain,(
% 1.70/0.61    ~spl5_32 | spl5_45),
% 1.70/0.61    inference(avatar_contradiction_clause,[],[f1321])).
% 1.70/0.61  fof(f1321,plain,(
% 1.70/0.61    $false | (~spl5_32 | spl5_45)),
% 1.70/0.61    inference(subsumption_resolution,[],[f1305,f506])).
% 1.70/0.61  fof(f506,plain,(
% 1.70/0.61    r2_hidden(sK1,sK2) | ~spl5_32),
% 1.70/0.61    inference(avatar_component_clause,[],[f504])).
% 1.70/0.61  fof(f504,plain,(
% 1.70/0.61    spl5_32 <=> r2_hidden(sK1,sK2)),
% 1.70/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 1.70/0.61  fof(f1305,plain,(
% 1.70/0.61    ~r2_hidden(sK1,sK2) | spl5_45),
% 1.70/0.61    inference(resolution,[],[f726,f94])).
% 1.70/0.61  fof(f94,plain,(
% 1.70/0.61    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k2_tarski(X0,X1))) | ~r2_hidden(X4,X0)) )),
% 1.70/0.61    inference(equality_resolution,[],[f91])).
% 1.70/0.61  fof(f91,plain,(
% 1.70/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k2_tarski(X0,X1)) != X2) )),
% 1.70/0.61    inference(definition_unfolding,[],[f78,f66])).
% 1.70/0.61  fof(f66,plain,(
% 1.70/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.70/0.61    inference(cnf_transformation,[],[f2])).
% 1.70/0.61  fof(f2,axiom,(
% 1.70/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.70/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.70/0.61  fof(f78,plain,(
% 1.70/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 1.70/0.61    inference(cnf_transformation,[],[f51])).
% 1.70/0.61  fof(f51,plain,(
% 1.70/0.61    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.70/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f49,f50])).
% 1.70/0.61  fof(f50,plain,(
% 1.70/0.61    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.70/0.61    introduced(choice_axiom,[])).
% 1.70/0.61  fof(f49,plain,(
% 1.70/0.61    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.70/0.61    inference(rectify,[],[f48])).
% 1.70/0.61  fof(f48,plain,(
% 1.70/0.61    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.70/0.61    inference(flattening,[],[f47])).
% 1.70/0.61  fof(f47,plain,(
% 1.70/0.61    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.70/0.61    inference(nnf_transformation,[],[f1])).
% 1.70/0.61  fof(f1,axiom,(
% 1.70/0.61    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.70/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.70/0.61  fof(f726,plain,(
% 1.70/0.61    ~r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3))) | spl5_45),
% 1.70/0.61    inference(avatar_component_clause,[],[f724])).
% 1.70/0.61  fof(f724,plain,(
% 1.70/0.61    spl5_45 <=> r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3)))),
% 1.70/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 1.70/0.61  fof(f1138,plain,(
% 1.70/0.61    k3_tarski(k2_tarski(sK2,sK3)) != k4_subset_1(u1_struct_0(sK0),sK2,sK3) | m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.70/0.61    introduced(theory_tautology_sat_conflict,[])).
% 1.70/0.61  fof(f1126,plain,(
% 1.70/0.61    spl5_46 | ~spl5_5 | ~spl5_6 | ~spl5_20 | ~spl5_21 | ~spl5_23 | ~spl5_33),
% 1.70/0.61    inference(avatar_split_clause,[],[f1023,f513,f328,f288,f280,f122,f117,f728])).
% 1.70/0.61  fof(f728,plain,(
% 1.70/0.61    spl5_46 <=> v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0)),
% 1.70/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 1.70/0.61  fof(f117,plain,(
% 1.70/0.61    spl5_5 <=> l1_pre_topc(sK0)),
% 1.70/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.70/0.61  fof(f122,plain,(
% 1.70/0.61    spl5_6 <=> v2_pre_topc(sK0)),
% 1.70/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.70/0.61  fof(f280,plain,(
% 1.70/0.61    spl5_20 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.70/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.70/0.61  fof(f288,plain,(
% 1.70/0.61    spl5_21 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.70/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 1.70/0.61  fof(f328,plain,(
% 1.70/0.61    spl5_23 <=> v3_pre_topc(sK3,sK0)),
% 1.70/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 1.70/0.61  fof(f513,plain,(
% 1.70/0.61    spl5_33 <=> v3_pre_topc(sK2,sK0)),
% 1.70/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 1.70/0.61  fof(f1023,plain,(
% 1.70/0.61    v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0) | (~spl5_5 | ~spl5_6 | ~spl5_20 | ~spl5_21 | ~spl5_23 | ~spl5_33)),
% 1.70/0.61    inference(unit_resulting_resolution,[],[f124,f119,f515,f330,f282,f290,f85])).
% 1.70/0.61  fof(f85,plain,(
% 1.70/0.61    ( ! [X2,X0,X1] : (v3_pre_topc(k3_tarski(k2_tarski(X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.70/0.61    inference(definition_unfolding,[],[f73,f66])).
% 1.70/0.61  fof(f73,plain,(
% 1.70/0.61    ( ! [X2,X0,X1] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f31])).
% 1.70/0.61  fof(f31,plain,(
% 1.70/0.61    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.70/0.61    inference(flattening,[],[f30])).
% 1.70/0.61  fof(f30,plain,(
% 1.70/0.61    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.70/0.61    inference(ennf_transformation,[],[f11])).
% 1.70/0.61  fof(f11,axiom,(
% 1.70/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_xboole_0(X1,X2),X0))),
% 1.70/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_tops_1)).
% 1.70/0.61  fof(f290,plain,(
% 1.70/0.61    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_21),
% 1.70/0.61    inference(avatar_component_clause,[],[f288])).
% 1.70/0.61  fof(f282,plain,(
% 1.70/0.61    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_20),
% 1.70/0.61    inference(avatar_component_clause,[],[f280])).
% 1.70/0.61  fof(f330,plain,(
% 1.70/0.61    v3_pre_topc(sK3,sK0) | ~spl5_23),
% 1.70/0.61    inference(avatar_component_clause,[],[f328])).
% 1.70/0.61  fof(f515,plain,(
% 1.70/0.61    v3_pre_topc(sK2,sK0) | ~spl5_33),
% 1.70/0.61    inference(avatar_component_clause,[],[f513])).
% 1.70/0.61  fof(f119,plain,(
% 1.70/0.61    l1_pre_topc(sK0) | ~spl5_5),
% 1.70/0.61    inference(avatar_component_clause,[],[f117])).
% 1.70/0.61  fof(f124,plain,(
% 1.70/0.61    v2_pre_topc(sK0) | ~spl5_6),
% 1.70/0.61    inference(avatar_component_clause,[],[f122])).
% 1.70/0.61  fof(f1108,plain,(
% 1.70/0.61    spl5_80 | ~spl5_20 | ~spl5_21),
% 1.70/0.61    inference(avatar_split_clause,[],[f1033,f288,f280,f1105])).
% 1.70/0.61  fof(f1105,plain,(
% 1.70/0.61    spl5_80 <=> k3_tarski(k2_tarski(sK2,sK3)) = k4_subset_1(u1_struct_0(sK0),sK2,sK3)),
% 1.70/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).
% 1.70/0.61  fof(f1033,plain,(
% 1.70/0.61    k3_tarski(k2_tarski(sK2,sK3)) = k4_subset_1(u1_struct_0(sK0),sK2,sK3) | (~spl5_20 | ~spl5_21)),
% 1.70/0.61    inference(unit_resulting_resolution,[],[f282,f290,f86])).
% 1.70/0.61  fof(f86,plain,(
% 1.70/0.61    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.70/0.61    inference(definition_unfolding,[],[f76,f66])).
% 1.70/0.61  fof(f76,plain,(
% 1.70/0.61    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.70/0.61    inference(cnf_transformation,[],[f37])).
% 1.70/0.61  fof(f37,plain,(
% 1.70/0.61    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.70/0.61    inference(flattening,[],[f36])).
% 1.70/0.61  fof(f36,plain,(
% 1.70/0.61    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.70/0.61    inference(ennf_transformation,[],[f7])).
% 1.70/0.61  fof(f7,axiom,(
% 1.70/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.70/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.70/0.61  fof(f1080,plain,(
% 1.70/0.61    spl5_75 | ~spl5_20 | ~spl5_21),
% 1.70/0.61    inference(avatar_split_clause,[],[f1039,f288,f280,f1077])).
% 1.70/0.61  fof(f1077,plain,(
% 1.70/0.61    spl5_75 <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.70/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).
% 1.70/0.61  fof(f1039,plain,(
% 1.70/0.61    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_20 | ~spl5_21)),
% 1.70/0.61    inference(unit_resulting_resolution,[],[f282,f290,f75])).
% 1.70/0.61  fof(f75,plain,(
% 1.70/0.61    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.70/0.61    inference(cnf_transformation,[],[f35])).
% 1.70/0.61  fof(f35,plain,(
% 1.70/0.61    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.70/0.61    inference(flattening,[],[f34])).
% 1.70/0.61  fof(f34,plain,(
% 1.70/0.61    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.70/0.61    inference(ennf_transformation,[],[f6])).
% 1.70/0.61  fof(f6,axiom,(
% 1.70/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.70/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 1.70/0.61  fof(f813,plain,(
% 1.70/0.61    ~spl5_21 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_15 | ~spl5_17),
% 1.70/0.61    inference(avatar_split_clause,[],[f792,f233,f218,f127,f122,f117,f112,f288])).
% 1.70/0.61  fof(f112,plain,(
% 1.70/0.61    spl5_4 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.70/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.70/0.61  fof(f127,plain,(
% 1.70/0.61    spl5_7 <=> v2_struct_0(sK0)),
% 1.70/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.70/0.61  fof(f218,plain,(
% 1.70/0.61    spl5_15 <=> m1_connsp_2(sK2,sK0,sK1)),
% 1.70/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.70/0.61  fof(f233,plain,(
% 1.70/0.61    spl5_17 <=> v1_xboole_0(sK2)),
% 1.70/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.70/0.61  fof(f792,plain,(
% 1.70/0.61    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_15 | ~spl5_17)),
% 1.70/0.61    inference(unit_resulting_resolution,[],[f129,f124,f119,f220,f114,f422,f65])).
% 1.70/0.61  fof(f65,plain,(
% 1.70/0.61    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f25])).
% 1.70/0.61  fof(f25,plain,(
% 1.70/0.61    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.70/0.61    inference(flattening,[],[f24])).
% 1.70/0.61  fof(f24,plain,(
% 1.70/0.61    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.70/0.61    inference(ennf_transformation,[],[f13])).
% 1.70/0.61  fof(f13,axiom,(
% 1.70/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 1.70/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).
% 1.70/0.61  fof(f422,plain,(
% 1.70/0.61    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl5_17),
% 1.70/0.61    inference(forward_demodulation,[],[f397,f59])).
% 1.70/0.61  fof(f59,plain,(
% 1.70/0.61    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.70/0.61    inference(cnf_transformation,[],[f4])).
% 1.70/0.61  fof(f4,axiom,(
% 1.70/0.61    ! [X0] : k2_subset_1(X0) = X0),
% 1.70/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.70/0.61  fof(f397,plain,(
% 1.70/0.61    ( ! [X0] : (~r2_hidden(X0,k2_subset_1(sK2))) ) | ~spl5_17),
% 1.70/0.61    inference(unit_resulting_resolution,[],[f60,f235,f83])).
% 1.70/0.61  fof(f83,plain,(
% 1.70/0.61    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f38])).
% 1.70/0.61  fof(f38,plain,(
% 1.70/0.61    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.70/0.61    inference(ennf_transformation,[],[f10])).
% 1.70/0.61  fof(f10,axiom,(
% 1.70/0.61    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.70/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.70/0.61  fof(f235,plain,(
% 1.70/0.61    v1_xboole_0(sK2) | ~spl5_17),
% 1.70/0.61    inference(avatar_component_clause,[],[f233])).
% 1.70/0.61  fof(f60,plain,(
% 1.70/0.61    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.70/0.61    inference(cnf_transformation,[],[f5])).
% 1.70/0.61  fof(f5,axiom,(
% 1.70/0.61    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.70/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.70/0.61  fof(f114,plain,(
% 1.70/0.61    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_4),
% 1.70/0.61    inference(avatar_component_clause,[],[f112])).
% 1.70/0.61  fof(f220,plain,(
% 1.70/0.61    m1_connsp_2(sK2,sK0,sK1) | ~spl5_15),
% 1.70/0.61    inference(avatar_component_clause,[],[f218])).
% 1.70/0.61  fof(f129,plain,(
% 1.70/0.61    ~v2_struct_0(sK0) | spl5_7),
% 1.70/0.61    inference(avatar_component_clause,[],[f127])).
% 1.70/0.61  fof(f731,plain,(
% 1.70/0.61    ~spl5_44 | ~spl5_45 | ~spl5_46 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | spl5_18),
% 1.70/0.61    inference(avatar_split_clause,[],[f718,f252,f127,f122,f117,f112,f728,f724,f720])).
% 1.70/0.61  fof(f720,plain,(
% 1.70/0.61    spl5_44 <=> m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.70/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 1.70/0.61  fof(f252,plain,(
% 1.70/0.61    spl5_18 <=> r2_hidden(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.70/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.70/0.61  fof(f718,plain,(
% 1.70/0.61    ~v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0) | ~r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3))) | ~m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | spl5_18)),
% 1.70/0.61    inference(subsumption_resolution,[],[f717,f129])).
% 1.70/0.61  fof(f717,plain,(
% 1.70/0.61    ~v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0) | ~r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3))) | ~m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_18)),
% 1.70/0.61    inference(subsumption_resolution,[],[f716,f124])).
% 1.70/0.61  fof(f716,plain,(
% 1.70/0.61    ~v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0) | ~r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3))) | ~m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5 | spl5_18)),
% 1.70/0.61    inference(subsumption_resolution,[],[f715,f119])).
% 1.70/0.61  fof(f715,plain,(
% 1.70/0.61    ~v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0) | ~r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3))) | ~m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_4 | spl5_18)),
% 1.70/0.61    inference(subsumption_resolution,[],[f700,f114])).
% 1.70/0.61  fof(f700,plain,(
% 1.70/0.61    ~v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0) | ~r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3))) | ~m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl5_18),
% 1.70/0.61    inference(resolution,[],[f254,f63])).
% 1.70/0.61  fof(f63,plain,(
% 1.70/0.61    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f45])).
% 1.70/0.61  fof(f45,plain,(
% 1.70/0.61    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2)) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.70/0.61    inference(flattening,[],[f44])).
% 1.70/0.61  fof(f44,plain,(
% 1.70/0.61    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | (~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2))) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.70/0.61    inference(nnf_transformation,[],[f21])).
% 1.70/0.61  fof(f21,plain,(
% 1.70/0.61    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.70/0.61    inference(flattening,[],[f20])).
% 1.70/0.61  fof(f20,plain,(
% 1.70/0.61    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.70/0.61    inference(ennf_transformation,[],[f14])).
% 1.70/0.61  fof(f14,axiom,(
% 1.70/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 1.70/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_6)).
% 1.70/0.61  fof(f254,plain,(
% 1.70/0.61    ~r2_hidden(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) | spl5_18),
% 1.70/0.61    inference(avatar_component_clause,[],[f252])).
% 1.70/0.61  fof(f696,plain,(
% 1.70/0.61    ~spl5_21 | spl5_33 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_16),
% 1.70/0.61    inference(avatar_split_clause,[],[f695,f228,f127,f122,f117,f112,f513,f288])).
% 1.70/0.61  fof(f228,plain,(
% 1.70/0.61    spl5_16 <=> r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.70/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.70/0.61  fof(f695,plain,(
% 1.70/0.61    v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_16)),
% 1.70/0.61    inference(subsumption_resolution,[],[f694,f129])).
% 1.70/0.61  fof(f694,plain,(
% 1.70/0.61    v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_16)),
% 1.70/0.61    inference(subsumption_resolution,[],[f693,f124])).
% 1.70/0.61  fof(f693,plain,(
% 1.70/0.61    v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5 | ~spl5_16)),
% 1.70/0.61    inference(subsumption_resolution,[],[f692,f119])).
% 1.70/0.61  fof(f692,plain,(
% 1.70/0.61    v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_16)),
% 1.70/0.61    inference(subsumption_resolution,[],[f678,f114])).
% 1.70/0.61  fof(f678,plain,(
% 1.70/0.61    v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_16),
% 1.70/0.61    inference(resolution,[],[f230,f62])).
% 1.70/0.61  fof(f62,plain,(
% 1.70/0.61    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f45])).
% 1.70/0.61  fof(f230,plain,(
% 1.70/0.61    r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl5_16),
% 1.70/0.61    inference(avatar_component_clause,[],[f228])).
% 1.70/0.61  fof(f691,plain,(
% 1.70/0.61    ~spl5_21 | spl5_32 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_16),
% 1.70/0.61    inference(avatar_split_clause,[],[f690,f228,f127,f122,f117,f112,f504,f288])).
% 1.70/0.61  fof(f690,plain,(
% 1.70/0.61    r2_hidden(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_16)),
% 1.70/0.61    inference(subsumption_resolution,[],[f689,f129])).
% 1.70/0.61  fof(f689,plain,(
% 1.70/0.61    r2_hidden(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_16)),
% 1.70/0.61    inference(subsumption_resolution,[],[f688,f124])).
% 1.70/0.61  fof(f688,plain,(
% 1.70/0.61    r2_hidden(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5 | ~spl5_16)),
% 1.70/0.61    inference(subsumption_resolution,[],[f687,f119])).
% 1.70/0.61  fof(f687,plain,(
% 1.70/0.61    r2_hidden(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_16)),
% 1.70/0.61    inference(subsumption_resolution,[],[f677,f114])).
% 1.70/0.61  fof(f677,plain,(
% 1.70/0.61    r2_hidden(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_16),
% 1.70/0.61    inference(resolution,[],[f230,f61])).
% 1.70/0.61  fof(f61,plain,(
% 1.70/0.61    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f45])).
% 1.70/0.61  fof(f668,plain,(
% 1.70/0.61    spl5_16 | ~spl5_3 | spl5_12),
% 1.70/0.61    inference(avatar_split_clause,[],[f654,f194,f107,f228])).
% 1.70/0.61  fof(f107,plain,(
% 1.70/0.61    spl5_3 <=> m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.70/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.70/0.61  fof(f194,plain,(
% 1.70/0.61    spl5_12 <=> v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.70/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.70/0.61  fof(f654,plain,(
% 1.70/0.61    r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | (~spl5_3 | spl5_12)),
% 1.70/0.61    inference(unit_resulting_resolution,[],[f109,f195,f67])).
% 1.70/0.61  fof(f67,plain,(
% 1.70/0.61    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f46])).
% 1.70/0.61  fof(f46,plain,(
% 1.70/0.61    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.70/0.61    inference(nnf_transformation,[],[f26])).
% 1.70/0.61  fof(f26,plain,(
% 1.70/0.61    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.70/0.61    inference(ennf_transformation,[],[f3])).
% 1.70/0.61  fof(f3,axiom,(
% 1.70/0.61    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.70/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.70/0.61  fof(f195,plain,(
% 1.70/0.61    ~v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) | spl5_12),
% 1.70/0.61    inference(avatar_component_clause,[],[f194])).
% 1.70/0.61  fof(f109,plain,(
% 1.70/0.61    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl5_3),
% 1.70/0.61    inference(avatar_component_clause,[],[f107])).
% 1.70/0.61  fof(f482,plain,(
% 1.70/0.61    ~spl5_20 | spl5_23 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_13),
% 1.70/0.61    inference(avatar_split_clause,[],[f481,f198,f127,f122,f117,f112,f328,f280])).
% 1.70/0.61  fof(f198,plain,(
% 1.70/0.61    spl5_13 <=> r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.70/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.70/0.61  fof(f481,plain,(
% 1.70/0.61    v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_13)),
% 1.70/0.61    inference(subsumption_resolution,[],[f480,f129])).
% 1.70/0.61  fof(f480,plain,(
% 1.70/0.61    v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_13)),
% 1.70/0.61    inference(subsumption_resolution,[],[f479,f124])).
% 1.70/0.61  fof(f479,plain,(
% 1.70/0.61    v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5 | ~spl5_13)),
% 1.70/0.61    inference(subsumption_resolution,[],[f478,f119])).
% 1.70/0.61  fof(f478,plain,(
% 1.70/0.61    v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_13)),
% 1.70/0.61    inference(subsumption_resolution,[],[f470,f114])).
% 1.70/0.61  fof(f470,plain,(
% 1.70/0.61    v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_13),
% 1.70/0.61    inference(resolution,[],[f200,f62])).
% 1.70/0.61  fof(f200,plain,(
% 1.70/0.61    r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl5_13),
% 1.70/0.61    inference(avatar_component_clause,[],[f198])).
% 1.70/0.61  fof(f440,plain,(
% 1.70/0.61    spl5_13 | ~spl5_2 | spl5_12),
% 1.70/0.61    inference(avatar_split_clause,[],[f434,f194,f102,f198])).
% 1.70/0.61  fof(f102,plain,(
% 1.70/0.61    spl5_2 <=> m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.70/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.70/0.61  fof(f434,plain,(
% 1.70/0.61    r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) | (~spl5_2 | spl5_12)),
% 1.70/0.61    inference(unit_resulting_resolution,[],[f104,f195,f67])).
% 1.70/0.61  fof(f104,plain,(
% 1.70/0.61    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl5_2),
% 1.70/0.61    inference(avatar_component_clause,[],[f102])).
% 1.70/0.61  fof(f432,plain,(
% 1.70/0.61    ~spl5_12 | ~spl5_3 | spl5_17),
% 1.70/0.61    inference(avatar_split_clause,[],[f428,f233,f107,f194])).
% 1.70/0.61  fof(f428,plain,(
% 1.70/0.61    ~v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) | (~spl5_3 | spl5_17)),
% 1.70/0.61    inference(unit_resulting_resolution,[],[f109,f234,f69])).
% 1.70/0.61  fof(f69,plain,(
% 1.70/0.61    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f46])).
% 1.70/0.61  fof(f234,plain,(
% 1.70/0.61    ~v1_xboole_0(sK2) | spl5_17),
% 1.70/0.61    inference(avatar_component_clause,[],[f233])).
% 1.70/0.61  fof(f291,plain,(
% 1.70/0.61    spl5_21 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_15),
% 1.70/0.61    inference(avatar_split_clause,[],[f284,f218,f127,f122,f117,f112,f288])).
% 1.70/0.61  fof(f284,plain,(
% 1.70/0.61    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_15)),
% 1.70/0.61    inference(unit_resulting_resolution,[],[f129,f124,f119,f114,f220,f72])).
% 1.70/0.61  fof(f72,plain,(
% 1.70/0.61    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f29])).
% 1.70/0.61  fof(f29,plain,(
% 1.70/0.61    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.70/0.61    inference(flattening,[],[f28])).
% 1.70/0.61  fof(f28,plain,(
% 1.70/0.61    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.70/0.61    inference(ennf_transformation,[],[f12])).
% 1.70/0.61  fof(f12,axiom,(
% 1.70/0.61    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.70/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 1.70/0.61  fof(f283,plain,(
% 1.70/0.61    spl5_20 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_11),
% 1.70/0.61    inference(avatar_split_clause,[],[f276,f184,f127,f122,f117,f112,f280])).
% 1.70/0.61  fof(f184,plain,(
% 1.70/0.61    spl5_11 <=> m1_connsp_2(sK3,sK0,sK1)),
% 1.70/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.70/0.61  fof(f276,plain,(
% 1.70/0.61    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_11)),
% 1.70/0.61    inference(unit_resulting_resolution,[],[f129,f124,f119,f114,f186,f72])).
% 1.70/0.61  fof(f186,plain,(
% 1.70/0.61    m1_connsp_2(sK3,sK0,sK1) | ~spl5_11),
% 1.70/0.61    inference(avatar_component_clause,[],[f184])).
% 1.70/0.61  fof(f258,plain,(
% 1.70/0.61    ~spl5_18 | spl5_1),
% 1.70/0.61    inference(avatar_split_clause,[],[f245,f97,f252])).
% 1.70/0.61  fof(f97,plain,(
% 1.70/0.61    spl5_1 <=> m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.70/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.70/0.61  fof(f245,plain,(
% 1.70/0.61    ~r2_hidden(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) | spl5_1),
% 1.70/0.61    inference(resolution,[],[f99,f71])).
% 1.70/0.61  fof(f71,plain,(
% 1.70/0.61    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f27])).
% 1.70/0.61  fof(f27,plain,(
% 1.70/0.61    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.70/0.61    inference(ennf_transformation,[],[f8])).
% 1.70/0.61  fof(f8,axiom,(
% 1.70/0.61    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.70/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.70/0.61  fof(f99,plain,(
% 1.70/0.61    ~m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) | spl5_1),
% 1.70/0.61    inference(avatar_component_clause,[],[f97])).
% 1.70/0.61  fof(f226,plain,(
% 1.70/0.61    spl5_15 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7),
% 1.70/0.61    inference(avatar_split_clause,[],[f225,f127,f122,f117,f112,f107,f218])).
% 1.70/0.61  fof(f225,plain,(
% 1.70/0.61    m1_connsp_2(sK2,sK0,sK1) | (~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7)),
% 1.70/0.61    inference(subsumption_resolution,[],[f224,f129])).
% 1.70/0.61  fof(f224,plain,(
% 1.70/0.61    m1_connsp_2(sK2,sK0,sK1) | v2_struct_0(sK0) | (~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 1.70/0.61    inference(subsumption_resolution,[],[f223,f124])).
% 1.70/0.61  fof(f223,plain,(
% 1.70/0.61    m1_connsp_2(sK2,sK0,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_3 | ~spl5_4 | ~spl5_5)),
% 1.70/0.61    inference(subsumption_resolution,[],[f222,f119])).
% 1.70/0.61  fof(f222,plain,(
% 1.70/0.61    m1_connsp_2(sK2,sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_3 | ~spl5_4)),
% 1.70/0.61    inference(subsumption_resolution,[],[f208,f114])).
% 1.70/0.61  fof(f208,plain,(
% 1.70/0.61    m1_connsp_2(sK2,sK0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_3),
% 1.70/0.61    inference(resolution,[],[f109,f64])).
% 1.70/0.61  fof(f64,plain,(
% 1.70/0.61    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f23])).
% 1.70/0.61  fof(f23,plain,(
% 1.70/0.61    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.70/0.61    inference(flattening,[],[f22])).
% 1.70/0.61  fof(f22,plain,(
% 1.70/0.61    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.70/0.61    inference(ennf_transformation,[],[f15])).
% 1.70/0.61  fof(f15,axiom,(
% 1.70/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => m1_connsp_2(X2,X0,X1))))),
% 1.70/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_waybel_9)).
% 1.70/0.61  fof(f192,plain,(
% 1.70/0.61    spl5_11 | ~spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7),
% 1.70/0.61    inference(avatar_split_clause,[],[f191,f127,f122,f117,f112,f102,f184])).
% 1.70/0.61  fof(f191,plain,(
% 1.70/0.61    m1_connsp_2(sK3,sK0,sK1) | (~spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7)),
% 1.70/0.61    inference(subsumption_resolution,[],[f190,f129])).
% 1.70/0.61  fof(f190,plain,(
% 1.70/0.61    m1_connsp_2(sK3,sK0,sK1) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 1.70/0.61    inference(subsumption_resolution,[],[f189,f124])).
% 1.70/0.61  fof(f189,plain,(
% 1.70/0.61    m1_connsp_2(sK3,sK0,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_4 | ~spl5_5)),
% 1.70/0.61    inference(subsumption_resolution,[],[f188,f119])).
% 1.70/0.61  fof(f188,plain,(
% 1.70/0.61    m1_connsp_2(sK3,sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_4)),
% 1.70/0.61    inference(subsumption_resolution,[],[f174,f114])).
% 1.70/0.61  fof(f174,plain,(
% 1.70/0.61    m1_connsp_2(sK3,sK0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_2),
% 1.70/0.61    inference(resolution,[],[f104,f64])).
% 1.70/0.61  fof(f130,plain,(
% 1.70/0.61    ~spl5_7),
% 1.70/0.61    inference(avatar_split_clause,[],[f52,f127])).
% 1.70/0.61  fof(f52,plain,(
% 1.70/0.61    ~v2_struct_0(sK0)),
% 1.70/0.61    inference(cnf_transformation,[],[f43])).
% 1.70/0.61  fof(f43,plain,(
% 1.70/0.61    (((~m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.70/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f42,f41,f40,f39])).
% 1.70/0.61  fof(f39,plain,(
% 1.70/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,X1)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.70/0.61    introduced(choice_axiom,[])).
% 1.70/0.61  fof(f40,plain,(
% 1.70/0.61    ? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,X1)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 1.70/0.61    introduced(choice_axiom,[])).
% 1.70/0.61  fof(f41,plain,(
% 1.70/0.61    ? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,sK1)))) => (? [X3] : (~m1_subset_1(k2_xboole_0(sK2,X3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))))),
% 1.70/0.61    introduced(choice_axiom,[])).
% 1.70/0.61  fof(f42,plain,(
% 1.70/0.61    ? [X3] : (~m1_subset_1(k2_xboole_0(sK2,X3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1)))) => (~m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))))),
% 1.70/0.61    introduced(choice_axiom,[])).
% 1.70/0.61  fof(f19,plain,(
% 1.70/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.70/0.61    inference(flattening,[],[f18])).
% 1.70/0.61  fof(f18,plain,(
% 1.70/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.70/0.61    inference(ennf_transformation,[],[f17])).
% 1.70/0.62  fof(f17,negated_conjecture,(
% 1.70/0.62    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 1.70/0.62    inference(negated_conjecture,[],[f16])).
% 1.70/0.62  fof(f16,conjecture,(
% 1.70/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 1.70/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_waybel_9)).
% 1.70/0.62  fof(f125,plain,(
% 1.70/0.62    spl5_6),
% 1.70/0.62    inference(avatar_split_clause,[],[f53,f122])).
% 1.70/0.62  fof(f53,plain,(
% 1.70/0.62    v2_pre_topc(sK0)),
% 1.70/0.62    inference(cnf_transformation,[],[f43])).
% 1.70/0.62  fof(f120,plain,(
% 1.70/0.62    spl5_5),
% 1.70/0.62    inference(avatar_split_clause,[],[f54,f117])).
% 1.70/0.62  fof(f54,plain,(
% 1.70/0.62    l1_pre_topc(sK0)),
% 1.70/0.62    inference(cnf_transformation,[],[f43])).
% 1.70/0.62  fof(f115,plain,(
% 1.70/0.62    spl5_4),
% 1.70/0.62    inference(avatar_split_clause,[],[f55,f112])).
% 1.70/0.62  fof(f55,plain,(
% 1.70/0.62    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.70/0.62    inference(cnf_transformation,[],[f43])).
% 1.70/0.62  fof(f110,plain,(
% 1.70/0.62    spl5_3),
% 1.70/0.62    inference(avatar_split_clause,[],[f56,f107])).
% 1.70/0.62  fof(f56,plain,(
% 1.70/0.62    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.70/0.62    inference(cnf_transformation,[],[f43])).
% 1.70/0.62  fof(f105,plain,(
% 1.70/0.62    spl5_2),
% 1.70/0.62    inference(avatar_split_clause,[],[f57,f102])).
% 1.70/0.62  fof(f57,plain,(
% 1.70/0.62    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.70/0.62    inference(cnf_transformation,[],[f43])).
% 1.70/0.62  fof(f100,plain,(
% 1.70/0.62    ~spl5_1),
% 1.70/0.62    inference(avatar_split_clause,[],[f84,f97])).
% 1.70/0.62  fof(f84,plain,(
% 1.70/0.62    ~m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.70/0.62    inference(definition_unfolding,[],[f58,f66])).
% 1.70/0.62  fof(f58,plain,(
% 1.70/0.62    ~m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.70/0.62    inference(cnf_transformation,[],[f43])).
% 1.70/0.62  % SZS output end Proof for theBenchmark
% 1.70/0.62  % (20873)------------------------------
% 1.70/0.62  % (20873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.62  % (20873)Termination reason: Refutation
% 1.70/0.62  
% 1.70/0.62  % (20873)Memory used [KB]: 7036
% 1.70/0.62  % (20873)Time elapsed: 0.161 s
% 1.70/0.62  % (20873)------------------------------
% 1.70/0.62  % (20873)------------------------------
% 1.70/0.62  % (20847)Success in time 0.257 s
%------------------------------------------------------------------------------
