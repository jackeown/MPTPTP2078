%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : connsp_2__t36_connsp_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:53 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 412 expanded)
%              Number of leaves         :   47 ( 175 expanded)
%              Depth                    :    8
%              Number of atoms          :  471 (1158 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f392,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f106,f113,f120,f127,f134,f145,f152,f163,f179,f190,f202,f212,f226,f233,f245,f255,f262,f275,f282,f295,f306,f318,f337,f344,f355,f367,f376,f389,f391])).

fof(f391,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_50
    | ~ spl6_54 ),
    inference(avatar_contradiction_clause,[],[f390])).

fof(f390,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_50
    | ~ spl6_54 ),
    inference(subsumption_resolution,[],[f382,f377])).

fof(f377,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK2))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_50 ),
    inference(unit_resulting_resolution,[],[f98,f105,f126,f133,f354,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_connsp_2(X2,X0,X1)
                  | ~ r1_tarski(X1,k1_tops_1(X0,X2)) )
                & ( r1_tarski(X1,k1_tops_1(X0,X2))
                  | ~ m2_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t36_connsp_2.p',d2_connsp_2)).

fof(f354,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f353])).

fof(f353,plain,
    ( spl6_50
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f133,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl6_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f126,plain,
    ( m2_connsp_2(sK2,sK0,sK1)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl6_8
  <=> m2_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f105,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl6_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f98,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl6_0
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f382,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK2))
    | ~ spl6_7
    | ~ spl6_54 ),
    inference(unit_resulting_resolution,[],[f375,f172])).

fof(f172,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | ~ r1_tarski(X0,sK2) )
    | ~ spl6_7 ),
    inference(resolution,[],[f90,f119])).

fof(f119,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl6_7
  <=> ~ r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t36_connsp_2.p',t1_xboole_1)).

fof(f375,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f374])).

fof(f374,plain,
    ( spl6_54
  <=> r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f389,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_50
    | ~ spl6_54 ),
    inference(avatar_contradiction_clause,[],[f388])).

fof(f388,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_50
    | ~ spl6_54 ),
    inference(subsumption_resolution,[],[f384,f377])).

fof(f384,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK2))
    | ~ spl6_7
    | ~ spl6_54 ),
    inference(unit_resulting_resolution,[],[f119,f375,f90])).

fof(f376,plain,
    ( spl6_54
    | ~ spl6_2
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f359,f353,f104,f374])).

fof(f359,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl6_2
    | ~ spl6_50 ),
    inference(unit_resulting_resolution,[],[f105,f354,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t36_connsp_2.p',t44_tops_1)).

fof(f367,plain,
    ( spl6_52
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f360,f353,f365])).

fof(f365,plain,
    ( spl6_52
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f360,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl6_50 ),
    inference(unit_resulting_resolution,[],[f354,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t36_connsp_2.p',t3_subset)).

fof(f355,plain,
    ( spl6_50
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f345,f132,f125,f104,f97,f353])).

fof(f345,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f98,f105,f126,f133,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X2] :
          ( m2_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t36_connsp_2.p',dt_m2_connsp_2)).

fof(f344,plain,
    ( spl6_48
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f324,f316,f132,f104,f342])).

fof(f342,plain,
    ( spl6_48
  <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f316,plain,
    ( spl6_44
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f324,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_44 ),
    inference(forward_demodulation,[],[f322,f309])).

fof(f309,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1))
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f105,f133,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t36_connsp_2.p',projectivity_k1_tops_1)).

fof(f322,plain,
    ( r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ spl6_2
    | ~ spl6_44 ),
    inference(unit_resulting_resolution,[],[f105,f317,f74])).

fof(f317,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f316])).

fof(f337,plain,
    ( spl6_46
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f247,f243,f335])).

fof(f335,plain,
    ( spl6_46
  <=> r1_tarski(sK3(k1_zfmisc_1(k1_tops_1(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f243,plain,
    ( spl6_30
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f247,plain,
    ( r1_tarski(sK3(k1_zfmisc_1(k1_tops_1(sK0,sK1))),sK1)
    | ~ spl6_30 ),
    inference(unit_resulting_resolution,[],[f136,f244,f90])).

fof(f244,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f243])).

fof(f136,plain,(
    ! [X0] : r1_tarski(sK3(k1_zfmisc_1(X0)),X0) ),
    inference(unit_resulting_resolution,[],[f77,f85])).

fof(f77,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t36_connsp_2.p',existence_m1_subset_1)).

fof(f318,plain,
    ( spl6_44
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f265,f132,f104,f316])).

fof(f265,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f105,f133,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t36_connsp_2.p',dt_k1_tops_1)).

fof(f306,plain,
    ( ~ spl6_43
    | spl6_39 ),
    inference(avatar_split_clause,[],[f298,f280,f304])).

fof(f304,plain,
    ( spl6_43
  <=> ~ r2_hidden(sK1,k1_zfmisc_1(sK3(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f280,plain,
    ( spl6_39
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(sK3(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f298,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))
    | ~ spl6_39 ),
    inference(unit_resulting_resolution,[],[f281,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t36_connsp_2.p',t1_subset)).

fof(f281,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f280])).

fof(f295,plain,
    ( spl6_40
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f288,f132,f104,f97,f293])).

fof(f293,plain,
    ( spl6_40
  <=> m2_connsp_2(sK4(sK0,sK1),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f288,plain,
    ( m2_connsp_2(sK4(sK0,sK1),sK0,sK1)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f98,f105,f133,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m2_connsp_2(sK4(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m2_connsp_2(sK4(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f44,f63])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X2] : m2_connsp_2(X2,X0,X1)
     => m2_connsp_2(sK4(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ? [X2] : m2_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t36_connsp_2.p',existence_m2_connsp_2)).

fof(f282,plain,
    ( ~ spl6_39
    | spl6_21 ),
    inference(avatar_split_clause,[],[f193,f188,f280])).

fof(f188,plain,
    ( spl6_21
  <=> ~ r1_tarski(sK1,sK3(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f193,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f189,f85])).

fof(f189,plain,
    ( ~ r1_tarski(sK1,sK3(k1_zfmisc_1(sK2)))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f188])).

fof(f275,plain,
    ( ~ spl6_37
    | spl6_19 ),
    inference(avatar_split_clause,[],[f180,f177,f273])).

fof(f273,plain,
    ( spl6_37
  <=> ~ r1_tarski(u1_struct_0(sK0),sK3(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f177,plain,
    ( spl6_19
  <=> ~ r1_tarski(u1_struct_0(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f180,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),sK3(k1_zfmisc_1(sK2)))
    | ~ spl6_19 ),
    inference(unit_resulting_resolution,[],[f136,f178,f90])).

fof(f178,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),sK2)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f177])).

fof(f262,plain,
    ( spl6_34
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f248,f243,f260])).

fof(f260,plain,
    ( spl6_34
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f248,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl6_30 ),
    inference(unit_resulting_resolution,[],[f244,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f255,plain,
    ( spl6_32
    | ~ spl6_14
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f246,f243,f150,f253])).

fof(f253,plain,
    ( spl6_32
  <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f150,plain,
    ( spl6_14
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f246,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl6_14
    | ~ spl6_30 ),
    inference(unit_resulting_resolution,[],[f151,f244,f90])).

fof(f151,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f150])).

fof(f245,plain,
    ( spl6_30
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f238,f132,f104,f243])).

fof(f238,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f105,f133,f74])).

fof(f233,plain,
    ( ~ spl6_29
    | spl6_13 ),
    inference(avatar_split_clause,[],[f213,f143,f231])).

fof(f231,plain,
    ( spl6_29
  <=> ~ r2_hidden(sK1,sK3(k1_zfmisc_1(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f143,plain,
    ( spl6_13
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f213,plain,
    ( ~ r2_hidden(sK1,sK3(k1_zfmisc_1(k1_zfmisc_1(sK2))))
    | ~ spl6_13 ),
    inference(unit_resulting_resolution,[],[f144,f77,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t36_connsp_2.p',t4_subset)).

fof(f144,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f143])).

fof(f226,plain,
    ( spl6_26
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f168,f150,f224])).

fof(f224,plain,
    ( spl6_26
  <=> r1_tarski(sK3(k1_zfmisc_1(sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f168,plain,
    ( r1_tarski(sK3(k1_zfmisc_1(sK1)),u1_struct_0(sK0))
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f136,f151,f90])).

fof(f212,plain,
    ( ~ spl6_25
    | spl6_23 ),
    inference(avatar_split_clause,[],[f204,f200,f210])).

fof(f210,plain,
    ( spl6_25
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f200,plain,
    ( spl6_23
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f204,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(sK2))
    | ~ spl6_23 ),
    inference(unit_resulting_resolution,[],[f201,f79])).

fof(f201,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(sK2))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f200])).

fof(f202,plain,
    ( ~ spl6_23
    | spl6_19 ),
    inference(avatar_split_clause,[],[f181,f177,f200])).

fof(f181,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(sK2))
    | ~ spl6_19 ),
    inference(unit_resulting_resolution,[],[f178,f85])).

fof(f190,plain,
    ( ~ spl6_21
    | spl6_7 ),
    inference(avatar_split_clause,[],[f171,f118,f188])).

fof(f171,plain,
    ( ~ r1_tarski(sK1,sK3(k1_zfmisc_1(sK2)))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f136,f119,f90])).

fof(f179,plain,
    ( ~ spl6_19
    | spl6_7
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f170,f150,f118,f177])).

fof(f170,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),sK2)
    | ~ spl6_7
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f151,f119,f90])).

fof(f163,plain,
    ( ~ spl6_17
    | spl6_13 ),
    inference(avatar_split_clause,[],[f154,f143,f161])).

fof(f161,plain,
    ( spl6_17
  <=> ~ r2_hidden(sK1,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f154,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK2))
    | ~ spl6_13 ),
    inference(unit_resulting_resolution,[],[f144,f79])).

fof(f152,plain,
    ( spl6_14
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f137,f132,f150])).

fof(f137,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f133,f85])).

fof(f145,plain,
    ( ~ spl6_13
    | spl6_7 ),
    inference(avatar_split_clause,[],[f135,f118,f143])).

fof(f135,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f119,f85])).

fof(f134,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f70,f132])).

fof(f70,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,
    ( ~ r1_tarski(sK1,sK2)
    & m2_connsp_2(sK2,sK0,sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f58,f57,f56])).

fof(f56,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(X1,X2)
                & m2_connsp_2(X2,X0,X1) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,X2)
              & m2_connsp_2(X2,sK0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,X2)
              & m2_connsp_2(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r1_tarski(sK1,X2)
            & m2_connsp_2(X2,X0,sK1) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & m2_connsp_2(X2,X0,X1) )
     => ( ~ r1_tarski(X1,sK2)
        & m2_connsp_2(sK2,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,X2)
              & m2_connsp_2(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,X2)
              & m2_connsp_2(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m2_connsp_2(X2,X0,X1)
               => r1_tarski(X1,X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m2_connsp_2(X2,X0,X1)
               => r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_connsp_2(X2,X0,X1)
             => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t36_connsp_2.p',t36_connsp_2)).

fof(f127,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f71,f125])).

fof(f71,plain,(
    m2_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f120,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f72,f118])).

fof(f72,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f113,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f92,f111])).

fof(f111,plain,
    ( spl6_4
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f92,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    l1_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f13,f66])).

fof(f66,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK5) ),
    introduced(choice_axiom,[])).

fof(f13,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t36_connsp_2.p',existence_l1_pre_topc)).

fof(f106,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f69,f104])).

fof(f69,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f99,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f68,f97])).

fof(f68,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).
%------------------------------------------------------------------------------
