%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : setfam_1__t17_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:13 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 378 expanded)
%              Number of leaves         :   46 ( 163 expanded)
%              Depth                    :   10
%              Number of atoms          :  376 (1003 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f448,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f74,f81,f91,f106,f121,f137,f144,f156,f169,f183,f192,f199,f206,f226,f252,f259,f266,f273,f287,f323,f340,f347,f370,f377,f384,f396,f407,f415,f447])).

fof(f447,plain,
    ( spl5_5
    | ~ spl5_56 ),
    inference(avatar_contradiction_clause,[],[f446])).

fof(f446,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_56 ),
    inference(subsumption_resolution,[],[f431,f435])).

fof(f435,plain,
    ( r2_hidden(sK4(sK1,sK3(sK0,sK1)),sK1)
    | ~ spl5_56 ),
    inference(unit_resulting_resolution,[],[f47,f414,f51])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X0)
      | r2_hidden(sK4(X1,X4),X1)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ( ! [X3] :
              ( ~ r1_tarski(sK3(X0,X1),X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X4] :
            ( ( r1_tarski(X4,sK4(X1,X4))
              & r2_hidden(sK4(X1,X4),X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f37,f39,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) )
     => ( ! [X3] :
            ( ~ r1_tarski(sK3(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X4,X1] :
      ( ? [X5] :
          ( r1_tarski(X4,X5)
          & r2_hidden(X5,X1) )
     => ( r1_tarski(X4,sK4(X1,X4))
        & r2_hidden(sK4(X1,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( r1_tarski(X4,X5)
                & r2_hidden(X5,X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( r1_tarski(X2,X3)
                & r2_hidden(X3,X1) )
            | ~ r2_hidden(X2,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t17_setfam_1.p',d2_setfam_1)).

fof(f414,plain,
    ( r2_hidden(sK3(sK0,sK1),sK1)
    | ~ spl5_56 ),
    inference(avatar_component_clause,[],[f413])).

fof(f413,plain,
    ( spl5_56
  <=> r2_hidden(sK3(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f47,plain,(
    ! [X0] : r1_setfam_1(X0,X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : r1_setfam_1(X0,X0) ),
    inference(rectify,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_setfam_1(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t17_setfam_1.p',reflexivity_r1_setfam_1)).

fof(f431,plain,
    ( ~ r2_hidden(sK4(sK1,sK3(sK0,sK1)),sK1)
    | ~ spl5_5
    | ~ spl5_56 ),
    inference(unit_resulting_resolution,[],[f47,f80,f414,f245])).

fof(f245,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r2_hidden(sK4(X5,sK3(X3,X4)),X4)
      | r1_setfam_1(X3,X4)
      | ~ r2_hidden(sK3(X3,X4),X6)
      | ~ r1_setfam_1(X6,X5) ) ),
    inference(resolution,[],[f54,f52])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( r1_tarski(X4,sK4(X1,X4))
      | ~ r2_hidden(X4,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(sK3(X0,X1),X3)
      | r1_setfam_1(X0,X1)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f80,plain,
    ( ~ r1_setfam_1(sK0,sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl5_5
  <=> ~ r1_setfam_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f415,plain,
    ( spl5_56
    | spl5_13
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f399,f394,f135,f413])).

fof(f135,plain,
    ( spl5_13
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f394,plain,
    ( spl5_52
  <=> m1_subset_1(sK3(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f399,plain,
    ( r2_hidden(sK3(sK0,sK1),sK1)
    | ~ spl5_13
    | ~ spl5_52 ),
    inference(unit_resulting_resolution,[],[f136,f395,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t17_setfam_1.p',t2_subset)).

fof(f395,plain,
    ( m1_subset_1(sK3(sK0,sK1),sK1)
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f394])).

fof(f136,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f135])).

fof(f407,plain,
    ( spl5_54
    | spl5_21 ),
    inference(avatar_split_clause,[],[f184,f181,f405])).

fof(f405,plain,
    ( spl5_54
  <=> r2_hidden(sK3(sK0,o_0_0_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f181,plain,
    ( spl5_21
  <=> ~ r1_setfam_1(sK0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f184,plain,
    ( r2_hidden(sK3(sK0,o_0_0_xboole_0),sK0)
    | ~ spl5_21 ),
    inference(unit_resulting_resolution,[],[f182,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f182,plain,
    ( ~ r1_setfam_1(sK0,o_0_0_xboole_0)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f181])).

fof(f396,plain,
    ( spl5_52
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f147,f119,f104,f394])).

fof(f104,plain,
    ( spl5_8
  <=> m1_subset_1(sK0,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f119,plain,
    ( spl5_10
  <=> r2_hidden(sK3(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f147,plain,
    ( m1_subset_1(sK3(sK0,sK1),sK1)
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f120,f105,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t17_setfam_1.p',t4_subset)).

fof(f105,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK1))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f104])).

fof(f120,plain,
    ( r2_hidden(sK3(sK0,sK1),sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f384,plain,
    ( ~ spl5_51
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f126,f119,f382])).

fof(f382,plain,
    ( spl5_51
  <=> ~ r2_hidden(sK0,sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f126,plain,
    ( ~ r2_hidden(sK0,sK3(sK0,sK1))
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f120,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t17_setfam_1.p',antisymmetry_r2_hidden)).

fof(f377,plain,
    ( spl5_48
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f124,f119,f375])).

fof(f375,plain,
    ( spl5_48
  <=> m1_subset_1(sK3(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f124,plain,
    ( m1_subset_1(sK3(sK0,sK1),sK0)
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f120,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t17_setfam_1.p',t1_subset)).

fof(f370,plain,
    ( ~ spl5_47
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f352,f345,f368])).

fof(f368,plain,
    ( spl5_47
  <=> ~ r2_hidden(sK1,sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f345,plain,
    ( spl5_44
  <=> r2_hidden(sK2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f352,plain,
    ( ~ r2_hidden(sK1,sK2(sK0))
    | ~ spl5_44 ),
    inference(unit_resulting_resolution,[],[f346,f48])).

fof(f346,plain,
    ( r2_hidden(sK2(sK0),sK1)
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f345])).

fof(f347,plain,
    ( spl5_44
    | spl5_13
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f332,f271,f135,f345])).

fof(f271,plain,
    ( spl5_36
  <=> m1_subset_1(sK2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f332,plain,
    ( r2_hidden(sK2(sK0),sK1)
    | ~ spl5_13
    | ~ spl5_36 ),
    inference(unit_resulting_resolution,[],[f136,f272,f50])).

fof(f272,plain,
    ( m1_subset_1(sK2(sK0),sK1)
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f271])).

fof(f340,plain,
    ( ~ spl5_43
    | spl5_33 ),
    inference(avatar_split_clause,[],[f313,f257,f338])).

fof(f338,plain,
    ( spl5_43
  <=> ~ r2_hidden(sK1,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f257,plain,
    ( spl5_33
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f313,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_33 ),
    inference(unit_resulting_resolution,[],[f258,f49])).

fof(f258,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f257])).

fof(f323,plain,
    ( ~ spl5_41
    | spl5_33 ),
    inference(avatar_split_clause,[],[f311,f257,f321])).

fof(f321,plain,
    ( spl5_41
  <=> ~ r1_tarski(sK1,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f311,plain,
    ( ~ r1_tarski(sK1,o_0_0_xboole_0)
    | ~ spl5_33 ),
    inference(unit_resulting_resolution,[],[f258,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t17_setfam_1.p',t3_subset)).

fof(f287,plain,
    ( spl5_38
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f274,f65,f285])).

fof(f285,plain,
    ( spl5_38
  <=> v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f65,plain,
    ( spl5_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f274,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_0 ),
    inference(unit_resulting_resolution,[],[f46,f114,f50])).

fof(f114,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_0 ),
    inference(unit_resulting_resolution,[],[f66,f46,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t17_setfam_1.p',t5_subset)).

fof(f66,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f65])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t17_setfam_1.p',existence_m1_subset_1)).

fof(f273,plain,
    ( spl5_36
    | ~ spl5_8
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f236,f197,f104,f271])).

fof(f197,plain,
    ( spl5_24
  <=> r2_hidden(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f236,plain,
    ( m1_subset_1(sK2(sK0),sK1)
    | ~ spl5_8
    | ~ spl5_24 ),
    inference(unit_resulting_resolution,[],[f105,f198,f59])).

fof(f198,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f197])).

fof(f266,plain,
    ( ~ spl5_35
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f230,f197,f264])).

fof(f264,plain,
    ( spl5_35
  <=> ~ r2_hidden(sK0,sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f230,plain,
    ( ~ r2_hidden(sK0,sK2(sK0))
    | ~ spl5_24 ),
    inference(unit_resulting_resolution,[],[f198,f48])).

fof(f259,plain,
    ( ~ spl5_33
    | ~ spl5_0
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f215,f190,f65,f257])).

fof(f190,plain,
    ( spl5_22
  <=> r2_hidden(sK2(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f215,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_0
    | ~ spl5_22 ),
    inference(unit_resulting_resolution,[],[f66,f191,f60])).

fof(f191,plain,
    ( r2_hidden(sK2(sK1),sK1)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f190])).

fof(f252,plain,
    ( ~ spl5_31
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f209,f190,f250])).

fof(f250,plain,
    ( spl5_31
  <=> ~ r2_hidden(sK1,sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f209,plain,
    ( ~ r2_hidden(sK1,sK2(sK1))
    | ~ spl5_22 ),
    inference(unit_resulting_resolution,[],[f191,f48])).

fof(f226,plain,
    ( ~ spl5_29
    | ~ spl5_0
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f212,f190,f65,f224])).

fof(f224,plain,
    ( spl5_29
  <=> ~ r1_setfam_1(sK1,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f212,plain,
    ( ~ r1_setfam_1(sK1,o_0_0_xboole_0)
    | ~ spl5_0
    | ~ spl5_22 ),
    inference(unit_resulting_resolution,[],[f92,f191,f51])).

fof(f92,plain,
    ( ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0)
    | ~ spl5_0 ),
    inference(unit_resulting_resolution,[],[f66,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t17_setfam_1.p',t7_boole)).

fof(f206,plain,
    ( ~ spl5_27
    | spl5_17 ),
    inference(avatar_split_clause,[],[f159,f154,f204])).

fof(f204,plain,
    ( spl5_27
  <=> ~ r2_hidden(sK0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f154,plain,
    ( spl5_17
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f159,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_17 ),
    inference(unit_resulting_resolution,[],[f155,f49])).

fof(f155,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f154])).

fof(f199,plain,
    ( spl5_24
    | spl5_15 ),
    inference(avatar_split_clause,[],[f148,f142,f197])).

fof(f142,plain,
    ( spl5_15
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f148,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f46,f143,f50])).

fof(f143,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f142])).

fof(f192,plain,
    ( spl5_22
    | spl5_13 ),
    inference(avatar_split_clause,[],[f145,f135,f190])).

fof(f145,plain,
    ( r2_hidden(sK2(sK1),sK1)
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f46,f136,f50])).

fof(f183,plain,
    ( ~ spl5_21
    | ~ spl5_0
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f173,f119,f65,f181])).

fof(f173,plain,
    ( ~ r1_setfam_1(sK0,o_0_0_xboole_0)
    | ~ spl5_0
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f120,f92,f51])).

fof(f169,plain,
    ( ~ spl5_19
    | spl5_17 ),
    inference(avatar_split_clause,[],[f157,f154,f167])).

fof(f167,plain,
    ( spl5_19
  <=> ~ r1_tarski(sK0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f157,plain,
    ( ~ r1_tarski(sK0,o_0_0_xboole_0)
    | ~ spl5_17 ),
    inference(unit_resulting_resolution,[],[f155,f56])).

fof(f156,plain,
    ( ~ spl5_17
    | ~ spl5_0
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f122,f119,f65,f154])).

fof(f122,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_0
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f66,f120,f60])).

fof(f144,plain,
    ( ~ spl5_15
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f127,f119,f142])).

fof(f127,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f120,f58])).

fof(f137,plain,
    ( ~ spl5_13
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f123,f119,f104,f135])).

fof(f123,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f105,f120,f60])).

fof(f121,plain,
    ( spl5_10
    | spl5_5 ),
    inference(avatar_split_clause,[],[f111,f79,f119])).

fof(f111,plain,
    ( r2_hidden(sK3(sK0,sK1),sK0)
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f80,f53])).

fof(f106,plain,
    ( spl5_8
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f96,f72,f104])).

fof(f72,plain,
    ( spl5_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f96,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK1))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f73,f56])).

fof(f73,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f91,plain,
    ( spl5_6
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f82,f65,f89])).

fof(f89,plain,
    ( spl5_6
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f82,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl5_0 ),
    inference(unit_resulting_resolution,[],[f66,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t17_setfam_1.p',t6_boole)).

fof(f81,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f43,f79])).

fof(f43,plain,(
    ~ r1_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ r1_setfam_1(sK0,sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f32])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ~ r1_setfam_1(X0,X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_setfam_1(sK0,sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => r1_setfam_1(X0,X1) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t17_setfam_1.p',t17_setfam_1)).

fof(f74,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f42,f72])).

fof(f42,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f67,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f44,f65])).

fof(f44,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t17_setfam_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
