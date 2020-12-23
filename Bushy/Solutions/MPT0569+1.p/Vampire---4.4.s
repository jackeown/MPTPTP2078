%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t173_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:54 EDT 2019

% Result     : Theorem 1.91s
% Output     : Refutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 175 expanded)
%              Number of leaves         :   26 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :  301 ( 501 expanded)
%              Number of equality atoms :   25 (  38 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1119,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f106,f151,f454,f458,f465,f471,f472,f681,f685,f692,f1077,f1118])).

fof(f1118,plain,
    ( ~ spl10_0
    | ~ spl10_2
    | spl10_5
    | ~ spl10_22
    | ~ spl10_64 ),
    inference(avatar_contradiction_clause,[],[f1117])).

fof(f1117,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_22
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f1116,f1059])).

fof(f1059,plain,
    ( r2_hidden(sK3(k2_relat_1(sK1),sK0),k2_relat_1(sK1))
    | ~ spl10_64 ),
    inference(avatar_component_clause,[],[f1058])).

fof(f1058,plain,
    ( spl10_64
  <=> r2_hidden(sK3(k2_relat_1(sK1),sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_64])])).

fof(f1116,plain,
    ( ~ r2_hidden(sK3(k2_relat_1(sK1),sK0),k2_relat_1(sK1))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_22 ),
    inference(resolution,[],[f1084,f102])).

fof(f102,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl10_5
  <=> ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f1084,plain,
    ( ! [X6] :
        ( r1_xboole_0(X6,sK0)
        | ~ r2_hidden(sK3(X6,sK0),k2_relat_1(sK1)) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_22 ),
    inference(resolution,[],[f729,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t173_relat_1.p',t3_xboole_0)).

fof(f729,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK0)
        | ~ r2_hidden(X2,k2_relat_1(sK1)) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f724,f79])).

fof(f79,plain,(
    ! [X2,X0] :
      ( sP5(X2,X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( sP5(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t173_relat_1.p',d5_relat_1)).

fof(f724,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK0)
        | ~ r2_hidden(X2,k2_relat_1(sK1))
        | ~ sP5(X2,sK1) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_22 ),
    inference(resolution,[],[f700,f60])).

fof(f60,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK6(X0,X2),X2),X0)
      | ~ sP5(X2,X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f700,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ r2_hidden(X1,sK0)
        | ~ r2_hidden(X1,k2_relat_1(sK1)) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f698,f473])).

fof(f473,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl10_22 ),
    inference(resolution,[],[f283,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t173_relat_1.p',t7_boole)).

fof(f283,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f282])).

fof(f282,plain,
    ( spl10_22
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f698,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k1_xboole_0)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ r2_hidden(X1,sK0)
        | ~ r2_hidden(X1,k2_relat_1(sK1)) )
    | ~ spl10_0
    | ~ spl10_2 ),
    inference(superposition,[],[f93,f99])).

fof(f99,plain,
    ( k10_relat_1(sK1,sK0) = k1_xboole_0
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl10_2
  <=> k10_relat_1(sK1,sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f93,plain,
    ( ! [X6,X8,X7] :
        ( r2_hidden(X7,k10_relat_1(sK1,X8))
        | ~ r2_hidden(k4_tarski(X7,X6),sK1)
        | ~ r2_hidden(X6,X8)
        | ~ r2_hidden(X6,k2_relat_1(sK1)) )
    | ~ spl10_0 ),
    inference(resolution,[],[f88,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t173_relat_1.p',t166_relat_1)).

fof(f88,plain,
    ( v1_relat_1(sK1)
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl10_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f1077,plain,
    ( spl10_5
    | spl10_65 ),
    inference(avatar_contradiction_clause,[],[f1076])).

fof(f1076,plain,
    ( $false
    | ~ spl10_5
    | ~ spl10_65 ),
    inference(subsumption_resolution,[],[f1071,f102])).

fof(f1071,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl10_65 ),
    inference(resolution,[],[f1062,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1062,plain,
    ( ~ r2_hidden(sK3(k2_relat_1(sK1),sK0),k2_relat_1(sK1))
    | ~ spl10_65 ),
    inference(avatar_component_clause,[],[f1061])).

fof(f1061,plain,
    ( spl10_65
  <=> ~ r2_hidden(sK3(k2_relat_1(sK1),sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_65])])).

fof(f692,plain,
    ( spl10_3
    | ~ spl10_44 ),
    inference(avatar_contradiction_clause,[],[f691])).

fof(f691,plain,
    ( $false
    | ~ spl10_3
    | ~ spl10_44 ),
    inference(subsumption_resolution,[],[f690,f96])).

fof(f96,plain,
    ( k10_relat_1(sK1,sK0) != k1_xboole_0
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl10_3
  <=> k10_relat_1(sK1,sK0) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f690,plain,
    ( k10_relat_1(sK1,sK0) = k1_xboole_0
    | ~ spl10_44 ),
    inference(resolution,[],[f680,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t173_relat_1.p',t6_boole)).

fof(f680,plain,
    ( v1_xboole_0(k10_relat_1(sK1,sK0))
    | ~ spl10_44 ),
    inference(avatar_component_clause,[],[f679])).

fof(f679,plain,
    ( spl10_44
  <=> v1_xboole_0(k10_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).

fof(f685,plain,(
    ~ spl10_42 ),
    inference(avatar_contradiction_clause,[],[f682])).

fof(f682,plain,
    ( $false
    | ~ spl10_42 ),
    inference(resolution,[],[f674,f47])).

fof(f47,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t173_relat_1.p',existence_m1_subset_1)).

fof(f674,plain,
    ( ! [X6] : ~ m1_subset_1(X6,k10_relat_1(sK1,sK0))
    | ~ spl10_42 ),
    inference(avatar_component_clause,[],[f673])).

fof(f673,plain,
    ( spl10_42
  <=> ! [X6] : ~ m1_subset_1(X6,k10_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f681,plain,
    ( spl10_42
    | spl10_44
    | ~ spl10_0
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f518,f104,f87,f679,f673])).

fof(f104,plain,
    ( spl10_4
  <=> r1_xboole_0(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f518,plain,
    ( ! [X6] :
        ( v1_xboole_0(k10_relat_1(sK1,sK0))
        | ~ m1_subset_1(X6,k10_relat_1(sK1,sK0)) )
    | ~ spl10_0
    | ~ spl10_4 ),
    inference(resolution,[],[f514,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t173_relat_1.p',t2_subset)).

fof(f514,plain,
    ( ! [X8] : ~ r2_hidden(X8,k10_relat_1(sK1,sK0))
    | ~ spl10_0
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f511,f90])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK7(X0,X1,sK1),k2_relat_1(sK1))
        | ~ r2_hidden(X0,k10_relat_1(sK1,X1)) )
    | ~ spl10_0 ),
    inference(resolution,[],[f88,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK7(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f511,plain,
    ( ! [X8] :
        ( ~ r2_hidden(sK7(X8,sK0,sK1),k2_relat_1(sK1))
        | ~ r2_hidden(X8,k10_relat_1(sK1,sK0)) )
    | ~ spl10_0
    | ~ spl10_4 ),
    inference(resolution,[],[f468,f92])).

fof(f92,plain,
    ( ! [X4,X5] :
        ( r2_hidden(sK7(X4,X5,sK1),X5)
        | ~ r2_hidden(X4,k10_relat_1(sK1,X5)) )
    | ~ spl10_0 ),
    inference(resolution,[],[f88,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK7(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f468,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl10_4 ),
    inference(resolution,[],[f105,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f105,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f472,plain,
    ( k10_relat_1(sK1,k1_xboole_0) != k1_xboole_0
    | v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(k10_relat_1(sK1,k1_xboole_0)) ),
    introduced(theory_axiom,[])).

fof(f471,plain,(
    spl10_27 ),
    inference(avatar_contradiction_clause,[],[f470])).

fof(f470,plain,
    ( $false
    | ~ spl10_27 ),
    inference(subsumption_resolution,[],[f469,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t173_relat_1.p',t2_boole)).

fof(f469,plain,
    ( k1_xboole_0 != k3_xboole_0(k2_relat_1(sK1),k1_xboole_0)
    | ~ spl10_27 ),
    inference(resolution,[],[f310,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k1_xboole_0 = k3_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t173_relat_1.p',d7_xboole_0)).

fof(f310,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),k1_xboole_0)
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f309])).

fof(f309,plain,
    ( spl10_27
  <=> ~ r1_xboole_0(k2_relat_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f465,plain,
    ( spl10_25
    | ~ spl10_36 ),
    inference(avatar_contradiction_clause,[],[f464])).

fof(f464,plain,
    ( $false
    | ~ spl10_25
    | ~ spl10_36 ),
    inference(subsumption_resolution,[],[f463,f288])).

fof(f288,plain,
    ( k10_relat_1(sK1,k1_xboole_0) != k1_xboole_0
    | ~ spl10_25 ),
    inference(avatar_component_clause,[],[f287])).

fof(f287,plain,
    ( spl10_25
  <=> k10_relat_1(sK1,k1_xboole_0) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f463,plain,
    ( k10_relat_1(sK1,k1_xboole_0) = k1_xboole_0
    | ~ spl10_36 ),
    inference(resolution,[],[f453,f46])).

fof(f453,plain,
    ( v1_xboole_0(k10_relat_1(sK1,k1_xboole_0))
    | ~ spl10_36 ),
    inference(avatar_component_clause,[],[f452])).

fof(f452,plain,
    ( spl10_36
  <=> v1_xboole_0(k10_relat_1(sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f458,plain,(
    ~ spl10_34 ),
    inference(avatar_contradiction_clause,[],[f455])).

fof(f455,plain,
    ( $false
    | ~ spl10_34 ),
    inference(resolution,[],[f447,f47])).

fof(f447,plain,
    ( ! [X6] : ~ m1_subset_1(X6,k10_relat_1(sK1,k1_xboole_0))
    | ~ spl10_34 ),
    inference(avatar_component_clause,[],[f446])).

fof(f446,plain,
    ( spl10_34
  <=> ! [X6] : ~ m1_subset_1(X6,k10_relat_1(sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f454,plain,
    ( spl10_34
    | spl10_36
    | ~ spl10_0
    | ~ spl10_26 ),
    inference(avatar_split_clause,[],[f345,f312,f87,f452,f446])).

fof(f312,plain,
    ( spl10_26
  <=> r1_xboole_0(k2_relat_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f345,plain,
    ( ! [X6] :
        ( v1_xboole_0(k10_relat_1(sK1,k1_xboole_0))
        | ~ m1_subset_1(X6,k10_relat_1(sK1,k1_xboole_0)) )
    | ~ spl10_0
    | ~ spl10_26 ),
    inference(resolution,[],[f340,f55])).

fof(f340,plain,
    ( ! [X8] : ~ r2_hidden(X8,k10_relat_1(sK1,k1_xboole_0))
    | ~ spl10_0
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f337,f90])).

fof(f337,plain,
    ( ! [X8] :
        ( ~ r2_hidden(sK7(X8,k1_xboole_0,sK1),k2_relat_1(sK1))
        | ~ r2_hidden(X8,k10_relat_1(sK1,k1_xboole_0)) )
    | ~ spl10_0
    | ~ spl10_26 ),
    inference(resolution,[],[f317,f92])).

fof(f317,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl10_26 ),
    inference(resolution,[],[f313,f50])).

fof(f313,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k1_xboole_0)
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f312])).

fof(f151,plain,
    ( ~ spl10_2
    | ~ spl10_4 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f149,f99])).

fof(f149,plain,
    ( k10_relat_1(sK1,sK0) != k1_xboole_0
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f42,f105])).

fof(f42,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | k10_relat_1(sK1,sK0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( k10_relat_1(X1,X0) = k1_xboole_0
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k10_relat_1(X1,X0) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t173_relat_1.p',t173_relat_1)).

fof(f106,plain,
    ( spl10_2
    | spl10_4 ),
    inference(avatar_split_clause,[],[f41,f104,f98])).

fof(f41,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | k10_relat_1(sK1,sK0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

fof(f89,plain,(
    spl10_0 ),
    inference(avatar_split_clause,[],[f43,f87])).

fof(f43,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
