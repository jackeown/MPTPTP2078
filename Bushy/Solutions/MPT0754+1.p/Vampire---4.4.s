%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : ordinal1__t47_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:27 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 172 expanded)
%              Number of leaves         :   23 (  69 expanded)
%              Depth                    :    7
%              Number of atoms          :  249 ( 775 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f187,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f76,f83,f90,f97,f104,f114,f127,f140,f150,f157,f170,f180,f182,f184,f186])).

fof(f186,plain,
    ( ~ spl4_8
    | ~ spl4_18
    | spl4_21 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | ~ spl4_8
    | ~ spl4_18
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f172,f156])).

fof(f156,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl4_21
  <=> ~ r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f172,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(unit_resulting_resolution,[],[f149,f96,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t47_ordinal1.p',t1_xboole_1)).

fof(f96,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl4_8
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f149,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl4_18
  <=> r1_tarski(k2_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f184,plain,
    ( ~ spl4_8
    | ~ spl4_18
    | spl4_21 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | ~ spl4_8
    | ~ spl4_18
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f175,f149])).

fof(f175,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK0)
    | ~ spl4_8
    | ~ spl4_21 ),
    inference(unit_resulting_resolution,[],[f96,f156,f61])).

fof(f182,plain,
    ( ~ spl4_8
    | ~ spl4_18
    | spl4_21 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | ~ spl4_8
    | ~ spl4_18
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f177,f96])).

fof(f177,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl4_18
    | ~ spl4_21 ),
    inference(unit_resulting_resolution,[],[f149,f156,f61])).

fof(f180,plain,
    ( ~ spl4_8
    | ~ spl4_18
    | spl4_21 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | ~ spl4_8
    | ~ spl4_18
    | ~ spl4_21 ),
    inference(unit_resulting_resolution,[],[f96,f149,f156,f61])).

fof(f170,plain,
    ( spl4_22
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f159,f148,f168])).

fof(f168,plain,
    ( spl4_22
  <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f159,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl4_18 ),
    inference(unit_resulting_resolution,[],[f149,f57])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t47_ordinal1.p',t3_subset)).

fof(f157,plain,
    ( ~ spl4_21
    | ~ spl4_0
    | spl4_17 ),
    inference(avatar_split_clause,[],[f142,f138,f67,f155])).

fof(f67,plain,
    ( spl4_0
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f138,plain,
    ( spl4_17
  <=> ~ v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f142,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl4_0
    | ~ spl4_17 ),
    inference(unit_resulting_resolution,[],[f139,f68,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t47_ordinal1.p',d19_relat_1)).

fof(f68,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f67])).

fof(f139,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f138])).

fof(f150,plain,
    ( spl4_18
    | ~ spl4_0
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f141,f102,f67,f148])).

fof(f102,plain,
    ( spl4_10
  <=> v5_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f141,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ spl4_0
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f68,f103,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f103,plain,
    ( v5_relat_1(sK2,sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f102])).

fof(f140,plain,
    ( ~ spl4_1
    | ~ spl4_17
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f47,f78,f71,f138,f64])).

fof(f64,plain,
    ( spl4_1
  <=> ~ v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f71,plain,
    ( spl4_3
  <=> ~ v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f78,plain,
    ( spl4_5
  <=> ~ v5_ordinal1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f47,plain,
    ( ~ v5_ordinal1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v5_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( ~ v5_ordinal1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v5_relat_1(sK2,sK1)
      | ~ v1_relat_1(sK2) )
    & v5_ordinal1(sK2)
    & v1_funct_1(sK2)
    & v5_relat_1(sK2,sK0)
    & v1_relat_1(sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f36,f35])).

fof(f35,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ v5_ordinal1(X2)
              | ~ v1_funct_1(X2)
              | ~ v5_relat_1(X2,X1)
              | ~ v1_relat_1(X2) )
            & v5_ordinal1(X2)
            & v1_funct_1(X2)
            & v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
        & r1_tarski(X0,X1) )
   => ( ? [X2] :
          ( ( ~ v5_ordinal1(X2)
            | ~ v1_funct_1(X2)
            | ~ v5_relat_1(X2,sK1)
            | ~ v1_relat_1(X2) )
          & v5_ordinal1(X2)
          & v1_funct_1(X2)
          & v5_relat_1(X2,sK0)
          & v1_relat_1(X2) )
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ v5_ordinal1(X2)
            | ~ v1_funct_1(X2)
            | ~ v5_relat_1(X2,X1)
            | ~ v1_relat_1(X2) )
          & v5_ordinal1(X2)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
     => ( ( ~ v5_ordinal1(sK2)
          | ~ v1_funct_1(sK2)
          | ~ v5_relat_1(sK2,X1)
          | ~ v1_relat_1(sK2) )
        & v5_ordinal1(sK2)
        & v1_funct_1(sK2)
        & v5_relat_1(sK2,X0)
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ v5_ordinal1(X2)
            | ~ v1_funct_1(X2)
            | ~ v5_relat_1(X2,X1)
            | ~ v1_relat_1(X2) )
          & v5_ordinal1(X2)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ v5_ordinal1(X2)
            | ~ v1_funct_1(X2)
            | ~ v5_relat_1(X2,X1)
            | ~ v1_relat_1(X2) )
          & v5_ordinal1(X2)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => ! [X2] :
            ( ( v5_ordinal1(X2)
              & v1_funct_1(X2)
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
           => ( v5_ordinal1(X2)
              & v1_funct_1(X2)
              & v5_relat_1(X2,X1)
              & v1_relat_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v5_ordinal1(X2)
            & v1_funct_1(X2)
            & v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => ( v5_ordinal1(X2)
            & v1_funct_1(X2)
            & v5_relat_1(X2,X1)
            & v1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t47_ordinal1.p',t47_ordinal1)).

fof(f127,plain,
    ( spl4_14
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f119,f95,f125])).

fof(f125,plain,
    ( spl4_14
  <=> m1_subset_1(sK0,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f119,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK1))
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f96,f57])).

fof(f114,plain,
    ( spl4_12
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f105,f88,f112])).

fof(f112,plain,
    ( spl4_12
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f88,plain,
    ( spl4_6
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f105,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f89,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t47_ordinal1.p',t6_boole)).

fof(f89,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f104,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f44,f102])).

fof(f44,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f97,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f42,f95])).

fof(f42,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f90,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f48,f88])).

fof(f48,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t47_ordinal1.p',dt_o_0_0_xboole_0)).

fof(f83,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f46,f81])).

fof(f81,plain,
    ( spl4_4
  <=> v5_ordinal1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f46,plain,(
    v5_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f76,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f45,f74])).

fof(f74,plain,
    ( spl4_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f45,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f69,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f43,f67])).

fof(f43,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
