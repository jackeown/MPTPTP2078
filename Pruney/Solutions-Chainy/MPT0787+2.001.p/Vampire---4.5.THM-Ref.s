%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:03 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 214 expanded)
%              Number of leaves         :   30 (  91 expanded)
%              Depth                    :   11
%              Number of atoms          :  382 ( 671 expanded)
%              Number of equality atoms :   31 (  50 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1039,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f102,f103,f109,f127,f274,f476,f478,f499,f502,f512,f946,f948,f973,f1020,f1032,f1038])).

fof(f1038,plain,
    ( sK0 != sK1
    | r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(k4_tarski(sK1,sK1),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1032,plain,
    ( ~ spl8_4
    | ~ spl8_94 ),
    inference(avatar_split_clause,[],[f1028,f1017,f90])).

fof(f90,plain,
    ( spl8_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f1017,plain,
    ( spl8_94
  <=> r2_hidden(sK1,k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_94])])).

fof(f1028,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl8_94 ),
    inference(resolution,[],[f1019,f71])).

fof(f71,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_wellord1(X0,X3))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,X2)
      | k1_wellord1(X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | X1 != X3
      | ~ r2_hidden(X3,X2)
      | k1_wellord1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

fof(f1019,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK1))
    | ~ spl8_94 ),
    inference(avatar_component_clause,[],[f1017])).

fof(f1020,plain,
    ( spl8_94
    | ~ spl8_6
    | ~ spl8_45 ),
    inference(avatar_split_clause,[],[f1009,f449,f99,f1017])).

fof(f99,plain,
    ( spl8_6
  <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f449,plain,
    ( spl8_45
  <=> r2_hidden(sK1,k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f1009,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK1))
    | ~ spl8_6
    | ~ spl8_45 ),
    inference(resolution,[],[f976,f100])).

fof(f100,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f976,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_wellord1(sK2,sK0),X0)
        | r2_hidden(sK1,X0) )
    | ~ spl8_45 ),
    inference(resolution,[],[f451,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f451,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ spl8_45 ),
    inference(avatar_component_clause,[],[f449])).

fof(f973,plain,
    ( spl8_45
    | ~ spl8_4
    | spl8_32
    | ~ spl8_33 ),
    inference(avatar_split_clause,[],[f970,f394,f390,f90,f449])).

fof(f390,plain,
    ( spl8_32
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f394,plain,
    ( spl8_33
  <=> r2_hidden(k4_tarski(sK1,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f970,plain,
    ( sK0 = sK1
    | ~ v1_relat_1(sK2)
    | r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ spl8_33 ),
    inference(resolution,[],[f396,f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X1),X0)
      | X1 = X3
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | X1 = X3
      | ~ r2_hidden(k4_tarski(X3,X1),X0)
      | r2_hidden(X3,X2)
      | k1_wellord1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f396,plain,
    ( r2_hidden(k4_tarski(sK1,sK0),sK2)
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f394])).

fof(f948,plain,
    ( spl8_32
    | spl8_5
    | spl8_33
    | ~ spl8_1
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f530,f272,f75,f394,f95,f390])).

fof(f95,plain,
    ( spl8_5
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f75,plain,
    ( spl8_1
  <=> r2_hidden(sK1,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f272,plain,
    ( spl8_20
  <=> ! [X1] :
        ( ~ r2_hidden(X1,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(X1,sK0),sK2)
        | r2_hidden(k4_tarski(sK0,X1),sK2)
        | sK0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f530,plain,
    ( r2_hidden(k4_tarski(sK1,sK0),sK2)
    | r2_hidden(k4_tarski(sK0,sK1),sK2)
    | sK0 = sK1
    | ~ spl8_1
    | ~ spl8_20 ),
    inference(resolution,[],[f273,f77])).

fof(f77,plain,
    ( r2_hidden(sK1,k3_relat_1(sK2))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f273,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(X1,sK0),sK2)
        | r2_hidden(k4_tarski(sK0,X1),sK2)
        | sK0 = X1 )
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f272])).

fof(f946,plain,
    ( spl8_6
    | ~ spl8_4
    | ~ spl8_50 ),
    inference(avatar_split_clause,[],[f945,f509,f90,f99])).

fof(f509,plain,
    ( spl8_50
  <=> k1_wellord1(sK2,sK0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f945,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl8_4
    | ~ spl8_50 ),
    inference(superposition,[],[f932,f511])).

fof(f511,plain,
    ( k1_wellord1(sK2,sK0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),sK0)
    | ~ spl8_50 ),
    inference(avatar_component_clause,[],[f509])).

fof(f932,plain,
    ( ! [X0,X1] : r1_tarski(k1_wellord1(k2_wellord1(sK2,X0),X1),X0)
    | ~ spl8_4 ),
    inference(resolution,[],[f183,f709])).

fof(f709,plain,
    ( ! [X0] : r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X0)
    | ~ spl8_4 ),
    inference(duplicate_literal_removal,[],[f698])).

fof(f698,plain,
    ( ! [X0] :
        ( r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X0)
        | r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X0) )
    | ~ spl8_4 ),
    inference(resolution,[],[f310,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f310,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK7(k3_relat_1(k2_wellord1(sK2,X0)),X1),X0)
        | r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X1) )
    | ~ spl8_4 ),
    inference(resolution,[],[f191,f92])).

fof(f92,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f191,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK7(k3_relat_1(k2_wellord1(X0,X1)),X2),X1)
      | r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X2) ) ),
    inference(resolution,[],[f65,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_wellord1)).

fof(f183,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X1)
        | r1_tarski(k1_wellord1(k2_wellord1(sK2,X0),X2),X1) )
    | ~ spl8_4 ),
    inference(resolution,[],[f138,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f138,plain,
    ( ! [X2,X1] : r1_tarski(k1_wellord1(k2_wellord1(sK2,X1),X2),k3_relat_1(k2_wellord1(sK2,X1)))
    | ~ spl8_4 ),
    inference(resolution,[],[f57,f134])).

fof(f134,plain,
    ( ! [X0] : v1_relat_1(k2_wellord1(sK2,X0))
    | ~ spl8_4 ),
    inference(resolution,[],[f56,f92])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k2_wellord1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_wellord1)).

fof(f512,plain,
    ( spl8_50
    | ~ spl8_4
    | ~ spl8_3
    | ~ spl8_46 ),
    inference(avatar_split_clause,[],[f505,f456,f85,f90,f509])).

fof(f85,plain,
    ( spl8_3
  <=> v2_wellord1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f456,plain,
    ( spl8_46
  <=> r2_hidden(sK0,k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f505,plain,
    ( ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_wellord1(sK2,sK0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),sK0)
    | ~ spl8_46 ),
    inference(resolution,[],[f458,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_wellord1(X2,X1))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2)
      | k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) = k1_wellord1(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) = k1_wellord1(X2,X0)
      | ~ r2_hidden(X0,k1_wellord1(X2,X1))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) = k1_wellord1(X2,X0)
      | ~ r2_hidden(X0,k1_wellord1(X2,X1))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X0,k1_wellord1(X2,X1))
          & v2_wellord1(X2) )
       => k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) = k1_wellord1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_wellord1)).

fof(f458,plain,
    ( r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | ~ spl8_46 ),
    inference(avatar_component_clause,[],[f456])).

fof(f502,plain,
    ( spl8_46
    | ~ spl8_4
    | spl8_32
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f500,f95,f390,f90,f456])).

fof(f500,plain,
    ( sK0 = sK1
    | ~ v1_relat_1(sK2)
    | r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | ~ spl8_5 ),
    inference(resolution,[],[f96,f68])).

fof(f96,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f95])).

fof(f499,plain,
    ( ~ spl8_7
    | spl8_14
    | ~ spl8_4
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f496,f75,f90,f202,f106])).

fof(f106,plain,
    ( spl8_7
  <=> v1_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f202,plain,
    ( spl8_14
  <=> r2_hidden(k4_tarski(sK1,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f496,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK1,sK1),sK2)
    | ~ v1_relat_2(sK2)
    | ~ spl8_1 ),
    inference(resolution,[],[f77,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X1,X1),X0)
      | ~ v1_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(k4_tarski(X1,X1),X0)
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k3_relat_1(X0))
           => r2_hidden(k4_tarski(X1,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_wellord1)).

fof(f478,plain,(
    spl8_47 ),
    inference(avatar_contradiction_clause,[],[f477])).

fof(f477,plain,
    ( $false
    | spl8_47 ),
    inference(resolution,[],[f471,f72])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f471,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))
    | spl8_47 ),
    inference(avatar_component_clause,[],[f469])).

fof(f469,plain,
    ( spl8_47
  <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f476,plain,
    ( ~ spl8_47
    | spl8_6
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f475,f390,f99,f469])).

fof(f475,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))
    | spl8_6
    | ~ spl8_32 ),
    inference(forward_demodulation,[],[f101,f392])).

fof(f392,plain,
    ( sK0 = sK1
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f390])).

fof(f101,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | spl8_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f274,plain,
    ( ~ spl8_10
    | spl8_20
    | ~ spl8_4
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f262,f80,f90,f272,f124])).

fof(f124,plain,
    ( spl8_10
  <=> v6_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f80,plain,
    ( spl8_2
  <=> r2_hidden(sK0,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f262,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(sK2)
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | sK0 = X1
        | r2_hidden(k4_tarski(sK0,X1),sK2)
        | r2_hidden(k4_tarski(X1,sK0),sK2)
        | ~ v6_relat_2(sK2) )
    | ~ spl8_2 ),
    inference(resolution,[],[f38,f82])).

fof(f82,plain,
    ( r2_hidden(sK0,k3_relat_1(sK2))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k3_relat_1(X0))
      | X1 = X2
      | r2_hidden(k4_tarski(X1,X2),X0)
      | r2_hidden(k4_tarski(X2,X1),X0)
      | ~ v6_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ~ ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).

fof(f127,plain,
    ( ~ spl8_4
    | spl8_10
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f122,f85,f124,f90])).

fof(f122,plain,
    ( v6_relat_2(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_3 ),
    inference(resolution,[],[f47,f87])).

fof(f87,plain,
    ( v2_wellord1(sK2)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).

fof(f109,plain,
    ( ~ spl8_4
    | spl8_7
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f104,f85,f106,f90])).

fof(f104,plain,
    ( v1_relat_2(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_3 ),
    inference(resolution,[],[f44,f87])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f103,plain,
    ( spl8_5
    | spl8_6 ),
    inference(avatar_split_clause,[],[f29,f99,f95])).

fof(f29,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) )
         => ( r2_hidden(k4_tarski(X0,X1),X2)
          <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_wellord1)).

fof(f102,plain,
    ( ~ spl8_5
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f30,f99,f95])).

fof(f30,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f93,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f31,f90])).

fof(f31,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f88,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f32,f85])).

fof(f32,plain,(
    v2_wellord1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f83,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f33,f80])).

fof(f33,plain,(
    r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f78,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f34,f75])).

fof(f34,plain,(
    r2_hidden(sK1,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:04:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (15149)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (15151)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (15150)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (15141)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (15148)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (15156)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (15142)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (15144)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (15163)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.38/0.54  % (15143)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.38/0.54  % (15155)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.38/0.54  % (15157)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.38/0.54  % (15165)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.38/0.54  % (15140)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.38/0.54  % (15168)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.38/0.54  % (15160)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.38/0.55  % (15139)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.38/0.55  % (15152)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.38/0.55  % (15166)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.50/0.55  % (15167)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.50/0.55  % (15154)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.50/0.55  % (15145)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.50/0.56  % (15158)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.50/0.56  % (15159)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.50/0.56  % (15147)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.50/0.56  % (15153)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.50/0.56  % (15164)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.50/0.57  % (15162)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.50/0.57  % (15161)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.50/0.58  % (15146)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.50/0.61  % (15155)Refutation found. Thanks to Tanya!
% 1.50/0.61  % SZS status Theorem for theBenchmark
% 1.50/0.61  % SZS output start Proof for theBenchmark
% 1.50/0.62  fof(f1039,plain,(
% 1.50/0.62    $false),
% 1.50/0.62    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f102,f103,f109,f127,f274,f476,f478,f499,f502,f512,f946,f948,f973,f1020,f1032,f1038])).
% 1.50/0.62  fof(f1038,plain,(
% 1.50/0.62    sK0 != sK1 | r2_hidden(k4_tarski(sK0,sK1),sK2) | ~r2_hidden(k4_tarski(sK1,sK1),sK2)),
% 1.50/0.62    introduced(theory_tautology_sat_conflict,[])).
% 1.50/0.62  fof(f1032,plain,(
% 1.50/0.62    ~spl8_4 | ~spl8_94),
% 1.50/0.62    inference(avatar_split_clause,[],[f1028,f1017,f90])).
% 1.50/0.62  fof(f90,plain,(
% 1.50/0.62    spl8_4 <=> v1_relat_1(sK2)),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.50/0.62  fof(f1017,plain,(
% 1.50/0.62    spl8_94 <=> r2_hidden(sK1,k1_wellord1(sK2,sK1))),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_94])])).
% 1.50/0.62  fof(f1028,plain,(
% 1.50/0.62    ~v1_relat_1(sK2) | ~spl8_94),
% 1.50/0.62    inference(resolution,[],[f1019,f71])).
% 1.50/0.62  fof(f71,plain,(
% 1.50/0.62    ( ! [X0,X3] : (~r2_hidden(X3,k1_wellord1(X0,X3)) | ~v1_relat_1(X0)) )),
% 1.50/0.62    inference(equality_resolution,[],[f70])).
% 1.50/0.62  fof(f70,plain,(
% 1.50/0.62    ( ! [X2,X0,X3] : (~v1_relat_1(X0) | ~r2_hidden(X3,X2) | k1_wellord1(X0,X3) != X2) )),
% 1.50/0.62    inference(equality_resolution,[],[f53])).
% 1.50/0.62  fof(f53,plain,(
% 1.50/0.62    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | X1 != X3 | ~r2_hidden(X3,X2) | k1_wellord1(X0,X1) != X2) )),
% 1.50/0.62    inference(cnf_transformation,[],[f19])).
% 1.50/0.62  fof(f19,plain,(
% 1.50/0.62    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 1.50/0.62    inference(ennf_transformation,[],[f4])).
% 1.50/0.62  fof(f4,axiom,(
% 1.50/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 1.50/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).
% 1.50/0.62  fof(f1019,plain,(
% 1.50/0.62    r2_hidden(sK1,k1_wellord1(sK2,sK1)) | ~spl8_94),
% 1.50/0.62    inference(avatar_component_clause,[],[f1017])).
% 1.50/0.62  fof(f1020,plain,(
% 1.50/0.62    spl8_94 | ~spl8_6 | ~spl8_45),
% 1.50/0.62    inference(avatar_split_clause,[],[f1009,f449,f99,f1017])).
% 1.50/0.62  fof(f99,plain,(
% 1.50/0.62    spl8_6 <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.50/0.62  fof(f449,plain,(
% 1.50/0.62    spl8_45 <=> r2_hidden(sK1,k1_wellord1(sK2,sK0))),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).
% 1.50/0.62  fof(f1009,plain,(
% 1.50/0.62    r2_hidden(sK1,k1_wellord1(sK2,sK1)) | (~spl8_6 | ~spl8_45)),
% 1.50/0.62    inference(resolution,[],[f976,f100])).
% 1.50/0.62  fof(f100,plain,(
% 1.50/0.62    r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~spl8_6),
% 1.50/0.62    inference(avatar_component_clause,[],[f99])).
% 1.50/0.62  fof(f976,plain,(
% 1.50/0.62    ( ! [X0] : (~r1_tarski(k1_wellord1(sK2,sK0),X0) | r2_hidden(sK1,X0)) ) | ~spl8_45),
% 1.50/0.62    inference(resolution,[],[f451,f61])).
% 1.50/0.62  fof(f61,plain,(
% 1.50/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.50/0.62    inference(cnf_transformation,[],[f22])).
% 1.50/0.62  fof(f22,plain,(
% 1.50/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.50/0.62    inference(ennf_transformation,[],[f1])).
% 1.50/0.62  fof(f1,axiom,(
% 1.50/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.50/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.50/0.62  fof(f451,plain,(
% 1.50/0.62    r2_hidden(sK1,k1_wellord1(sK2,sK0)) | ~spl8_45),
% 1.50/0.62    inference(avatar_component_clause,[],[f449])).
% 1.50/0.62  fof(f973,plain,(
% 1.50/0.62    spl8_45 | ~spl8_4 | spl8_32 | ~spl8_33),
% 1.50/0.62    inference(avatar_split_clause,[],[f970,f394,f390,f90,f449])).
% 1.50/0.62  fof(f390,plain,(
% 1.50/0.62    spl8_32 <=> sK0 = sK1),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 1.50/0.62  fof(f394,plain,(
% 1.50/0.62    spl8_33 <=> r2_hidden(k4_tarski(sK1,sK0),sK2)),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 1.50/0.62  fof(f970,plain,(
% 1.50/0.62    sK0 = sK1 | ~v1_relat_1(sK2) | r2_hidden(sK1,k1_wellord1(sK2,sK0)) | ~spl8_33),
% 1.50/0.62    inference(resolution,[],[f396,f68])).
% 1.50/0.62  fof(f68,plain,(
% 1.50/0.62    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~v1_relat_1(X0) | r2_hidden(X3,k1_wellord1(X0,X1))) )),
% 1.50/0.62    inference(equality_resolution,[],[f55])).
% 1.50/0.62  fof(f55,plain,(
% 1.50/0.62    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | X1 = X3 | ~r2_hidden(k4_tarski(X3,X1),X0) | r2_hidden(X3,X2) | k1_wellord1(X0,X1) != X2) )),
% 1.50/0.62    inference(cnf_transformation,[],[f19])).
% 1.50/0.62  fof(f396,plain,(
% 1.50/0.62    r2_hidden(k4_tarski(sK1,sK0),sK2) | ~spl8_33),
% 1.50/0.62    inference(avatar_component_clause,[],[f394])).
% 1.50/0.62  fof(f948,plain,(
% 1.50/0.62    spl8_32 | spl8_5 | spl8_33 | ~spl8_1 | ~spl8_20),
% 1.50/0.62    inference(avatar_split_clause,[],[f530,f272,f75,f394,f95,f390])).
% 1.50/0.62  fof(f95,plain,(
% 1.50/0.62    spl8_5 <=> r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.50/0.62  fof(f75,plain,(
% 1.50/0.62    spl8_1 <=> r2_hidden(sK1,k3_relat_1(sK2))),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.50/0.62  fof(f272,plain,(
% 1.50/0.62    spl8_20 <=> ! [X1] : (~r2_hidden(X1,k3_relat_1(sK2)) | r2_hidden(k4_tarski(X1,sK0),sK2) | r2_hidden(k4_tarski(sK0,X1),sK2) | sK0 = X1)),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 1.50/0.62  fof(f530,plain,(
% 1.50/0.62    r2_hidden(k4_tarski(sK1,sK0),sK2) | r2_hidden(k4_tarski(sK0,sK1),sK2) | sK0 = sK1 | (~spl8_1 | ~spl8_20)),
% 1.50/0.62    inference(resolution,[],[f273,f77])).
% 1.50/0.62  fof(f77,plain,(
% 1.50/0.62    r2_hidden(sK1,k3_relat_1(sK2)) | ~spl8_1),
% 1.50/0.62    inference(avatar_component_clause,[],[f75])).
% 1.50/0.62  fof(f273,plain,(
% 1.50/0.62    ( ! [X1] : (~r2_hidden(X1,k3_relat_1(sK2)) | r2_hidden(k4_tarski(X1,sK0),sK2) | r2_hidden(k4_tarski(sK0,X1),sK2) | sK0 = X1) ) | ~spl8_20),
% 1.50/0.62    inference(avatar_component_clause,[],[f272])).
% 1.50/0.62  fof(f946,plain,(
% 1.50/0.62    spl8_6 | ~spl8_4 | ~spl8_50),
% 1.50/0.62    inference(avatar_split_clause,[],[f945,f509,f90,f99])).
% 1.50/0.62  fof(f509,plain,(
% 1.50/0.62    spl8_50 <=> k1_wellord1(sK2,sK0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),sK0)),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).
% 1.50/0.62  fof(f945,plain,(
% 1.50/0.62    r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | (~spl8_4 | ~spl8_50)),
% 1.50/0.62    inference(superposition,[],[f932,f511])).
% 1.50/0.62  fof(f511,plain,(
% 1.50/0.62    k1_wellord1(sK2,sK0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),sK0) | ~spl8_50),
% 1.50/0.62    inference(avatar_component_clause,[],[f509])).
% 1.50/0.62  fof(f932,plain,(
% 1.50/0.62    ( ! [X0,X1] : (r1_tarski(k1_wellord1(k2_wellord1(sK2,X0),X1),X0)) ) | ~spl8_4),
% 1.50/0.62    inference(resolution,[],[f183,f709])).
% 1.50/0.62  fof(f709,plain,(
% 1.50/0.62    ( ! [X0] : (r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X0)) ) | ~spl8_4),
% 1.50/0.62    inference(duplicate_literal_removal,[],[f698])).
% 1.50/0.62  fof(f698,plain,(
% 1.50/0.62    ( ! [X0] : (r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X0) | r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X0)) ) | ~spl8_4),
% 1.50/0.62    inference(resolution,[],[f310,f63])).
% 1.50/0.62  fof(f63,plain,(
% 1.50/0.62    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.50/0.62    inference(cnf_transformation,[],[f22])).
% 1.50/0.62  fof(f310,plain,(
% 1.50/0.62    ( ! [X0,X1] : (r2_hidden(sK7(k3_relat_1(k2_wellord1(sK2,X0)),X1),X0) | r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X1)) ) | ~spl8_4),
% 1.50/0.62    inference(resolution,[],[f191,f92])).
% 1.50/0.62  fof(f92,plain,(
% 1.50/0.62    v1_relat_1(sK2) | ~spl8_4),
% 1.50/0.62    inference(avatar_component_clause,[],[f90])).
% 1.50/0.62  fof(f191,plain,(
% 1.50/0.62    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r2_hidden(sK7(k3_relat_1(k2_wellord1(X0,X1)),X2),X1) | r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X2)) )),
% 1.50/0.62    inference(resolution,[],[f65,f62])).
% 1.50/0.62  fof(f62,plain,(
% 1.50/0.62    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.50/0.62    inference(cnf_transformation,[],[f22])).
% 1.50/0.62  fof(f65,plain,(
% 1.50/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2) | r2_hidden(X0,X1)) )),
% 1.50/0.62    inference(cnf_transformation,[],[f24])).
% 1.50/0.62  fof(f24,plain,(
% 1.50/0.62    ! [X0,X1,X2] : ((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2))),
% 1.50/0.62    inference(flattening,[],[f23])).
% 1.50/0.62  fof(f23,plain,(
% 1.50/0.62    ! [X0,X1,X2] : (((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.50/0.62    inference(ennf_transformation,[],[f10])).
% 1.50/0.62  fof(f10,axiom,(
% 1.50/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) => (r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2)))))),
% 1.50/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_wellord1)).
% 1.50/0.62  fof(f183,plain,(
% 1.50/0.62    ( ! [X2,X0,X1] : (~r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X1) | r1_tarski(k1_wellord1(k2_wellord1(sK2,X0),X2),X1)) ) | ~spl8_4),
% 1.50/0.62    inference(resolution,[],[f138,f67])).
% 1.50/0.62  fof(f67,plain,(
% 1.50/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 1.50/0.62    inference(cnf_transformation,[],[f28])).
% 1.50/0.62  fof(f28,plain,(
% 1.50/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.50/0.62    inference(flattening,[],[f27])).
% 1.50/0.62  fof(f27,plain,(
% 1.50/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.50/0.62    inference(ennf_transformation,[],[f3])).
% 1.50/0.62  fof(f3,axiom,(
% 1.50/0.62    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.50/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.50/0.62  fof(f138,plain,(
% 1.50/0.62    ( ! [X2,X1] : (r1_tarski(k1_wellord1(k2_wellord1(sK2,X1),X2),k3_relat_1(k2_wellord1(sK2,X1)))) ) | ~spl8_4),
% 1.50/0.62    inference(resolution,[],[f57,f134])).
% 1.50/0.62  fof(f134,plain,(
% 1.50/0.62    ( ! [X0] : (v1_relat_1(k2_wellord1(sK2,X0))) ) | ~spl8_4),
% 1.50/0.62    inference(resolution,[],[f56,f92])).
% 1.50/0.62  fof(f56,plain,(
% 1.50/0.62    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k2_wellord1(X0,X1))) )),
% 1.50/0.62    inference(cnf_transformation,[],[f20])).
% 1.50/0.62  fof(f20,plain,(
% 1.50/0.62    ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0))),
% 1.50/0.62    inference(ennf_transformation,[],[f6])).
% 1.50/0.62  fof(f6,axiom,(
% 1.50/0.62    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k2_wellord1(X0,X1)))),
% 1.50/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).
% 1.50/0.62  fof(f57,plain,(
% 1.50/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))) )),
% 1.50/0.62    inference(cnf_transformation,[],[f21])).
% 1.50/0.62  fof(f21,plain,(
% 1.50/0.62    ! [X0,X1] : (r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.50/0.62    inference(ennf_transformation,[],[f9])).
% 1.50/0.62  fof(f9,axiom,(
% 1.50/0.62    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)))),
% 1.50/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_wellord1)).
% 1.50/0.62  fof(f512,plain,(
% 1.50/0.62    spl8_50 | ~spl8_4 | ~spl8_3 | ~spl8_46),
% 1.50/0.62    inference(avatar_split_clause,[],[f505,f456,f85,f90,f509])).
% 1.50/0.62  fof(f85,plain,(
% 1.50/0.62    spl8_3 <=> v2_wellord1(sK2)),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.50/0.62  fof(f456,plain,(
% 1.50/0.62    spl8_46 <=> r2_hidden(sK0,k1_wellord1(sK2,sK1))),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).
% 1.50/0.62  fof(f505,plain,(
% 1.50/0.62    ~v2_wellord1(sK2) | ~v1_relat_1(sK2) | k1_wellord1(sK2,sK0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),sK0) | ~spl8_46),
% 1.50/0.62    inference(resolution,[],[f458,f66])).
% 1.50/0.62  fof(f66,plain,(
% 1.50/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_wellord1(X2,X1)) | ~v2_wellord1(X2) | ~v1_relat_1(X2) | k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) = k1_wellord1(X2,X0)) )),
% 1.50/0.62    inference(cnf_transformation,[],[f26])).
% 1.50/0.62  fof(f26,plain,(
% 1.50/0.62    ! [X0,X1,X2] : (k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) = k1_wellord1(X2,X0) | ~r2_hidden(X0,k1_wellord1(X2,X1)) | ~v2_wellord1(X2) | ~v1_relat_1(X2))),
% 1.50/0.62    inference(flattening,[],[f25])).
% 1.50/0.62  fof(f25,plain,(
% 1.50/0.62    ! [X0,X1,X2] : ((k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) = k1_wellord1(X2,X0) | (~r2_hidden(X0,k1_wellord1(X2,X1)) | ~v2_wellord1(X2))) | ~v1_relat_1(X2))),
% 1.50/0.62    inference(ennf_transformation,[],[f11])).
% 1.50/0.62  fof(f11,axiom,(
% 1.50/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X0,k1_wellord1(X2,X1)) & v2_wellord1(X2)) => k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) = k1_wellord1(X2,X0)))),
% 1.50/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_wellord1)).
% 1.50/0.62  fof(f458,plain,(
% 1.50/0.62    r2_hidden(sK0,k1_wellord1(sK2,sK1)) | ~spl8_46),
% 1.50/0.62    inference(avatar_component_clause,[],[f456])).
% 1.50/0.62  fof(f502,plain,(
% 1.50/0.62    spl8_46 | ~spl8_4 | spl8_32 | ~spl8_5),
% 1.50/0.62    inference(avatar_split_clause,[],[f500,f95,f390,f90,f456])).
% 1.50/0.62  fof(f500,plain,(
% 1.50/0.62    sK0 = sK1 | ~v1_relat_1(sK2) | r2_hidden(sK0,k1_wellord1(sK2,sK1)) | ~spl8_5),
% 1.50/0.62    inference(resolution,[],[f96,f68])).
% 1.50/0.62  fof(f96,plain,(
% 1.50/0.62    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl8_5),
% 1.50/0.62    inference(avatar_component_clause,[],[f95])).
% 1.50/0.62  fof(f499,plain,(
% 1.50/0.62    ~spl8_7 | spl8_14 | ~spl8_4 | ~spl8_1),
% 1.50/0.62    inference(avatar_split_clause,[],[f496,f75,f90,f202,f106])).
% 1.50/0.62  fof(f106,plain,(
% 1.50/0.62    spl8_7 <=> v1_relat_2(sK2)),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.50/0.62  fof(f202,plain,(
% 1.50/0.62    spl8_14 <=> r2_hidden(k4_tarski(sK1,sK1),sK2)),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 1.50/0.62  fof(f496,plain,(
% 1.50/0.62    ~v1_relat_1(sK2) | r2_hidden(k4_tarski(sK1,sK1),sK2) | ~v1_relat_2(sK2) | ~spl8_1),
% 1.50/0.62    inference(resolution,[],[f77,f35])).
% 1.50/0.62  fof(f35,plain,(
% 1.50/0.62    ( ! [X0,X1] : (~r2_hidden(X1,k3_relat_1(X0)) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(X1,X1),X0) | ~v1_relat_2(X0)) )),
% 1.50/0.62    inference(cnf_transformation,[],[f16])).
% 1.50/0.62  fof(f16,plain,(
% 1.50/0.62    ! [X0] : ((v1_relat_2(X0) <=> ! [X1] : (r2_hidden(k4_tarski(X1,X1),X0) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 1.50/0.62    inference(ennf_transformation,[],[f7])).
% 1.50/0.62  fof(f7,axiom,(
% 1.50/0.62    ! [X0] : (v1_relat_1(X0) => (v1_relat_2(X0) <=> ! [X1] : (r2_hidden(X1,k3_relat_1(X0)) => r2_hidden(k4_tarski(X1,X1),X0))))),
% 1.50/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_wellord1)).
% 1.50/0.62  fof(f478,plain,(
% 1.50/0.62    spl8_47),
% 1.50/0.62    inference(avatar_contradiction_clause,[],[f477])).
% 1.50/0.62  fof(f477,plain,(
% 1.50/0.62    $false | spl8_47),
% 1.50/0.62    inference(resolution,[],[f471,f72])).
% 1.50/0.62  fof(f72,plain,(
% 1.50/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.50/0.62    inference(equality_resolution,[],[f59])).
% 1.50/0.62  fof(f59,plain,(
% 1.50/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.50/0.62    inference(cnf_transformation,[],[f2])).
% 1.50/0.62  fof(f2,axiom,(
% 1.50/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.50/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.50/0.62  fof(f471,plain,(
% 1.50/0.62    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) | spl8_47),
% 1.50/0.62    inference(avatar_component_clause,[],[f469])).
% 1.50/0.62  fof(f469,plain,(
% 1.50/0.62    spl8_47 <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).
% 1.50/0.62  fof(f476,plain,(
% 1.50/0.62    ~spl8_47 | spl8_6 | ~spl8_32),
% 1.50/0.62    inference(avatar_split_clause,[],[f475,f390,f99,f469])).
% 1.50/0.62  fof(f475,plain,(
% 1.50/0.62    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) | (spl8_6 | ~spl8_32)),
% 1.50/0.62    inference(forward_demodulation,[],[f101,f392])).
% 1.50/0.62  fof(f392,plain,(
% 1.50/0.62    sK0 = sK1 | ~spl8_32),
% 1.50/0.62    inference(avatar_component_clause,[],[f390])).
% 1.50/0.62  fof(f101,plain,(
% 1.50/0.62    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | spl8_6),
% 1.50/0.62    inference(avatar_component_clause,[],[f99])).
% 1.50/0.62  fof(f274,plain,(
% 1.50/0.62    ~spl8_10 | spl8_20 | ~spl8_4 | ~spl8_2),
% 1.50/0.62    inference(avatar_split_clause,[],[f262,f80,f90,f272,f124])).
% 1.50/0.62  fof(f124,plain,(
% 1.50/0.62    spl8_10 <=> v6_relat_2(sK2)),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.50/0.62  fof(f80,plain,(
% 1.50/0.62    spl8_2 <=> r2_hidden(sK0,k3_relat_1(sK2))),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.50/0.62  fof(f262,plain,(
% 1.50/0.62    ( ! [X1] : (~v1_relat_1(sK2) | ~r2_hidden(X1,k3_relat_1(sK2)) | sK0 = X1 | r2_hidden(k4_tarski(sK0,X1),sK2) | r2_hidden(k4_tarski(X1,sK0),sK2) | ~v6_relat_2(sK2)) ) | ~spl8_2),
% 1.50/0.62    inference(resolution,[],[f38,f82])).
% 1.50/0.62  fof(f82,plain,(
% 1.50/0.62    r2_hidden(sK0,k3_relat_1(sK2)) | ~spl8_2),
% 1.50/0.62    inference(avatar_component_clause,[],[f80])).
% 1.50/0.62  fof(f38,plain,(
% 1.50/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X1,k3_relat_1(X0)) | ~v1_relat_1(X0) | ~r2_hidden(X2,k3_relat_1(X0)) | X1 = X2 | r2_hidden(k4_tarski(X1,X2),X0) | r2_hidden(k4_tarski(X2,X1),X0) | ~v6_relat_2(X0)) )),
% 1.50/0.62    inference(cnf_transformation,[],[f17])).
% 1.50/0.62  fof(f17,plain,(
% 1.50/0.62    ! [X0] : ((v6_relat_2(X0) <=> ! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 1.50/0.62    inference(ennf_transformation,[],[f8])).
% 1.50/0.62  fof(f8,axiom,(
% 1.50/0.62    ! [X0] : (v1_relat_1(X0) => (v6_relat_2(X0) <=> ! [X1,X2] : ~(~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))))),
% 1.50/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).
% 1.50/0.62  fof(f127,plain,(
% 1.50/0.62    ~spl8_4 | spl8_10 | ~spl8_3),
% 1.50/0.62    inference(avatar_split_clause,[],[f122,f85,f124,f90])).
% 1.50/0.62  fof(f122,plain,(
% 1.50/0.62    v6_relat_2(sK2) | ~v1_relat_1(sK2) | ~spl8_3),
% 1.50/0.62    inference(resolution,[],[f47,f87])).
% 1.50/0.62  fof(f87,plain,(
% 1.50/0.62    v2_wellord1(sK2) | ~spl8_3),
% 1.50/0.62    inference(avatar_component_clause,[],[f85])).
% 1.50/0.62  fof(f47,plain,(
% 1.50/0.62    ( ! [X0] : (~v2_wellord1(X0) | v6_relat_2(X0) | ~v1_relat_1(X0)) )),
% 1.50/0.62    inference(cnf_transformation,[],[f18])).
% 1.50/0.62  fof(f18,plain,(
% 1.50/0.62    ! [X0] : ((v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 1.50/0.62    inference(ennf_transformation,[],[f5])).
% 1.50/0.62  fof(f5,axiom,(
% 1.50/0.62    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))))),
% 1.50/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).
% 1.50/0.62  fof(f109,plain,(
% 1.50/0.62    ~spl8_4 | spl8_7 | ~spl8_3),
% 1.50/0.62    inference(avatar_split_clause,[],[f104,f85,f106,f90])).
% 1.50/0.62  fof(f104,plain,(
% 1.50/0.62    v1_relat_2(sK2) | ~v1_relat_1(sK2) | ~spl8_3),
% 1.50/0.62    inference(resolution,[],[f44,f87])).
% 1.50/0.62  fof(f44,plain,(
% 1.50/0.62    ( ! [X0] : (~v2_wellord1(X0) | v1_relat_2(X0) | ~v1_relat_1(X0)) )),
% 1.50/0.62    inference(cnf_transformation,[],[f18])).
% 1.50/0.62  fof(f103,plain,(
% 1.50/0.62    spl8_5 | spl8_6),
% 1.50/0.62    inference(avatar_split_clause,[],[f29,f99,f95])).
% 1.50/0.62  fof(f29,plain,(
% 1.50/0.62    r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 1.50/0.62    inference(cnf_transformation,[],[f15])).
% 1.50/0.62  fof(f15,plain,(
% 1.50/0.62    ? [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 1.50/0.62    inference(flattening,[],[f14])).
% 1.50/0.62  fof(f14,plain,(
% 1.50/0.62    ? [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2))) & v1_relat_1(X2))),
% 1.50/0.62    inference(ennf_transformation,[],[f13])).
% 1.50/0.62  fof(f13,negated_conjecture,(
% 1.50/0.62    ~! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 1.50/0.62    inference(negated_conjecture,[],[f12])).
% 1.50/0.62  fof(f12,conjecture,(
% 1.50/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 1.50/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_wellord1)).
% 1.50/0.62  fof(f102,plain,(
% 1.50/0.62    ~spl8_5 | ~spl8_6),
% 1.50/0.62    inference(avatar_split_clause,[],[f30,f99,f95])).
% 1.50/0.62  fof(f30,plain,(
% 1.50/0.62    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 1.50/0.62    inference(cnf_transformation,[],[f15])).
% 1.50/0.62  fof(f93,plain,(
% 1.50/0.62    spl8_4),
% 1.50/0.62    inference(avatar_split_clause,[],[f31,f90])).
% 1.50/0.62  fof(f31,plain,(
% 1.50/0.62    v1_relat_1(sK2)),
% 1.50/0.62    inference(cnf_transformation,[],[f15])).
% 1.50/0.62  fof(f88,plain,(
% 1.50/0.62    spl8_3),
% 1.50/0.62    inference(avatar_split_clause,[],[f32,f85])).
% 1.50/0.62  fof(f32,plain,(
% 1.50/0.62    v2_wellord1(sK2)),
% 1.50/0.62    inference(cnf_transformation,[],[f15])).
% 1.50/0.62  fof(f83,plain,(
% 1.50/0.62    spl8_2),
% 1.50/0.62    inference(avatar_split_clause,[],[f33,f80])).
% 1.50/0.62  fof(f33,plain,(
% 1.50/0.62    r2_hidden(sK0,k3_relat_1(sK2))),
% 1.50/0.62    inference(cnf_transformation,[],[f15])).
% 1.50/0.62  fof(f78,plain,(
% 1.50/0.62    spl8_1),
% 1.50/0.62    inference(avatar_split_clause,[],[f34,f75])).
% 1.50/0.62  fof(f34,plain,(
% 1.50/0.62    r2_hidden(sK1,k3_relat_1(sK2))),
% 1.50/0.62    inference(cnf_transformation,[],[f15])).
% 1.50/0.62  % SZS output end Proof for theBenchmark
% 1.50/0.62  % (15155)------------------------------
% 1.50/0.62  % (15155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.62  % (15155)Termination reason: Refutation
% 1.50/0.62  
% 1.50/0.62  % (15155)Memory used [KB]: 11513
% 1.50/0.62  % (15155)Time elapsed: 0.177 s
% 1.50/0.62  % (15155)------------------------------
% 1.50/0.62  % (15155)------------------------------
% 1.50/0.62  % (15138)Success in time 0.261 s
%------------------------------------------------------------------------------
