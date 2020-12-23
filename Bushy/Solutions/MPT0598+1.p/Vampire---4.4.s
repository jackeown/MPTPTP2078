%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t202_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:58 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 239 expanded)
%              Number of leaves         :   32 (  95 expanded)
%              Depth                    :    9
%              Number of atoms          :  284 ( 604 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f240,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f70,f77,f84,f91,f101,f111,f123,f131,f149,f157,f165,f179,f193,f206,f216,f225,f233,f235,f237,f239])).

fof(f239,plain,
    ( ~ spl4_8
    | ~ spl4_22
    | spl4_31 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | ~ spl4_8
    | ~ spl4_22
    | ~ spl4_31 ),
    inference(subsumption_resolution,[],[f226,f164])).

fof(f164,plain,
    ( m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(sK0))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl4_22
  <=> m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f226,plain,
    ( ~ m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(sK0))
    | ~ spl4_8
    | ~ spl4_31 ),
    inference(unit_resulting_resolution,[],[f90,f215,f55])).

fof(f55,plain,(
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
    file('/export/starexec/sandbox/benchmark/relat_1__t202_relat_1.p',t4_subset)).

fof(f215,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl4_31
  <=> ~ m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f90,plain,
    ( r2_hidden(sK2,k2_relat_1(sK1))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl4_8
  <=> r2_hidden(sK2,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f237,plain,
    ( ~ spl4_8
    | ~ spl4_22
    | spl4_31 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl4_8
    | ~ spl4_22
    | ~ spl4_31 ),
    inference(subsumption_resolution,[],[f228,f90])).

fof(f228,plain,
    ( ~ r2_hidden(sK2,k2_relat_1(sK1))
    | ~ spl4_22
    | ~ spl4_31 ),
    inference(unit_resulting_resolution,[],[f215,f164,f55])).

fof(f235,plain,
    ( ~ spl4_8
    | ~ spl4_22
    | spl4_31 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | ~ spl4_8
    | ~ spl4_22
    | ~ spl4_31 ),
    inference(subsumption_resolution,[],[f229,f215])).

fof(f229,plain,
    ( m1_subset_1(sK2,sK0)
    | ~ spl4_8
    | ~ spl4_22 ),
    inference(unit_resulting_resolution,[],[f90,f164,f55])).

fof(f233,plain,
    ( ~ spl4_8
    | ~ spl4_22
    | spl4_31 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | ~ spl4_8
    | ~ spl4_22
    | ~ spl4_31 ),
    inference(unit_resulting_resolution,[],[f215,f90,f164,f55])).

fof(f225,plain,
    ( spl4_32
    | spl4_29 ),
    inference(avatar_split_clause,[],[f207,f204,f223])).

fof(f223,plain,
    ( spl4_32
  <=> r2_hidden(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f204,plain,
    ( spl4_29
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f207,plain,
    ( r2_hidden(sK3(sK0),sK0)
    | ~ spl4_29 ),
    inference(unit_resulting_resolution,[],[f45,f205,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/relat_1__t202_relat_1.p',t2_subset)).

fof(f205,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f204])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f10,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t202_relat_1.p',existence_m1_subset_1)).

fof(f216,plain,
    ( ~ spl4_31
    | spl4_7
    | spl4_29 ),
    inference(avatar_split_clause,[],[f208,f204,f82,f214])).

fof(f82,plain,
    ( spl4_7
  <=> ~ r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f208,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ spl4_7
    | ~ spl4_29 ),
    inference(unit_resulting_resolution,[],[f83,f205,f50])).

fof(f83,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f206,plain,
    ( ~ spl4_29
    | ~ spl4_8
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f197,f163,f89,f204])).

fof(f197,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl4_8
    | ~ spl4_22 ),
    inference(unit_resulting_resolution,[],[f90,f164,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
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
    file('/export/starexec/sandbox/benchmark/relat_1__t202_relat_1.p',t5_subset)).

fof(f193,plain,
    ( ~ spl4_27
    | spl4_13 ),
    inference(avatar_split_clause,[],[f186,f109,f191])).

fof(f191,plain,
    ( spl4_27
  <=> ~ m1_subset_1(k2_relat_1(sK1),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f109,plain,
    ( spl4_13
  <=> ~ v1_xboole_0(k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f186,plain,
    ( ~ m1_subset_1(k2_relat_1(sK1),k2_relat_1(sK1))
    | ~ spl4_13 ),
    inference(duplicate_literal_removal,[],[f185])).

fof(f185,plain,
    ( ~ m1_subset_1(k2_relat_1(sK1),k2_relat_1(sK1))
    | ~ m1_subset_1(k2_relat_1(sK1),k2_relat_1(sK1))
    | ~ spl4_13 ),
    inference(resolution,[],[f182,f142])).

fof(f142,plain,
    ( ! [X8] :
        ( r2_hidden(X8,k2_relat_1(sK1))
        | ~ m1_subset_1(X8,k2_relat_1(sK1)) )
    | ~ spl4_13 ),
    inference(resolution,[],[f50,f110])).

fof(f110,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK1))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f109])).

fof(f182,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k2_relat_1(sK1),X0)
        | ~ m1_subset_1(X0,k2_relat_1(sK1)) )
    | ~ spl4_13 ),
    inference(resolution,[],[f142,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t202_relat_1.p',antisymmetry_r2_hidden)).

fof(f179,plain,
    ( ~ spl4_25
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f169,f147,f177])).

fof(f177,plain,
    ( spl4_25
  <=> ~ r2_hidden(k2_relat_1(sK1),sK3(k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f147,plain,
    ( spl4_18
  <=> r2_hidden(sK3(k2_relat_1(sK1)),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f169,plain,
    ( ~ r2_hidden(k2_relat_1(sK1),sK3(k2_relat_1(sK1)))
    | ~ spl4_18 ),
    inference(unit_resulting_resolution,[],[f148,f48])).

fof(f148,plain,
    ( r2_hidden(sK3(k2_relat_1(sK1)),k2_relat_1(sK1))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f147])).

fof(f165,plain,
    ( spl4_22
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f158,f155,f163])).

fof(f155,plain,
    ( spl4_20
  <=> r1_tarski(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f158,plain,
    ( m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(sK0))
    | ~ spl4_20 ),
    inference(unit_resulting_resolution,[],[f156,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox/benchmark/relat_1__t202_relat_1.p',t3_subset)).

fof(f156,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f155])).

fof(f157,plain,
    ( spl4_20
    | ~ spl4_0
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f150,f75,f61,f155])).

fof(f61,plain,
    ( spl4_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f75,plain,
    ( spl4_4
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f150,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0)
    | ~ spl4_0
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f62,f76,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/relat_1__t202_relat_1.p',d19_relat_1)).

fof(f76,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f62,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f61])).

fof(f149,plain,
    ( spl4_18
    | spl4_13 ),
    inference(avatar_split_clause,[],[f137,f109,f147])).

fof(f137,plain,
    ( r2_hidden(sK3(k2_relat_1(sK1)),k2_relat_1(sK1))
    | ~ spl4_13 ),
    inference(unit_resulting_resolution,[],[f45,f110,f50])).

fof(f131,plain,
    ( spl4_16
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f124,f89,f129])).

fof(f129,plain,
    ( spl4_16
  <=> m1_subset_1(sK2,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f124,plain,
    ( m1_subset_1(sK2,k2_relat_1(sK1))
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f90,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t202_relat_1.p',t1_subset)).

fof(f123,plain,
    ( ~ spl4_15
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f115,f89,f121])).

fof(f121,plain,
    ( spl4_15
  <=> ~ r2_hidden(k2_relat_1(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f115,plain,
    ( ~ r2_hidden(k2_relat_1(sK1),sK2)
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f90,f48])).

fof(f111,plain,
    ( ~ spl4_13
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f102,f89,f109])).

fof(f102,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK1))
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f90,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
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
    file('/export/starexec/sandbox/benchmark/relat_1__t202_relat_1.p',t7_boole)).

fof(f101,plain,
    ( spl4_10
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f92,f68,f99])).

fof(f99,plain,
    ( spl4_10
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f68,plain,
    ( spl4_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f92,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f69,f44])).

fof(f44,plain,(
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
    file('/export/starexec/sandbox/benchmark/relat_1__t202_relat_1.p',t6_boole)).

fof(f69,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f91,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f41,f89])).

fof(f41,plain,(
    r2_hidden(sK2,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ~ r2_hidden(sK2,sK0)
    & r2_hidden(sK2,k2_relat_1(sK1))
    & v5_relat_1(sK1,sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f33,f32])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,k2_relat_1(X1)) )
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r2_hidden(X2,sK0)
          & r2_hidden(X2,k2_relat_1(sK1)) )
      & v5_relat_1(sK1,sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,k2_relat_1(X1)) )
     => ( ~ r2_hidden(sK2,X0)
        & r2_hidden(sK2,k2_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,k2_relat_1(X1)) )
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,k2_relat_1(X1)) )
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v5_relat_1(X1,X0)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( r2_hidden(X2,k2_relat_1(X1))
           => r2_hidden(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k2_relat_1(X1))
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t202_relat_1.p',t202_relat_1)).

fof(f84,plain,(
    ~ spl4_7 ),
    inference(avatar_split_clause,[],[f42,f82])).

fof(f42,plain,(
    ~ r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f77,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f40,f75])).

fof(f40,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f70,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f43,f68])).

fof(f43,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t202_relat_1.p',dt_o_0_0_xboole_0)).

fof(f63,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f39,f61])).

fof(f39,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
