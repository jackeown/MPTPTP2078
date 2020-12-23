%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 282 expanded)
%              Number of leaves         :   35 ( 122 expanded)
%              Depth                    :    8
%              Number of atoms          :  498 (1078 expanded)
%              Number of equality atoms :   84 ( 221 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f747,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f82,f91,f99,f104,f109,f130,f188,f248,f310,f414,f432,f471,f478,f511,f557,f563,f569,f575,f597,f603,f663,f664])).

fof(f664,plain,
    ( spl6_13
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f413,f69,f132])).

fof(f132,plain,
    ( spl6_13
  <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f69,plain,
    ( spl6_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f413,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl6_3 ),
    inference(resolution,[],[f71,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f71,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f663,plain,
    ( ~ spl6_50
    | spl6_33
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f420,f401,f275,f425])).

fof(f425,plain,
    ( spl6_50
  <=> v4_relat_1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f275,plain,
    ( spl6_33
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f401,plain,
    ( spl6_48
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f420,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ v4_relat_1(sK3,k1_xboole_0)
    | ~ spl6_48 ),
    inference(resolution,[],[f402,f119])).

fof(f119,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f110,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f110,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f42,f32])).

fof(f32,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f402,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f401])).

fof(f603,plain,
    ( ~ spl6_2
    | ~ spl6_8
    | spl6_10
    | ~ spl6_52
    | ~ spl6_58
    | ~ spl6_62
    | ~ spl6_64 ),
    inference(avatar_contradiction_clause,[],[f600])).

fof(f600,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_8
    | spl6_10
    | ~ spl6_52
    | ~ spl6_58
    | ~ spl6_62
    | ~ spl6_64 ),
    inference(unit_resulting_resolution,[],[f66,f466,f95,f555,f103,f574,f510])).

fof(f510,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_1(X2)
        | ~ r1_partfun1(X2,sK3)
        | k1_funct_1(X2,X3) = k1_funct_1(sK3,X3)
        | ~ r2_hidden(X3,k1_relat_1(X2))
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(k1_relat_1(X2),sK0) )
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f509])).

fof(f509,plain,
    ( spl6_58
  <=> ! [X3,X2] :
        ( ~ r1_tarski(k1_relat_1(X2),sK0)
        | ~ r1_partfun1(X2,sK3)
        | k1_funct_1(X2,X3) = k1_funct_1(sK3,X3)
        | ~ r2_hidden(X3,k1_relat_1(X2))
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f574,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | ~ spl6_64 ),
    inference(avatar_component_clause,[],[f572])).

fof(f572,plain,
    ( spl6_64
  <=> r2_hidden(sK4,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f103,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl6_10
  <=> k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f555,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f554])).

fof(f554,plain,
    ( spl6_62
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f95,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl6_8
  <=> r1_partfun1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f466,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f465])).

fof(f465,plain,
    ( spl6_52
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f66,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl6_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f597,plain,
    ( spl6_8
    | ~ spl6_52
    | ~ spl6_5
    | ~ spl6_48
    | ~ spl6_2
    | ~ spl6_62
    | ~ spl6_16
    | ~ spl6_61 ),
    inference(avatar_split_clause,[],[f596,f550,f163,f554,f64,f401,f79,f465,f93])).

fof(f79,plain,
    ( spl6_5
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f163,plain,
    ( spl6_16
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f550,plain,
    ( spl6_61
  <=> k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f596,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | r1_partfun1(sK2,sK3)
    | ~ spl6_16
    | ~ spl6_61 ),
    inference(forward_demodulation,[],[f595,f165])).

fof(f165,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f163])).

fof(f595,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_relat_1(sK2)
    | r1_partfun1(sK2,sK3)
    | ~ spl6_61 ),
    inference(trivial_inequality_removal,[],[f594])).

fof(f594,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK2,sK5(sK2,sK3))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_relat_1(sK2)
    | r1_partfun1(sK2,sK3)
    | ~ spl6_61 ),
    inference(superposition,[],[f36,f552])).

fof(f552,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))
    | ~ spl6_61 ),
    inference(avatar_component_clause,[],[f550])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X0)
      | r1_partfun1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_partfun1(X0,X1)
          <=> ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_partfun1(X0,X1)
          <=> ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
           => ( r1_partfun1(X0,X1)
            <=> ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_partfun1)).

fof(f575,plain,
    ( spl6_64
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f570,f127,f106,f572])).

fof(f106,plain,
    ( spl6_11
  <=> r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f127,plain,
    ( spl6_12
  <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f570,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f108,f129])).

fof(f129,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f127])).

fof(f108,plain,
    ( r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f106])).

fof(f569,plain,
    ( ~ spl6_1
    | spl6_63 ),
    inference(avatar_contradiction_clause,[],[f568])).

fof(f568,plain,
    ( $false
    | ~ spl6_1
    | spl6_63 ),
    inference(subsumption_resolution,[],[f61,f565])).

fof(f565,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | spl6_63 ),
    inference(resolution,[],[f562,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f562,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | spl6_63 ),
    inference(avatar_component_clause,[],[f560])).

fof(f560,plain,
    ( spl6_63
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f61,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl6_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f563,plain,
    ( ~ spl6_63
    | ~ spl6_52
    | spl6_62 ),
    inference(avatar_split_clause,[],[f558,f554,f465,f560])).

fof(f558,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,sK0)
    | spl6_62 ),
    inference(resolution,[],[f556,f39])).

fof(f556,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl6_62 ),
    inference(avatar_component_clause,[],[f554])).

fof(f557,plain,
    ( ~ spl6_5
    | ~ spl6_48
    | spl6_61
    | ~ spl6_62
    | spl6_8
    | ~ spl6_16
    | ~ spl6_53 ),
    inference(avatar_split_clause,[],[f548,f469,f163,f93,f554,f550,f401,f79])).

fof(f469,plain,
    ( spl6_53
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_funct_1(sK2,sK5(sK2,X0)) = k1_funct_1(sK3,sK5(sK2,X0))
        | r1_partfun1(sK2,X0)
        | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X0))
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f548,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | spl6_8
    | ~ spl6_16
    | ~ spl6_53 ),
    inference(forward_demodulation,[],[f547,f165])).

fof(f547,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))
    | ~ v1_relat_1(sK3)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | spl6_8
    | ~ spl6_53 ),
    inference(resolution,[],[f470,f94])).

fof(f94,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f93])).

fof(f470,plain,
    ( ! [X0] :
        ( r1_partfun1(sK2,X0)
        | k1_funct_1(sK2,sK5(sK2,X0)) = k1_funct_1(sK3,sK5(sK2,X0))
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X0))
        | ~ v1_funct_1(X0) )
    | ~ spl6_53 ),
    inference(avatar_component_clause,[],[f469])).

fof(f511,plain,
    ( ~ spl6_48
    | spl6_58
    | ~ spl6_5
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f507,f163,f79,f509,f401])).

fof(f507,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(k1_relat_1(X2),sK0)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(sK3)
        | ~ v1_relat_1(X2)
        | ~ r2_hidden(X3,k1_relat_1(X2))
        | k1_funct_1(X2,X3) = k1_funct_1(sK3,X3)
        | ~ r1_partfun1(X2,sK3) )
    | ~ spl6_5
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f498,f165])).

fof(f498,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_1(X2)
        | ~ v1_relat_1(sK3)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(k1_relat_1(X2),k1_relat_1(sK3))
        | ~ r2_hidden(X3,k1_relat_1(X2))
        | k1_funct_1(X2,X3) = k1_funct_1(sK3,X3)
        | ~ r1_partfun1(X2,sK3) )
    | ~ spl6_5 ),
    inference(resolution,[],[f34,f81])).

fof(f81,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
      | ~ r1_partfun1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f478,plain,
    ( ~ spl6_1
    | spl6_52 ),
    inference(avatar_contradiction_clause,[],[f476])).

fof(f476,plain,
    ( $false
    | ~ spl6_1
    | spl6_52 ),
    inference(unit_resulting_resolution,[],[f37,f61,f467,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f467,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_52 ),
    inference(avatar_component_clause,[],[f465])).

fof(f37,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f471,plain,
    ( ~ spl6_52
    | spl6_53
    | ~ spl6_2
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f462,f127,f97,f64,f469,f465])).

fof(f97,plain,
    ( spl6_9
  <=> ! [X4] :
        ( ~ r2_hidden(X4,k1_relset_1(sK0,sK1,sK2))
        | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f462,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X0))
        | ~ v1_relat_1(sK2)
        | r1_partfun1(sK2,X0)
        | k1_funct_1(sK2,sK5(sK2,X0)) = k1_funct_1(sK3,sK5(sK2,X0)) )
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(resolution,[],[f35,f136])).

fof(f136,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relat_1(sK2))
        | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) )
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(backward_demodulation,[],[f98,f129])).

fof(f98,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relset_1(sK0,sK1,sK2))
        | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) )
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f97])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X0)
      | r1_partfun1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f432,plain,
    ( ~ spl6_28
    | spl6_50 ),
    inference(avatar_contradiction_clause,[],[f431])).

fof(f431,plain,
    ( $false
    | ~ spl6_28
    | spl6_50 ),
    inference(subsumption_resolution,[],[f247,f429])).

fof(f429,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | spl6_50 ),
    inference(resolution,[],[f427,f44])).

fof(f427,plain,
    ( ~ v4_relat_1(sK3,k1_xboole_0)
    | spl6_50 ),
    inference(avatar_component_clause,[],[f425])).

fof(f247,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl6_28
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f414,plain,
    ( ~ spl6_3
    | spl6_48 ),
    inference(avatar_contradiction_clause,[],[f409])).

fof(f409,plain,
    ( $false
    | ~ spl6_3
    | spl6_48 ),
    inference(unit_resulting_resolution,[],[f403,f37,f71,f33])).

fof(f403,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_48 ),
    inference(avatar_component_clause,[],[f401])).

fof(f310,plain,
    ( ~ spl6_33
    | ~ spl6_6
    | spl6_16 ),
    inference(avatar_split_clause,[],[f309,f163,f84,f275])).

fof(f84,plain,
    ( spl6_6
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f309,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | ~ spl6_6
    | spl6_16 ),
    inference(forward_demodulation,[],[f164,f86])).

fof(f86,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f84])).

fof(f164,plain,
    ( sK0 != k1_relat_1(sK3)
    | spl6_16 ),
    inference(avatar_component_clause,[],[f163])).

fof(f248,plain,
    ( spl6_28
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f243,f84,f69,f245])).

fof(f243,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f71,f86])).

fof(f188,plain,
    ( ~ spl6_4
    | spl6_7
    | spl6_16
    | ~ spl6_3
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f187,f132,f69,f163,f88,f74])).

fof(f74,plain,
    ( spl6_4
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f88,plain,
    ( spl6_7
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f187,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl6_3
    | ~ spl6_13 ),
    inference(forward_demodulation,[],[f184,f134])).

fof(f134,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f132])).

fof(f184,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl6_3 ),
    inference(resolution,[],[f50,f71])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f130,plain,
    ( spl6_12
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f124,f59,f127])).

fof(f124,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl6_1 ),
    inference(resolution,[],[f43,f61])).

fof(f109,plain,
    ( ~ spl6_8
    | spl6_11 ),
    inference(avatar_split_clause,[],[f23,f106,f93])).

fof(f23,plain,
    ( r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2))
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( r1_partfun1(X2,X3)
          <~> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( r1_partfun1(X2,X3)
          <~> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ( k1_xboole_0 = X1
               => k1_xboole_0 = X0 )
             => ( r1_partfun1(X2,X3)
              <=> ! [X4] :
                    ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                   => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ( k1_xboole_0 = X1
             => k1_xboole_0 = X0 )
           => ( r1_partfun1(X2,X3)
            <=> ! [X4] :
                  ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_2)).

fof(f104,plain,
    ( ~ spl6_8
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f24,f101,f93])).

fof(f24,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f14])).

% (20879)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
fof(f99,plain,
    ( spl6_8
    | spl6_9 ),
    inference(avatar_split_clause,[],[f25,f97,f93])).

fof(f25,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_relset_1(sK0,sK1,sK2))
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
      | r1_partfun1(sK2,sK3) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f91,plain,
    ( spl6_6
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f26,f88,f84])).

fof(f26,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f14])).

fof(f82,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f27,f79])).

fof(f27,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f77,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f28,f74])).

fof(f28,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f72,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f29,f69])).

fof(f29,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f67,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f30,f64])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f62,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f31,f59])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:25:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (20866)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.49  % (20881)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.49  % (20885)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.49  % (20873)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.49  % (20866)Refutation not found, incomplete strategy% (20866)------------------------------
% 0.22/0.49  % (20866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (20888)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.50  % (20873)Refutation not found, incomplete strategy% (20873)------------------------------
% 0.22/0.50  % (20873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (20866)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (20866)Memory used [KB]: 10618
% 0.22/0.50  % (20866)Time elapsed: 0.082 s
% 0.22/0.50  % (20866)------------------------------
% 0.22/0.50  % (20866)------------------------------
% 0.22/0.50  % (20870)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (20873)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (20873)Memory used [KB]: 1663
% 0.22/0.50  % (20873)Time elapsed: 0.087 s
% 0.22/0.50  % (20873)------------------------------
% 0.22/0.50  % (20873)------------------------------
% 0.22/0.50  % (20878)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.50  % (20867)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (20876)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % (20871)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (20881)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f747,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f82,f91,f99,f104,f109,f130,f188,f248,f310,f414,f432,f471,f478,f511,f557,f563,f569,f575,f597,f603,f663,f664])).
% 0.22/0.51  fof(f664,plain,(
% 0.22/0.51    spl6_13 | ~spl6_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f413,f69,f132])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    spl6_13 <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    spl6_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.51  fof(f413,plain,(
% 0.22/0.51    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | ~spl6_3),
% 0.22/0.51    inference(resolution,[],[f71,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f69])).
% 0.22/0.51  fof(f663,plain,(
% 0.22/0.51    ~spl6_50 | spl6_33 | ~spl6_48),
% 0.22/0.51    inference(avatar_split_clause,[],[f420,f401,f275,f425])).
% 0.22/0.51  fof(f425,plain,(
% 0.22/0.51    spl6_50 <=> v4_relat_1(sK3,k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).
% 0.22/0.51  fof(f275,plain,(
% 0.22/0.51    spl6_33 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.22/0.51  fof(f401,plain,(
% 0.22/0.51    spl6_48 <=> v1_relat_1(sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 0.22/0.51  fof(f420,plain,(
% 0.22/0.51    k1_xboole_0 = k1_relat_1(sK3) | ~v4_relat_1(sK3,k1_xboole_0) | ~spl6_48),
% 0.22/0.51    inference(resolution,[],[f402,f119])).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0) | ~v4_relat_1(X0,k1_xboole_0)) )),
% 0.22/0.51    inference(resolution,[],[f110,f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(resolution,[],[f42,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.51  fof(f402,plain,(
% 0.22/0.51    v1_relat_1(sK3) | ~spl6_48),
% 0.22/0.51    inference(avatar_component_clause,[],[f401])).
% 0.22/0.51  fof(f603,plain,(
% 0.22/0.51    ~spl6_2 | ~spl6_8 | spl6_10 | ~spl6_52 | ~spl6_58 | ~spl6_62 | ~spl6_64),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f600])).
% 0.22/0.51  fof(f600,plain,(
% 0.22/0.51    $false | (~spl6_2 | ~spl6_8 | spl6_10 | ~spl6_52 | ~spl6_58 | ~spl6_62 | ~spl6_64)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f66,f466,f95,f555,f103,f574,f510])).
% 0.22/0.51  fof(f510,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~v1_funct_1(X2) | ~r1_partfun1(X2,sK3) | k1_funct_1(X2,X3) = k1_funct_1(sK3,X3) | ~r2_hidden(X3,k1_relat_1(X2)) | ~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),sK0)) ) | ~spl6_58),
% 0.22/0.51    inference(avatar_component_clause,[],[f509])).
% 0.22/0.51  fof(f509,plain,(
% 0.22/0.51    spl6_58 <=> ! [X3,X2] : (~r1_tarski(k1_relat_1(X2),sK0) | ~r1_partfun1(X2,sK3) | k1_funct_1(X2,X3) = k1_funct_1(sK3,X3) | ~r2_hidden(X3,k1_relat_1(X2)) | ~v1_relat_1(X2) | ~v1_funct_1(X2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).
% 0.22/0.51  fof(f574,plain,(
% 0.22/0.51    r2_hidden(sK4,k1_relat_1(sK2)) | ~spl6_64),
% 0.22/0.51    inference(avatar_component_clause,[],[f572])).
% 0.22/0.51  fof(f572,plain,(
% 0.22/0.51    spl6_64 <=> r2_hidden(sK4,k1_relat_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) | spl6_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f101])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    spl6_10 <=> k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.51  fof(f555,plain,(
% 0.22/0.51    r1_tarski(k1_relat_1(sK2),sK0) | ~spl6_62),
% 0.22/0.51    inference(avatar_component_clause,[],[f554])).
% 0.22/0.51  fof(f554,plain,(
% 0.22/0.51    spl6_62 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    r1_partfun1(sK2,sK3) | ~spl6_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f93])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    spl6_8 <=> r1_partfun1(sK2,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.51  fof(f466,plain,(
% 0.22/0.51    v1_relat_1(sK2) | ~spl6_52),
% 0.22/0.51    inference(avatar_component_clause,[],[f465])).
% 0.22/0.51  fof(f465,plain,(
% 0.22/0.51    spl6_52 <=> v1_relat_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    v1_funct_1(sK2) | ~spl6_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f64])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    spl6_2 <=> v1_funct_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.51  fof(f597,plain,(
% 0.22/0.51    spl6_8 | ~spl6_52 | ~spl6_5 | ~spl6_48 | ~spl6_2 | ~spl6_62 | ~spl6_16 | ~spl6_61),
% 0.22/0.51    inference(avatar_split_clause,[],[f596,f550,f163,f554,f64,f401,f79,f465,f93])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    spl6_5 <=> v1_funct_1(sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.51  fof(f163,plain,(
% 0.22/0.51    spl6_16 <=> sK0 = k1_relat_1(sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.22/0.51  fof(f550,plain,(
% 0.22/0.51    spl6_61 <=> k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).
% 0.22/0.51  fof(f596,plain,(
% 0.22/0.51    ~r1_tarski(k1_relat_1(sK2),sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | r1_partfun1(sK2,sK3) | (~spl6_16 | ~spl6_61)),
% 0.22/0.51    inference(forward_demodulation,[],[f595,f165])).
% 0.22/0.51  fof(f165,plain,(
% 0.22/0.51    sK0 = k1_relat_1(sK3) | ~spl6_16),
% 0.22/0.51    inference(avatar_component_clause,[],[f163])).
% 0.22/0.51  fof(f595,plain,(
% 0.22/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | ~v1_relat_1(sK2) | r1_partfun1(sK2,sK3) | ~spl6_61),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f594])).
% 0.22/0.51  fof(f594,plain,(
% 0.22/0.51    k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK2,sK5(sK2,sK3)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | ~v1_relat_1(sK2) | r1_partfun1(sK2,sK3) | ~spl6_61),
% 0.22/0.51    inference(superposition,[],[f36,f552])).
% 0.22/0.51  fof(f552,plain,(
% 0.22/0.51    k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) | ~spl6_61),
% 0.22/0.51    inference(avatar_component_clause,[],[f550])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X0) | r1_partfun1(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) => (r1_partfun1(X0,X1) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_partfun1)).
% 0.22/0.51  fof(f575,plain,(
% 0.22/0.51    spl6_64 | ~spl6_11 | ~spl6_12),
% 0.22/0.51    inference(avatar_split_clause,[],[f570,f127,f106,f572])).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    spl6_11 <=> r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.51  fof(f127,plain,(
% 0.22/0.51    spl6_12 <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.51  fof(f570,plain,(
% 0.22/0.51    r2_hidden(sK4,k1_relat_1(sK2)) | (~spl6_11 | ~spl6_12)),
% 0.22/0.51    inference(forward_demodulation,[],[f108,f129])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl6_12),
% 0.22/0.51    inference(avatar_component_clause,[],[f127])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)) | ~spl6_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f106])).
% 0.22/0.51  fof(f569,plain,(
% 0.22/0.51    ~spl6_1 | spl6_63),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f568])).
% 0.22/0.51  fof(f568,plain,(
% 0.22/0.51    $false | (~spl6_1 | spl6_63)),
% 0.22/0.51    inference(subsumption_resolution,[],[f61,f565])).
% 0.22/0.51  fof(f565,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) ) | spl6_63),
% 0.22/0.51    inference(resolution,[],[f562,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.51    inference(pure_predicate_removal,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.51  fof(f562,plain,(
% 0.22/0.51    ~v4_relat_1(sK2,sK0) | spl6_63),
% 0.22/0.51    inference(avatar_component_clause,[],[f560])).
% 0.22/0.51  fof(f560,plain,(
% 0.22/0.51    spl6_63 <=> v4_relat_1(sK2,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    spl6_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.51  fof(f563,plain,(
% 0.22/0.51    ~spl6_63 | ~spl6_52 | spl6_62),
% 0.22/0.51    inference(avatar_split_clause,[],[f558,f554,f465,f560])).
% 0.22/0.51  fof(f558,plain,(
% 0.22/0.51    ~v1_relat_1(sK2) | ~v4_relat_1(sK2,sK0) | spl6_62),
% 0.22/0.51    inference(resolution,[],[f556,f39])).
% 0.22/0.51  fof(f556,plain,(
% 0.22/0.51    ~r1_tarski(k1_relat_1(sK2),sK0) | spl6_62),
% 0.22/0.51    inference(avatar_component_clause,[],[f554])).
% 0.22/0.51  fof(f557,plain,(
% 0.22/0.51    ~spl6_5 | ~spl6_48 | spl6_61 | ~spl6_62 | spl6_8 | ~spl6_16 | ~spl6_53),
% 0.22/0.51    inference(avatar_split_clause,[],[f548,f469,f163,f93,f554,f550,f401,f79])).
% 0.22/0.51  fof(f469,plain,(
% 0.22/0.51    spl6_53 <=> ! [X0] : (~v1_relat_1(X0) | k1_funct_1(sK2,sK5(sK2,X0)) = k1_funct_1(sK3,sK5(sK2,X0)) | r1_partfun1(sK2,X0) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) | ~v1_funct_1(X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 0.22/0.51  fof(f548,plain,(
% 0.22/0.51    ~r1_tarski(k1_relat_1(sK2),sK0) | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | (spl6_8 | ~spl6_16 | ~spl6_53)),
% 0.22/0.51    inference(forward_demodulation,[],[f547,f165])).
% 0.22/0.51  fof(f547,plain,(
% 0.22/0.51    k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) | ~v1_relat_1(sK3) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | ~v1_funct_1(sK3) | (spl6_8 | ~spl6_53)),
% 0.22/0.51    inference(resolution,[],[f470,f94])).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    ~r1_partfun1(sK2,sK3) | spl6_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f93])).
% 0.22/0.51  fof(f470,plain,(
% 0.22/0.51    ( ! [X0] : (r1_partfun1(sK2,X0) | k1_funct_1(sK2,sK5(sK2,X0)) = k1_funct_1(sK3,sK5(sK2,X0)) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) | ~v1_funct_1(X0)) ) | ~spl6_53),
% 0.22/0.51    inference(avatar_component_clause,[],[f469])).
% 0.22/0.51  fof(f511,plain,(
% 0.22/0.51    ~spl6_48 | spl6_58 | ~spl6_5 | ~spl6_16),
% 0.22/0.51    inference(avatar_split_clause,[],[f507,f163,f79,f509,f401])).
% 0.22/0.51  fof(f507,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~r1_tarski(k1_relat_1(X2),sK0) | ~v1_funct_1(X2) | ~v1_relat_1(sK3) | ~v1_relat_1(X2) | ~r2_hidden(X3,k1_relat_1(X2)) | k1_funct_1(X2,X3) = k1_funct_1(sK3,X3) | ~r1_partfun1(X2,sK3)) ) | (~spl6_5 | ~spl6_16)),
% 0.22/0.51    inference(forward_demodulation,[],[f498,f165])).
% 0.22/0.51  fof(f498,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~v1_funct_1(X2) | ~v1_relat_1(sK3) | ~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),k1_relat_1(sK3)) | ~r2_hidden(X3,k1_relat_1(X2)) | k1_funct_1(X2,X3) = k1_funct_1(sK3,X3) | ~r1_partfun1(X2,sK3)) ) | ~spl6_5),
% 0.22/0.51    inference(resolution,[],[f34,f81])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    v1_funct_1(sK3) | ~spl6_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f79])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0)) | k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r1_partfun1(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f478,plain,(
% 0.22/0.51    ~spl6_1 | spl6_52),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f476])).
% 0.22/0.51  fof(f476,plain,(
% 0.22/0.51    $false | (~spl6_1 | spl6_52)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f37,f61,f467,f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.51  fof(f467,plain,(
% 0.22/0.51    ~v1_relat_1(sK2) | spl6_52),
% 0.22/0.51    inference(avatar_component_clause,[],[f465])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.51  fof(f471,plain,(
% 0.22/0.51    ~spl6_52 | spl6_53 | ~spl6_2 | ~spl6_9 | ~spl6_12),
% 0.22/0.51    inference(avatar_split_clause,[],[f462,f127,f97,f64,f469,f465])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    spl6_9 <=> ! [X4] : (~r2_hidden(X4,k1_relset_1(sK0,sK1,sK2)) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.51  fof(f462,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_funct_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) | ~v1_relat_1(sK2) | r1_partfun1(sK2,X0) | k1_funct_1(sK2,sK5(sK2,X0)) = k1_funct_1(sK3,sK5(sK2,X0))) ) | (~spl6_9 | ~spl6_12)),
% 0.22/0.51    inference(resolution,[],[f35,f136])).
% 0.22/0.51  fof(f136,plain,(
% 0.22/0.51    ( ! [X4] : (~r2_hidden(X4,k1_relat_1(sK2)) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) ) | (~spl6_9 | ~spl6_12)),
% 0.22/0.51    inference(backward_demodulation,[],[f98,f129])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    ( ! [X4] : (~r2_hidden(X4,k1_relset_1(sK0,sK1,sK2)) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) ) | ~spl6_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f97])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X0) | r1_partfun1(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f432,plain,(
% 0.22/0.51    ~spl6_28 | spl6_50),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f431])).
% 0.22/0.51  fof(f431,plain,(
% 0.22/0.51    $false | (~spl6_28 | spl6_50)),
% 0.22/0.51    inference(subsumption_resolution,[],[f247,f429])).
% 0.22/0.51  fof(f429,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | spl6_50),
% 0.22/0.51    inference(resolution,[],[f427,f44])).
% 0.22/0.51  fof(f427,plain,(
% 0.22/0.51    ~v4_relat_1(sK3,k1_xboole_0) | spl6_50),
% 0.22/0.51    inference(avatar_component_clause,[],[f425])).
% 0.22/0.51  fof(f247,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl6_28),
% 0.22/0.51    inference(avatar_component_clause,[],[f245])).
% 0.22/0.51  fof(f245,plain,(
% 0.22/0.51    spl6_28 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.22/0.51  fof(f414,plain,(
% 0.22/0.51    ~spl6_3 | spl6_48),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f409])).
% 0.22/0.51  fof(f409,plain,(
% 0.22/0.51    $false | (~spl6_3 | spl6_48)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f403,f37,f71,f33])).
% 0.22/0.51  fof(f403,plain,(
% 0.22/0.51    ~v1_relat_1(sK3) | spl6_48),
% 0.22/0.51    inference(avatar_component_clause,[],[f401])).
% 0.22/0.51  fof(f310,plain,(
% 0.22/0.51    ~spl6_33 | ~spl6_6 | spl6_16),
% 0.22/0.51    inference(avatar_split_clause,[],[f309,f163,f84,f275])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    spl6_6 <=> k1_xboole_0 = sK0),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.51  fof(f309,plain,(
% 0.22/0.51    k1_xboole_0 != k1_relat_1(sK3) | (~spl6_6 | spl6_16)),
% 0.22/0.51    inference(forward_demodulation,[],[f164,f86])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    k1_xboole_0 = sK0 | ~spl6_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f84])).
% 0.22/0.51  fof(f164,plain,(
% 0.22/0.51    sK0 != k1_relat_1(sK3) | spl6_16),
% 0.22/0.51    inference(avatar_component_clause,[],[f163])).
% 0.22/0.51  fof(f248,plain,(
% 0.22/0.51    spl6_28 | ~spl6_3 | ~spl6_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f243,f84,f69,f245])).
% 0.22/0.51  fof(f243,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl6_3 | ~spl6_6)),
% 0.22/0.51    inference(forward_demodulation,[],[f71,f86])).
% 0.22/0.51  fof(f188,plain,(
% 0.22/0.51    ~spl6_4 | spl6_7 | spl6_16 | ~spl6_3 | ~spl6_13),
% 0.22/0.51    inference(avatar_split_clause,[],[f187,f132,f69,f163,f88,f74])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    spl6_4 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    spl6_7 <=> k1_xboole_0 = sK1),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.51  fof(f187,plain,(
% 0.22/0.51    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1 | ~v1_funct_2(sK3,sK0,sK1) | (~spl6_3 | ~spl6_13)),
% 0.22/0.51    inference(forward_demodulation,[],[f184,f134])).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | ~spl6_13),
% 0.22/0.51    inference(avatar_component_clause,[],[f132])).
% 0.22/0.51  fof(f184,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl6_3),
% 0.22/0.51    inference(resolution,[],[f50,f71])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(flattening,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.51  fof(f130,plain,(
% 0.22/0.51    spl6_12 | ~spl6_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f124,f59,f127])).
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl6_1),
% 0.22/0.51    inference(resolution,[],[f43,f61])).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    ~spl6_8 | spl6_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f23,f106,f93])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)) | ~r1_partfun1(sK2,sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (? [X3] : ((r1_partfun1(X2,X3) <~> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.22/0.51    inference(flattening,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (? [X3] : (((r1_partfun1(X2,X3) <~> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f10])).
% 0.22/0.51  fof(f10,conjecture,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_2)).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    ~spl6_8 | ~spl6_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f24,f101,f93])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) | ~r1_partfun1(sK2,sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  % (20879)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    spl6_8 | spl6_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f25,f97,f93])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ( ! [X4] : (~r2_hidden(X4,k1_relset_1(sK0,sK1,sK2)) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | r1_partfun1(sK2,sK3)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    spl6_6 | ~spl6_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f26,f88,f84])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    spl6_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f27,f79])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    v1_funct_1(sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    spl6_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f28,f74])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    spl6_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f29,f69])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    spl6_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f30,f64])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    v1_funct_1(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    spl6_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f31,f59])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (20881)------------------------------
% 0.22/0.51  % (20881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (20881)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (20881)Memory used [KB]: 6652
% 0.22/0.51  % (20881)Time elapsed: 0.107 s
% 0.22/0.51  % (20881)------------------------------
% 0.22/0.51  % (20881)------------------------------
% 0.22/0.51  % (20859)Success in time 0.148 s
%------------------------------------------------------------------------------
