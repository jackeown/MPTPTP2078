%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:53 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 321 expanded)
%              Number of leaves         :   42 ( 149 expanded)
%              Depth                    :    9
%              Number of atoms          :  601 (1100 expanded)
%              Number of equality atoms :   82 ( 146 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f706,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f104,f109,f114,f129,f138,f143,f153,f159,f168,f175,f206,f223,f233,f238,f254,f275,f312,f314,f374,f413,f526,f532,f537,f612,f638,f702,f705])).

fof(f705,plain,
    ( ~ spl2_37
    | ~ spl2_46
    | spl2_54 ),
    inference(avatar_contradiction_clause,[],[f703])).

fof(f703,plain,
    ( $false
    | ~ spl2_37
    | ~ spl2_46
    | spl2_54 ),
    inference(unit_resulting_resolution,[],[f412,f637,f701,f92])).

fof(f92,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f701,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | spl2_54 ),
    inference(avatar_component_clause,[],[f699])).

fof(f699,plain,
    ( spl2_54
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f637,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl2_46 ),
    inference(avatar_component_clause,[],[f635])).

fof(f635,plain,
    ( spl2_46
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f412,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f410])).

fof(f410,plain,
    ( spl2_37
  <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f702,plain,
    ( ~ spl2_54
    | spl2_12
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f664,f165,f161,f699])).

fof(f161,plain,
    ( spl2_12
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f165,plain,
    ( spl2_13
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f664,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | spl2_12
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f162,f167])).

fof(f167,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f165])).

fof(f162,plain,
    ( sK0 != k1_relset_1(sK0,sK0,sK1)
    | spl2_12 ),
    inference(avatar_component_clause,[],[f161])).

fof(f638,plain,
    ( spl2_46
    | ~ spl2_4
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f617,f165,f111,f635])).

fof(f111,plain,
    ( spl2_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f617,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl2_4
    | ~ spl2_13 ),
    inference(backward_demodulation,[],[f113,f167])).

fof(f113,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f111])).

fof(f612,plain,
    ( ~ spl2_8
    | ~ spl2_11
    | ~ spl2_33
    | ~ spl2_43 ),
    inference(avatar_contradiction_clause,[],[f610])).

fof(f610,plain,
    ( $false
    | ~ spl2_8
    | ~ spl2_11
    | ~ spl2_33
    | ~ spl2_43 ),
    inference(unit_resulting_resolution,[],[f158,f142,f310,f536])).

fof(f536,plain,
    ( ! [X0] :
        ( ~ r2_relset_1(sK0,sK0,k6_partfun1(X0),k6_partfun1(sK0))
        | ~ v5_relat_1(sK1,X0)
        | ~ v2_funct_2(sK1,X0) )
    | ~ spl2_43 ),
    inference(avatar_component_clause,[],[f535])).

fof(f535,plain,
    ( spl2_43
  <=> ! [X0] :
        ( ~ r2_relset_1(sK0,sK0,k6_partfun1(X0),k6_partfun1(sK0))
        | ~ v5_relat_1(sK1,X0)
        | ~ v2_funct_2(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f310,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f309])).

fof(f309,plain,
    ( spl2_33
  <=> r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f142,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl2_8
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f158,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl2_11
  <=> v2_funct_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f537,plain,
    ( ~ spl2_5
    | spl2_43
    | spl2_42 ),
    inference(avatar_split_clause,[],[f533,f529,f535,f126])).

fof(f126,plain,
    ( spl2_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f529,plain,
    ( spl2_42
  <=> r2_relset_1(sK0,sK0,k6_partfun1(k2_relat_1(sK1)),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f533,plain,
    ( ! [X0] :
        ( ~ r2_relset_1(sK0,sK0,k6_partfun1(X0),k6_partfun1(sK0))
        | ~ v2_funct_2(sK1,X0)
        | ~ v5_relat_1(sK1,X0)
        | ~ v1_relat_1(sK1) )
    | spl2_42 ),
    inference(superposition,[],[f531,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f531,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(k2_relat_1(sK1)),k6_partfun1(sK0))
    | spl2_42 ),
    inference(avatar_component_clause,[],[f529])).

fof(f532,plain,
    ( ~ spl2_5
    | ~ spl2_1
    | ~ spl2_10
    | ~ spl2_42
    | spl2_41 ),
    inference(avatar_split_clause,[],[f527,f523,f529,f150,f96,f126])).

fof(f96,plain,
    ( spl2_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f150,plain,
    ( spl2_10
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f523,plain,
    ( spl2_41
  <=> r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f527,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(k2_relat_1(sK1)),k6_partfun1(sK0))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl2_41 ),
    inference(superposition,[],[f525,f85])).

fof(f85,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f60,f53])).

fof(f53,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f60,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f525,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | spl2_41 ),
    inference(avatar_component_clause,[],[f523])).

fof(f526,plain,
    ( ~ spl2_20
    | ~ spl2_24
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_41
    | spl2_35 ),
    inference(avatar_split_clause,[],[f375,f371,f523,f111,f96,f251,f230])).

fof(f230,plain,
    ( spl2_20
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f251,plain,
    ( spl2_24
  <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f371,plain,
    ( spl2_35
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f375,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | spl2_35 ),
    inference(superposition,[],[f373,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f373,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | spl2_35 ),
    inference(avatar_component_clause,[],[f371])).

fof(f413,plain,
    ( spl2_37
    | ~ spl2_2
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f386,f165,f101,f410])).

fof(f101,plain,
    ( spl2_2
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f386,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl2_2
    | ~ spl2_13 ),
    inference(backward_demodulation,[],[f103,f167])).

fof(f103,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f374,plain,
    ( ~ spl2_35
    | spl2_7
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f369,f220,f135,f371])).

fof(f135,plain,
    ( spl2_7
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f220,plain,
    ( spl2_19
  <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f369,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | spl2_7
    | ~ spl2_19 ),
    inference(forward_demodulation,[],[f137,f222])).

fof(f222,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f220])).

fof(f137,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | spl2_7 ),
    inference(avatar_component_clause,[],[f135])).

fof(f314,plain,(
    spl2_33 ),
    inference(avatar_contradiction_clause,[],[f313])).

fof(f313,plain,
    ( $false
    | spl2_33 ),
    inference(unit_resulting_resolution,[],[f54,f311,f94])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f311,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | spl2_33 ),
    inference(avatar_component_clause,[],[f309])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f312,plain,
    ( ~ spl2_5
    | ~ spl2_1
    | ~ spl2_10
    | ~ spl2_33
    | ~ spl2_14
    | spl2_26 ),
    inference(avatar_split_clause,[],[f287,f272,f172,f309,f150,f96,f126])).

fof(f172,plain,
    ( spl2_14
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f272,plain,
    ( spl2_26
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f287,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl2_14
    | spl2_26 ),
    inference(forward_demodulation,[],[f286,f174])).

fof(f174,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f172])).

fof(f286,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl2_26 ),
    inference(superposition,[],[f274,f86])).

fof(f86,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f59,f53])).

fof(f59,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f274,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | spl2_26 ),
    inference(avatar_component_clause,[],[f272])).

fof(f275,plain,
    ( ~ spl2_1
    | ~ spl2_4
    | ~ spl2_20
    | ~ spl2_24
    | ~ spl2_26
    | spl2_21 ),
    inference(avatar_split_clause,[],[f239,f235,f272,f251,f230,f111,f96])).

fof(f235,plain,
    ( spl2_21
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f239,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | spl2_21 ),
    inference(superposition,[],[f237,f82])).

fof(f237,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | spl2_21 ),
    inference(avatar_component_clause,[],[f235])).

fof(f254,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | spl2_24
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f228,f220,f251,f111,f106,f101,f96])).

fof(f106,plain,
    ( spl2_3
  <=> v3_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f228,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl2_19 ),
    inference(superposition,[],[f67,f222])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f238,plain,
    ( ~ spl2_21
    | spl2_6
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f225,f220,f131,f235])).

fof(f131,plain,
    ( spl2_6
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f225,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | spl2_6
    | ~ spl2_19 ),
    inference(backward_demodulation,[],[f133,f222])).

fof(f133,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f131])).

fof(f233,plain,
    ( spl2_20
    | ~ spl2_16
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f224,f220,f203,f230])).

fof(f203,plain,
    ( spl2_16
  <=> v1_funct_1(k2_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f224,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl2_16
    | ~ spl2_19 ),
    inference(backward_demodulation,[],[f205,f222])).

fof(f205,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f203])).

fof(f223,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_19
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f116,f111,f220,f106,f101,f96])).

fof(f116,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f113,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f206,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_16
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f115,f111,f203,f106,f101,f96])).

fof(f115,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f113,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v1_funct_1(k2_funct_2(X0,X1))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f175,plain,
    ( ~ spl2_4
    | spl2_14
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f169,f161,f172,f111])).

fof(f169,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_12 ),
    inference(superposition,[],[f163,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f163,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f161])).

fof(f168,plain,
    ( spl2_12
    | spl2_13
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f119,f111,f101,f165,f161])).

fof(f119,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | k1_xboole_0 = sK0
    | sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f113,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f159,plain,
    ( spl2_11
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f122,f111,f106,f96,f156])).

fof(f122,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_2(sK1,sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f113,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f153,plain,
    ( spl2_10
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f121,f111,f106,f96,f150])).

fof(f121,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f113,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f143,plain,
    ( spl2_8
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f118,f111,f140])).

fof(f118,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f113,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f138,plain,
    ( ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f52,f135,f131])).

fof(f52,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f43])).

fof(f43,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
        | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

fof(f129,plain,
    ( spl2_5
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f117,f111,f126])).

fof(f117,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f113,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f114,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f51,f111])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f109,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f50,f106])).

fof(f50,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f104,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f49,f101])).

fof(f49,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f99,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f48,f96])).

fof(f48,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:50:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (11166)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (11158)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (11146)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (11150)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (11155)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (11156)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (11154)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (11145)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (11157)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (11162)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (11169)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.53  % (11144)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (11160)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (11171)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (11164)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (11165)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (11161)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (11148)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (11149)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.40/0.54  % (11147)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.40/0.54  % (11167)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.40/0.54  % (11168)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.40/0.54  % (11170)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.40/0.54  % (11152)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.40/0.54  % (11163)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.40/0.54  % (11159)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.40/0.55  % (11172)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.40/0.55  % (11153)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.40/0.55  % (11173)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.40/0.55  % (11151)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.51/0.56  % (11160)Refutation not found, incomplete strategy% (11160)------------------------------
% 1.51/0.56  % (11160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (11160)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.56  
% 1.51/0.56  % (11160)Memory used [KB]: 10746
% 1.51/0.56  % (11160)Time elapsed: 0.149 s
% 1.51/0.56  % (11160)------------------------------
% 1.51/0.56  % (11160)------------------------------
% 1.51/0.57  % (11154)Refutation found. Thanks to Tanya!
% 1.51/0.57  % SZS status Theorem for theBenchmark
% 1.51/0.57  % SZS output start Proof for theBenchmark
% 1.51/0.57  fof(f706,plain,(
% 1.51/0.57    $false),
% 1.51/0.57    inference(avatar_sat_refutation,[],[f99,f104,f109,f114,f129,f138,f143,f153,f159,f168,f175,f206,f223,f233,f238,f254,f275,f312,f314,f374,f413,f526,f532,f537,f612,f638,f702,f705])).
% 1.51/0.57  fof(f705,plain,(
% 1.51/0.57    ~spl2_37 | ~spl2_46 | spl2_54),
% 1.51/0.57    inference(avatar_contradiction_clause,[],[f703])).
% 1.51/0.57  fof(f703,plain,(
% 1.51/0.57    $false | (~spl2_37 | ~spl2_46 | spl2_54)),
% 1.51/0.57    inference(unit_resulting_resolution,[],[f412,f637,f701,f92])).
% 1.51/0.57  fof(f92,plain,(
% 1.51/0.57    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 1.51/0.57    inference(equality_resolution,[],[f72])).
% 1.51/0.57  fof(f72,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.57    inference(cnf_transformation,[],[f46])).
% 1.51/0.57  fof(f46,plain,(
% 1.51/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.57    inference(nnf_transformation,[],[f36])).
% 1.51/0.57  fof(f36,plain,(
% 1.51/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.57    inference(flattening,[],[f35])).
% 1.51/0.57  fof(f35,plain,(
% 1.51/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.57    inference(ennf_transformation,[],[f9])).
% 1.51/0.57  fof(f9,axiom,(
% 1.51/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.51/0.57  fof(f701,plain,(
% 1.51/0.57    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) | spl2_54),
% 1.51/0.57    inference(avatar_component_clause,[],[f699])).
% 1.51/0.57  fof(f699,plain,(
% 1.51/0.57    spl2_54 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).
% 1.51/0.57  fof(f637,plain,(
% 1.51/0.57    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl2_46),
% 1.51/0.57    inference(avatar_component_clause,[],[f635])).
% 1.51/0.57  fof(f635,plain,(
% 1.51/0.57    spl2_46 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 1.51/0.57  fof(f412,plain,(
% 1.51/0.57    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | ~spl2_37),
% 1.51/0.57    inference(avatar_component_clause,[],[f410])).
% 1.51/0.57  fof(f410,plain,(
% 1.51/0.57    spl2_37 <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 1.51/0.57  fof(f702,plain,(
% 1.51/0.57    ~spl2_54 | spl2_12 | ~spl2_13),
% 1.51/0.57    inference(avatar_split_clause,[],[f664,f165,f161,f699])).
% 1.51/0.57  fof(f161,plain,(
% 1.51/0.57    spl2_12 <=> sK0 = k1_relset_1(sK0,sK0,sK1)),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 1.51/0.57  fof(f165,plain,(
% 1.51/0.57    spl2_13 <=> k1_xboole_0 = sK0),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 1.51/0.57  fof(f664,plain,(
% 1.51/0.57    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) | (spl2_12 | ~spl2_13)),
% 1.51/0.57    inference(forward_demodulation,[],[f162,f167])).
% 1.51/0.57  fof(f167,plain,(
% 1.51/0.57    k1_xboole_0 = sK0 | ~spl2_13),
% 1.51/0.57    inference(avatar_component_clause,[],[f165])).
% 1.51/0.57  fof(f162,plain,(
% 1.51/0.57    sK0 != k1_relset_1(sK0,sK0,sK1) | spl2_12),
% 1.51/0.57    inference(avatar_component_clause,[],[f161])).
% 1.51/0.57  fof(f638,plain,(
% 1.51/0.57    spl2_46 | ~spl2_4 | ~spl2_13),
% 1.51/0.57    inference(avatar_split_clause,[],[f617,f165,f111,f635])).
% 1.51/0.57  fof(f111,plain,(
% 1.51/0.57    spl2_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.51/0.57  fof(f617,plain,(
% 1.51/0.57    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl2_4 | ~spl2_13)),
% 1.51/0.57    inference(backward_demodulation,[],[f113,f167])).
% 1.51/0.57  fof(f113,plain,(
% 1.51/0.57    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl2_4),
% 1.51/0.57    inference(avatar_component_clause,[],[f111])).
% 1.51/0.57  fof(f612,plain,(
% 1.51/0.57    ~spl2_8 | ~spl2_11 | ~spl2_33 | ~spl2_43),
% 1.51/0.57    inference(avatar_contradiction_clause,[],[f610])).
% 1.51/0.57  fof(f610,plain,(
% 1.51/0.57    $false | (~spl2_8 | ~spl2_11 | ~spl2_33 | ~spl2_43)),
% 1.51/0.57    inference(unit_resulting_resolution,[],[f158,f142,f310,f536])).
% 1.51/0.57  fof(f536,plain,(
% 1.51/0.57    ( ! [X0] : (~r2_relset_1(sK0,sK0,k6_partfun1(X0),k6_partfun1(sK0)) | ~v5_relat_1(sK1,X0) | ~v2_funct_2(sK1,X0)) ) | ~spl2_43),
% 1.51/0.57    inference(avatar_component_clause,[],[f535])).
% 1.51/0.57  fof(f535,plain,(
% 1.51/0.57    spl2_43 <=> ! [X0] : (~r2_relset_1(sK0,sK0,k6_partfun1(X0),k6_partfun1(sK0)) | ~v5_relat_1(sK1,X0) | ~v2_funct_2(sK1,X0))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 1.51/0.57  fof(f310,plain,(
% 1.51/0.57    r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | ~spl2_33),
% 1.51/0.57    inference(avatar_component_clause,[],[f309])).
% 1.51/0.57  fof(f309,plain,(
% 1.51/0.57    spl2_33 <=> r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 1.51/0.57  fof(f142,plain,(
% 1.51/0.57    v5_relat_1(sK1,sK0) | ~spl2_8),
% 1.51/0.57    inference(avatar_component_clause,[],[f140])).
% 1.51/0.57  fof(f140,plain,(
% 1.51/0.57    spl2_8 <=> v5_relat_1(sK1,sK0)),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.51/0.57  fof(f158,plain,(
% 1.51/0.57    v2_funct_2(sK1,sK0) | ~spl2_11),
% 1.51/0.57    inference(avatar_component_clause,[],[f156])).
% 1.51/0.57  fof(f156,plain,(
% 1.51/0.57    spl2_11 <=> v2_funct_2(sK1,sK0)),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.51/0.57  fof(f537,plain,(
% 1.51/0.57    ~spl2_5 | spl2_43 | spl2_42),
% 1.51/0.57    inference(avatar_split_clause,[],[f533,f529,f535,f126])).
% 1.51/0.57  fof(f126,plain,(
% 1.51/0.57    spl2_5 <=> v1_relat_1(sK1)),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.51/0.57  fof(f529,plain,(
% 1.51/0.57    spl2_42 <=> r2_relset_1(sK0,sK0,k6_partfun1(k2_relat_1(sK1)),k6_partfun1(sK0))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 1.51/0.57  fof(f533,plain,(
% 1.51/0.57    ( ! [X0] : (~r2_relset_1(sK0,sK0,k6_partfun1(X0),k6_partfun1(sK0)) | ~v2_funct_2(sK1,X0) | ~v5_relat_1(sK1,X0) | ~v1_relat_1(sK1)) ) | spl2_42),
% 1.51/0.57    inference(superposition,[],[f531,f61])).
% 1.51/0.57  fof(f61,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f45])).
% 1.51/0.57  fof(f45,plain,(
% 1.51/0.57    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.51/0.57    inference(nnf_transformation,[],[f27])).
% 1.51/0.57  fof(f27,plain,(
% 1.51/0.57    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.51/0.57    inference(flattening,[],[f26])).
% 1.51/0.57  fof(f26,plain,(
% 1.51/0.57    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.51/0.57    inference(ennf_transformation,[],[f10])).
% 1.51/0.57  fof(f10,axiom,(
% 1.51/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 1.51/0.57  fof(f531,plain,(
% 1.51/0.57    ~r2_relset_1(sK0,sK0,k6_partfun1(k2_relat_1(sK1)),k6_partfun1(sK0)) | spl2_42),
% 1.51/0.57    inference(avatar_component_clause,[],[f529])).
% 1.51/0.57  fof(f532,plain,(
% 1.51/0.57    ~spl2_5 | ~spl2_1 | ~spl2_10 | ~spl2_42 | spl2_41),
% 1.51/0.57    inference(avatar_split_clause,[],[f527,f523,f529,f150,f96,f126])).
% 1.51/0.57  fof(f96,plain,(
% 1.51/0.57    spl2_1 <=> v1_funct_1(sK1)),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.51/0.57  fof(f150,plain,(
% 1.51/0.57    spl2_10 <=> v2_funct_1(sK1)),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 1.51/0.57  fof(f523,plain,(
% 1.51/0.57    spl2_41 <=> r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 1.51/0.57  fof(f527,plain,(
% 1.51/0.57    ~r2_relset_1(sK0,sK0,k6_partfun1(k2_relat_1(sK1)),k6_partfun1(sK0)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl2_41),
% 1.51/0.57    inference(superposition,[],[f525,f85])).
% 1.51/0.57  fof(f85,plain,(
% 1.51/0.57    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.51/0.57    inference(definition_unfolding,[],[f60,f53])).
% 1.51/0.57  fof(f53,plain,(
% 1.51/0.57    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f15])).
% 1.51/0.57  fof(f15,axiom,(
% 1.51/0.57    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.51/0.57  fof(f60,plain,(
% 1.51/0.57    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f25])).
% 1.51/0.57  fof(f25,plain,(
% 1.51/0.57    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.51/0.57    inference(flattening,[],[f24])).
% 1.51/0.57  fof(f24,plain,(
% 1.51/0.57    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.51/0.57    inference(ennf_transformation,[],[f3])).
% 1.51/0.57  fof(f3,axiom,(
% 1.51/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 1.51/0.57  fof(f525,plain,(
% 1.51/0.57    ~r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | spl2_41),
% 1.51/0.57    inference(avatar_component_clause,[],[f523])).
% 1.51/0.57  fof(f526,plain,(
% 1.51/0.57    ~spl2_20 | ~spl2_24 | ~spl2_1 | ~spl2_4 | ~spl2_41 | spl2_35),
% 1.51/0.57    inference(avatar_split_clause,[],[f375,f371,f523,f111,f96,f251,f230])).
% 1.51/0.57  fof(f230,plain,(
% 1.51/0.57    spl2_20 <=> v1_funct_1(k2_funct_1(sK1))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 1.51/0.57  fof(f251,plain,(
% 1.51/0.57    spl2_24 <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 1.51/0.57  fof(f371,plain,(
% 1.51/0.57    spl2_35 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 1.51/0.57  fof(f375,plain,(
% 1.51/0.57    ~r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1)) | spl2_35),
% 1.51/0.57    inference(superposition,[],[f373,f82])).
% 1.51/0.57  fof(f82,plain,(
% 1.51/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f42])).
% 1.51/0.57  fof(f42,plain,(
% 1.51/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.51/0.57    inference(flattening,[],[f41])).
% 1.51/0.57  fof(f41,plain,(
% 1.51/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.51/0.57    inference(ennf_transformation,[],[f13])).
% 1.51/0.57  fof(f13,axiom,(
% 1.51/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.51/0.57  fof(f373,plain,(
% 1.51/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | spl2_35),
% 1.51/0.57    inference(avatar_component_clause,[],[f371])).
% 1.51/0.57  fof(f413,plain,(
% 1.51/0.57    spl2_37 | ~spl2_2 | ~spl2_13),
% 1.51/0.57    inference(avatar_split_clause,[],[f386,f165,f101,f410])).
% 1.51/0.57  fof(f101,plain,(
% 1.51/0.57    spl2_2 <=> v1_funct_2(sK1,sK0,sK0)),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.51/0.57  fof(f386,plain,(
% 1.51/0.57    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | (~spl2_2 | ~spl2_13)),
% 1.51/0.57    inference(backward_demodulation,[],[f103,f167])).
% 1.51/0.57  fof(f103,plain,(
% 1.51/0.57    v1_funct_2(sK1,sK0,sK0) | ~spl2_2),
% 1.51/0.57    inference(avatar_component_clause,[],[f101])).
% 1.51/0.57  fof(f374,plain,(
% 1.51/0.57    ~spl2_35 | spl2_7 | ~spl2_19),
% 1.51/0.57    inference(avatar_split_clause,[],[f369,f220,f135,f371])).
% 1.51/0.57  fof(f135,plain,(
% 1.51/0.57    spl2_7 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.51/0.57  fof(f220,plain,(
% 1.51/0.57    spl2_19 <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 1.51/0.57  fof(f369,plain,(
% 1.51/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | (spl2_7 | ~spl2_19)),
% 1.51/0.57    inference(forward_demodulation,[],[f137,f222])).
% 1.51/0.57  fof(f222,plain,(
% 1.51/0.57    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~spl2_19),
% 1.51/0.57    inference(avatar_component_clause,[],[f220])).
% 1.51/0.57  fof(f137,plain,(
% 1.51/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | spl2_7),
% 1.51/0.57    inference(avatar_component_clause,[],[f135])).
% 1.51/0.57  fof(f314,plain,(
% 1.51/0.57    spl2_33),
% 1.51/0.57    inference(avatar_contradiction_clause,[],[f313])).
% 1.51/0.57  fof(f313,plain,(
% 1.51/0.57    $false | spl2_33),
% 1.51/0.57    inference(unit_resulting_resolution,[],[f54,f311,f94])).
% 1.51/0.57  fof(f94,plain,(
% 1.51/0.57    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.51/0.57    inference(duplicate_literal_removal,[],[f93])).
% 1.51/0.57  fof(f93,plain,(
% 1.51/0.57    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.57    inference(equality_resolution,[],[f81])).
% 1.51/0.57  fof(f81,plain,(
% 1.51/0.57    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.57    inference(cnf_transformation,[],[f47])).
% 1.51/0.57  fof(f47,plain,(
% 1.51/0.57    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.57    inference(nnf_transformation,[],[f40])).
% 1.51/0.57  fof(f40,plain,(
% 1.51/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.57    inference(flattening,[],[f39])).
% 1.51/0.57  fof(f39,plain,(
% 1.51/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.51/0.57    inference(ennf_transformation,[],[f7])).
% 1.51/0.57  fof(f7,axiom,(
% 1.51/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.51/0.57  fof(f311,plain,(
% 1.51/0.57    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | spl2_33),
% 1.51/0.57    inference(avatar_component_clause,[],[f309])).
% 1.51/0.57  fof(f54,plain,(
% 1.51/0.57    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.51/0.57    inference(cnf_transformation,[],[f18])).
% 1.51/0.57  fof(f18,plain,(
% 1.51/0.57    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.51/0.57    inference(pure_predicate_removal,[],[f12])).
% 1.51/0.57  fof(f12,axiom,(
% 1.51/0.57    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.51/0.57  fof(f312,plain,(
% 1.51/0.57    ~spl2_5 | ~spl2_1 | ~spl2_10 | ~spl2_33 | ~spl2_14 | spl2_26),
% 1.51/0.57    inference(avatar_split_clause,[],[f287,f272,f172,f309,f150,f96,f126])).
% 1.51/0.57  fof(f172,plain,(
% 1.51/0.57    spl2_14 <=> sK0 = k1_relat_1(sK1)),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 1.51/0.57  fof(f272,plain,(
% 1.51/0.57    spl2_26 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 1.51/0.57  fof(f287,plain,(
% 1.51/0.57    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl2_14 | spl2_26)),
% 1.51/0.57    inference(forward_demodulation,[],[f286,f174])).
% 1.51/0.57  fof(f174,plain,(
% 1.51/0.57    sK0 = k1_relat_1(sK1) | ~spl2_14),
% 1.51/0.57    inference(avatar_component_clause,[],[f172])).
% 1.51/0.57  fof(f286,plain,(
% 1.51/0.57    ~r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl2_26),
% 1.51/0.57    inference(superposition,[],[f274,f86])).
% 1.51/0.57  fof(f86,plain,(
% 1.51/0.57    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.51/0.57    inference(definition_unfolding,[],[f59,f53])).
% 1.51/0.57  fof(f59,plain,(
% 1.51/0.57    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f25])).
% 1.51/0.57  fof(f274,plain,(
% 1.51/0.57    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | spl2_26),
% 1.51/0.57    inference(avatar_component_clause,[],[f272])).
% 1.51/0.57  fof(f275,plain,(
% 1.51/0.57    ~spl2_1 | ~spl2_4 | ~spl2_20 | ~spl2_24 | ~spl2_26 | spl2_21),
% 1.51/0.57    inference(avatar_split_clause,[],[f239,f235,f272,f251,f230,f111,f96])).
% 1.51/0.57  fof(f235,plain,(
% 1.51/0.57    spl2_21 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 1.51/0.57  fof(f239,plain,(
% 1.51/0.57    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | spl2_21),
% 1.51/0.57    inference(superposition,[],[f237,f82])).
% 1.51/0.57  fof(f237,plain,(
% 1.51/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | spl2_21),
% 1.51/0.57    inference(avatar_component_clause,[],[f235])).
% 1.51/0.57  fof(f254,plain,(
% 1.51/0.57    ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | spl2_24 | ~spl2_19),
% 1.51/0.57    inference(avatar_split_clause,[],[f228,f220,f251,f111,f106,f101,f96])).
% 1.51/0.57  fof(f106,plain,(
% 1.51/0.57    spl2_3 <=> v3_funct_2(sK1,sK0,sK0)),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.51/0.57  fof(f228,plain,(
% 1.51/0.57    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl2_19),
% 1.51/0.57    inference(superposition,[],[f67,f222])).
% 1.51/0.57  fof(f67,plain,(
% 1.51/0.57    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f31])).
% 1.51/0.57  fof(f31,plain,(
% 1.51/0.57    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.51/0.57    inference(flattening,[],[f30])).
% 1.51/0.57  fof(f30,plain,(
% 1.51/0.57    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.51/0.57    inference(ennf_transformation,[],[f11])).
% 1.51/0.57  fof(f11,axiom,(
% 1.51/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 1.51/0.57  fof(f238,plain,(
% 1.51/0.57    ~spl2_21 | spl2_6 | ~spl2_19),
% 1.51/0.57    inference(avatar_split_clause,[],[f225,f220,f131,f235])).
% 1.51/0.57  fof(f131,plain,(
% 1.51/0.57    spl2_6 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.51/0.57  fof(f225,plain,(
% 1.51/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | (spl2_6 | ~spl2_19)),
% 1.51/0.57    inference(backward_demodulation,[],[f133,f222])).
% 1.51/0.57  fof(f133,plain,(
% 1.51/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) | spl2_6),
% 1.51/0.57    inference(avatar_component_clause,[],[f131])).
% 1.51/0.57  fof(f233,plain,(
% 1.51/0.57    spl2_20 | ~spl2_16 | ~spl2_19),
% 1.51/0.57    inference(avatar_split_clause,[],[f224,f220,f203,f230])).
% 1.51/0.57  fof(f203,plain,(
% 1.51/0.57    spl2_16 <=> v1_funct_1(k2_funct_2(sK0,sK1))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 1.51/0.57  fof(f224,plain,(
% 1.51/0.57    v1_funct_1(k2_funct_1(sK1)) | (~spl2_16 | ~spl2_19)),
% 1.51/0.57    inference(backward_demodulation,[],[f205,f222])).
% 1.51/0.57  fof(f205,plain,(
% 1.51/0.57    v1_funct_1(k2_funct_2(sK0,sK1)) | ~spl2_16),
% 1.51/0.57    inference(avatar_component_clause,[],[f203])).
% 1.51/0.57  fof(f223,plain,(
% 1.51/0.57    ~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_19 | ~spl2_4),
% 1.51/0.57    inference(avatar_split_clause,[],[f116,f111,f220,f106,f101,f96])).
% 1.51/0.57  fof(f116,plain,(
% 1.51/0.57    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl2_4),
% 1.51/0.57    inference(resolution,[],[f113,f63])).
% 1.51/0.57  fof(f63,plain,(
% 1.51/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f29])).
% 1.51/0.57  fof(f29,plain,(
% 1.51/0.57    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.51/0.57    inference(flattening,[],[f28])).
% 1.51/0.57  fof(f28,plain,(
% 1.51/0.57    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.51/0.57    inference(ennf_transformation,[],[f14])).
% 1.51/0.57  fof(f14,axiom,(
% 1.51/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 1.51/0.57  fof(f206,plain,(
% 1.51/0.57    ~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_16 | ~spl2_4),
% 1.51/0.57    inference(avatar_split_clause,[],[f115,f111,f203,f106,f101,f96])).
% 1.51/0.57  fof(f115,plain,(
% 1.51/0.57    v1_funct_1(k2_funct_2(sK0,sK1)) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl2_4),
% 1.51/0.57    inference(resolution,[],[f113,f64])).
% 1.51/0.57  fof(f64,plain,(
% 1.51/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | v1_funct_1(k2_funct_2(X0,X1)) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f31])).
% 1.51/0.57  fof(f175,plain,(
% 1.51/0.57    ~spl2_4 | spl2_14 | ~spl2_12),
% 1.51/0.57    inference(avatar_split_clause,[],[f169,f161,f172,f111])).
% 1.51/0.57  fof(f169,plain,(
% 1.51/0.57    sK0 = k1_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl2_12),
% 1.51/0.57    inference(superposition,[],[f163,f69])).
% 1.51/0.57  fof(f69,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.57    inference(cnf_transformation,[],[f33])).
% 1.51/0.57  fof(f33,plain,(
% 1.51/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.57    inference(ennf_transformation,[],[f6])).
% 1.51/0.57  fof(f6,axiom,(
% 1.51/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.51/0.57  fof(f163,plain,(
% 1.51/0.57    sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl2_12),
% 1.51/0.57    inference(avatar_component_clause,[],[f161])).
% 1.51/0.57  fof(f168,plain,(
% 1.51/0.57    spl2_12 | spl2_13 | ~spl2_2 | ~spl2_4),
% 1.51/0.57    inference(avatar_split_clause,[],[f119,f111,f101,f165,f161])).
% 1.51/0.57  fof(f119,plain,(
% 1.51/0.57    ~v1_funct_2(sK1,sK0,sK0) | k1_xboole_0 = sK0 | sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl2_4),
% 1.51/0.57    inference(resolution,[],[f113,f71])).
% 1.51/0.57  fof(f71,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.51/0.57    inference(cnf_transformation,[],[f46])).
% 1.51/0.57  fof(f159,plain,(
% 1.51/0.57    spl2_11 | ~spl2_1 | ~spl2_3 | ~spl2_4),
% 1.51/0.57    inference(avatar_split_clause,[],[f122,f111,f106,f96,f156])).
% 1.51/0.57  fof(f122,plain,(
% 1.51/0.57    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v2_funct_2(sK1,sK0) | ~spl2_4),
% 1.51/0.57    inference(resolution,[],[f113,f79])).
% 1.51/0.57  fof(f79,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_2(X2,X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f38])).
% 1.51/0.57  fof(f38,plain,(
% 1.51/0.57    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.57    inference(flattening,[],[f37])).
% 1.51/0.57  fof(f37,plain,(
% 1.51/0.57    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.57    inference(ennf_transformation,[],[f8])).
% 1.51/0.57  fof(f8,axiom,(
% 1.51/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 1.51/0.57  fof(f153,plain,(
% 1.51/0.57    spl2_10 | ~spl2_1 | ~spl2_3 | ~spl2_4),
% 1.51/0.57    inference(avatar_split_clause,[],[f121,f111,f106,f96,f150])).
% 1.51/0.57  fof(f121,plain,(
% 1.51/0.57    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v2_funct_1(sK1) | ~spl2_4),
% 1.51/0.57    inference(resolution,[],[f113,f78])).
% 1.51/0.57  fof(f78,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_1(X2)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f38])).
% 1.51/0.57  fof(f143,plain,(
% 1.51/0.57    spl2_8 | ~spl2_4),
% 1.51/0.57    inference(avatar_split_clause,[],[f118,f111,f140])).
% 1.51/0.57  fof(f118,plain,(
% 1.51/0.57    v5_relat_1(sK1,sK0) | ~spl2_4),
% 1.51/0.57    inference(resolution,[],[f113,f70])).
% 1.51/0.57  fof(f70,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f34])).
% 1.51/0.57  fof(f34,plain,(
% 1.51/0.57    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.57    inference(ennf_transformation,[],[f19])).
% 1.51/0.57  fof(f19,plain,(
% 1.51/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.51/0.57    inference(pure_predicate_removal,[],[f5])).
% 1.51/0.57  fof(f5,axiom,(
% 1.51/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.51/0.57  fof(f138,plain,(
% 1.51/0.57    ~spl2_6 | ~spl2_7),
% 1.51/0.57    inference(avatar_split_clause,[],[f52,f135,f131])).
% 1.51/0.57  fof(f52,plain,(
% 1.51/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 1.51/0.57    inference(cnf_transformation,[],[f44])).
% 1.51/0.57  fof(f44,plain,(
% 1.51/0.57    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 1.51/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f43])).
% 1.51/0.57  fof(f43,plain,(
% 1.51/0.57    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 1.51/0.57    introduced(choice_axiom,[])).
% 1.51/0.57  fof(f21,plain,(
% 1.51/0.57    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.51/0.57    inference(flattening,[],[f20])).
% 1.51/0.57  fof(f20,plain,(
% 1.51/0.57    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.51/0.57    inference(ennf_transformation,[],[f17])).
% 1.51/0.57  fof(f17,negated_conjecture,(
% 1.51/0.57    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 1.51/0.57    inference(negated_conjecture,[],[f16])).
% 1.51/0.57  fof(f16,conjecture,(
% 1.51/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).
% 1.51/0.57  fof(f129,plain,(
% 1.51/0.57    spl2_5 | ~spl2_4),
% 1.51/0.57    inference(avatar_split_clause,[],[f117,f111,f126])).
% 1.51/0.57  fof(f117,plain,(
% 1.51/0.57    v1_relat_1(sK1) | ~spl2_4),
% 1.51/0.57    inference(resolution,[],[f113,f68])).
% 1.51/0.57  fof(f68,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f32])).
% 1.51/0.57  fof(f32,plain,(
% 1.51/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.57    inference(ennf_transformation,[],[f4])).
% 1.51/0.57  fof(f4,axiom,(
% 1.51/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.51/0.57  fof(f114,plain,(
% 1.51/0.57    spl2_4),
% 1.51/0.57    inference(avatar_split_clause,[],[f51,f111])).
% 1.51/0.57  fof(f51,plain,(
% 1.51/0.57    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.51/0.57    inference(cnf_transformation,[],[f44])).
% 1.51/0.57  fof(f109,plain,(
% 1.51/0.57    spl2_3),
% 1.51/0.57    inference(avatar_split_clause,[],[f50,f106])).
% 1.51/0.57  fof(f50,plain,(
% 1.51/0.57    v3_funct_2(sK1,sK0,sK0)),
% 1.51/0.57    inference(cnf_transformation,[],[f44])).
% 1.51/0.57  fof(f104,plain,(
% 1.51/0.57    spl2_2),
% 1.51/0.57    inference(avatar_split_clause,[],[f49,f101])).
% 1.51/0.57  fof(f49,plain,(
% 1.51/0.57    v1_funct_2(sK1,sK0,sK0)),
% 1.51/0.57    inference(cnf_transformation,[],[f44])).
% 1.51/0.57  fof(f99,plain,(
% 1.51/0.57    spl2_1),
% 1.51/0.57    inference(avatar_split_clause,[],[f48,f96])).
% 1.51/0.57  fof(f48,plain,(
% 1.51/0.57    v1_funct_1(sK1)),
% 1.51/0.57    inference(cnf_transformation,[],[f44])).
% 1.51/0.57  % SZS output end Proof for theBenchmark
% 1.51/0.57  % (11154)------------------------------
% 1.51/0.57  % (11154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.57  % (11154)Termination reason: Refutation
% 1.51/0.57  
% 1.51/0.57  % (11154)Memory used [KB]: 11129
% 1.51/0.57  % (11154)Time elapsed: 0.168 s
% 1.51/0.57  % (11154)------------------------------
% 1.51/0.57  % (11154)------------------------------
% 1.51/0.58  % (11143)Success in time 0.211 s
%------------------------------------------------------------------------------
