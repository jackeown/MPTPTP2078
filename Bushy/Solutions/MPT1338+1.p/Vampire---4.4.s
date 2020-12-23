%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_2__t62_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:42 EDT 2019

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 326 expanded)
%              Number of leaves         :   35 ( 128 expanded)
%              Depth                    :   12
%              Number of atoms          :  473 (1273 expanded)
%              Number of equality atoms :  121 ( 329 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f506,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f119,f123,f127,f131,f135,f145,f149,f153,f157,f192,f222,f228,f296,f300,f304,f308,f312,f366,f451,f459,f460,f504,f505])).

fof(f505,plain,
    ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2)
    | u1_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(theory_axiom,[])).

fof(f504,plain,
    ( spl5_5
    | ~ spl5_6
    | ~ spl5_70 ),
    inference(avatar_contradiction_clause,[],[f503])).

fof(f503,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_70 ),
    inference(subsumption_resolution,[],[f502,f126])).

fof(f126,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl5_5
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f502,plain,
    ( v2_struct_0(sK1)
    | ~ spl5_6
    | ~ spl5_70 ),
    inference(subsumption_resolution,[],[f501,f130])).

fof(f130,plain,
    ( l1_struct_0(sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl5_6
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f501,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_70 ),
    inference(subsumption_resolution,[],[f500,f105])).

fof(f105,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t62_tops_2.p',fc1_xboole_0)).

fof(f500,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_70 ),
    inference(superposition,[],[f100,f365])).

fof(f365,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | ~ spl5_70 ),
    inference(avatar_component_clause,[],[f364])).

fof(f364,plain,
    ( spl5_70
  <=> u1_struct_0(sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).

fof(f100,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t62_tops_2.p',fc2_struct_0)).

fof(f460,plain,
    ( u1_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k1_relat_1(sK2)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) != k1_relat_1(sK2)
    | u1_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) ),
    introduced(theory_axiom,[])).

fof(f459,plain,
    ( spl5_98
    | ~ spl5_56
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f337,f310,f306,f457])).

fof(f457,plain,
    ( spl5_98
  <=> k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).

fof(f306,plain,
    ( spl5_56
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f310,plain,
    ( spl5_58
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f337,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2)
    | ~ spl5_56
    | ~ spl5_58 ),
    inference(forward_demodulation,[],[f326,f307])).

fof(f307,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl5_56 ),
    inference(avatar_component_clause,[],[f306])).

fof(f326,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl5_58 ),
    inference(resolution,[],[f311,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t62_tops_2.p',redefinition_k2_relset_1)).

fof(f311,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl5_58 ),
    inference(avatar_component_clause,[],[f310])).

fof(f451,plain,
    ( spl5_96
    | ~ spl5_52
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f330,f310,f298,f449])).

fof(f449,plain,
    ( spl5_96
  <=> u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).

fof(f298,plain,
    ( spl5_52
  <=> u1_struct_0(sK1) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f330,plain,
    ( u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl5_52
    | ~ spl5_58 ),
    inference(forward_demodulation,[],[f320,f299])).

fof(f299,plain,
    ( u1_struct_0(sK1) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f298])).

fof(f320,plain,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl5_58 ),
    inference(resolution,[],[f311,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t62_tops_2.p',redefinition_k1_relset_1)).

fof(f366,plain,
    ( spl5_68
    | spl5_70
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f170,f155,f147,f364,f361])).

fof(f361,plain,
    ( spl5_68
  <=> u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f147,plain,
    ( spl5_12
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f155,plain,
    ( spl5_16
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f170,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f159,f148])).

fof(f148,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f147])).

fof(f159,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl5_16 ),
    inference(resolution,[],[f156,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/tops_2__t62_tops_2.p',d1_funct_2)).

fof(f156,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f155])).

fof(f312,plain,
    ( spl5_58
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f184,f155,f147,f143,f121,f117,f310])).

fof(f117,plain,
    ( spl5_0
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f121,plain,
    ( spl5_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f143,plain,
    ( spl5_10
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f184,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f183,f175])).

fof(f175,plain,
    ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f174,f144])).

fof(f144,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f143])).

fof(f174,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f173,f73])).

fof(f73,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
                    & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t62_tops_2.p',t62_tops_2)).

fof(f173,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f172,f122])).

fof(f122,plain,
    ( v2_funct_1(sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f121])).

fof(f172,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f171,f118])).

fof(f118,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f117])).

fof(f171,plain,
    ( ~ v1_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f162,f148])).

fof(f162,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ spl5_16 ),
    inference(resolution,[],[f156,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t62_tops_2.p',d4_tops_2)).

fof(f183,plain,
    ( m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f182,f118])).

fof(f182,plain,
    ( ~ v1_funct_1(sK2)
    | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f165,f148])).

fof(f165,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl5_16 ),
    inference(resolution,[],[f156,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t62_tops_2.p',dt_k2_tops_2)).

fof(f308,plain,
    ( spl5_56
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f210,f190,f121,f117,f306])).

fof(f190,plain,
    ( spl5_18
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f210,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f209,f122])).

fof(f209,plain,
    ( ~ v2_funct_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl5_0
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f204,f118])).

fof(f204,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl5_18 ),
    inference(resolution,[],[f191,f91])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t62_tops_2.p',t55_funct_1)).

fof(f191,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f190])).

fof(f304,plain,
    ( spl5_54
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f175,f155,f147,f143,f121,f117,f302])).

fof(f302,plain,
    ( spl5_54
  <=> k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f300,plain,
    ( spl5_52
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_16
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f208,f190,f155,f143,f121,f117,f298])).

fof(f208,plain,
    ( u1_struct_0(sK1) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_16
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f207,f188])).

fof(f188,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl5_10
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f187,f144])).

fof(f187,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f167,f73])).

fof(f167,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl5_16 ),
    inference(resolution,[],[f156,f96])).

fof(f207,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f206,f122])).

fof(f206,plain,
    ( ~ v2_funct_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | ~ spl5_0
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f203,f118])).

fof(f203,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | ~ spl5_18 ),
    inference(resolution,[],[f191,f90])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f296,plain,
    ( spl5_50
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f161,f155,f294])).

fof(f294,plain,
    ( spl5_50
  <=> k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f161,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2)
    | ~ spl5_16 ),
    inference(resolution,[],[f156,f85])).

fof(f228,plain,
    ( ~ spl5_31
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_16
    | spl5_27 ),
    inference(avatar_split_clause,[],[f224,f217,f155,f151,f147,f143,f121,f117,f226])).

fof(f226,plain,
    ( spl5_31
  <=> u1_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f151,plain,
    ( spl5_14
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f217,plain,
    ( spl5_27
  <=> k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f224,plain,
    ( u1_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_16
    | ~ spl5_27 ),
    inference(forward_demodulation,[],[f223,f175])).

fof(f223,plain,
    ( u1_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl5_14
    | ~ spl5_27 ),
    inference(forward_demodulation,[],[f218,f152])).

fof(f152,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f151])).

fof(f218,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f217])).

fof(f222,plain,
    ( ~ spl5_27
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f69,f220,f217])).

fof(f220,plain,
    ( spl5_29
  <=> k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f69,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f192,plain,
    ( spl5_18
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f168,f155,f190])).

fof(f168,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_16 ),
    inference(resolution,[],[f156,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t62_tops_2.p',cc1_relset_1)).

fof(f157,plain,(
    spl5_16 ),
    inference(avatar_split_clause,[],[f72,f155])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f39])).

fof(f153,plain,
    ( spl5_14
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f139,f133,f151])).

fof(f133,plain,
    ( spl5_8
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f139,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(resolution,[],[f134,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t62_tops_2.p',d3_struct_0)).

fof(f134,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f133])).

fof(f149,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f71,f147])).

fof(f71,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f145,plain,
    ( spl5_10
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f136,f129,f143])).

fof(f136,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl5_6 ),
    inference(resolution,[],[f130,f94])).

fof(f135,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f77,f133])).

fof(f77,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f131,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f76,f129])).

fof(f76,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f127,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f75,f125])).

fof(f75,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f123,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f74,f121])).

fof(f74,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f119,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f70,f117])).

fof(f70,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
