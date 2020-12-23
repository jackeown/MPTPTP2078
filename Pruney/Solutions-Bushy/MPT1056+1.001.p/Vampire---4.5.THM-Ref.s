%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1056+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:11 EST 2020

% Result     : Theorem 2.29s
% Output     : Refutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :  199 ( 503 expanded)
%              Number of leaves         :   43 ( 204 expanded)
%              Depth                    :   22
%              Number of atoms          : 1094 (3769 expanded)
%              Number of equality atoms :  101 ( 509 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1043,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f95,f100,f105,f110,f115,f120,f125,f130,f135,f140,f145,f150,f164,f216,f243,f359,f919,f956,f962,f972,f1010,f1032])).

fof(f1032,plain,
    ( ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_15
    | spl6_33
    | spl6_57
    | ~ spl6_59
    | ~ spl6_61 ),
    inference(avatar_contradiction_clause,[],[f1028])).

fof(f1028,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_15
    | spl6_33
    | spl6_57
    | ~ spl6_59
    | ~ spl6_61 ),
    inference(unit_resulting_resolution,[],[f163,f345,f124,f99,f119,f94,f910,f903,f1017])).

fof(f1017,plain,
    ( ! [X2,X1] :
        ( r2_relset_1(sK3,X1,k7_relat_1(sK2,sK3),sK4)
        | ~ v1_funct_2(k7_relat_1(sK2,sK3),sK3,X1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
        | ~ v1_funct_2(sK4,sK3,X1)
        | k1_xboole_0 = X1
        | ~ r1_tarski(sK3,X2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(sK2,X2,X1) )
    | ~ spl6_9
    | ~ spl6_61 ),
    inference(subsumption_resolution,[],[f1014,f129])).

fof(f129,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl6_9
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f1014,plain,
    ( ! [X2,X1] :
        ( r2_relset_1(sK3,X1,k7_relat_1(sK2,sK3),sK4)
        | ~ v1_funct_2(k7_relat_1(sK2,sK3),sK3,X1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
        | ~ v1_funct_2(sK4,sK3,X1)
        | k1_xboole_0 = X1
        | ~ r1_tarski(sK3,X2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(sK2,X2,X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl6_61 ),
    inference(resolution,[],[f918,f290])).

fof(f290,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relat_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f289])).

fof(f289,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relat_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(superposition,[],[f67,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

fof(f918,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,X2)))
        | r2_relset_1(sK3,X2,k7_relat_1(sK2,sK3),sK4)
        | ~ v1_funct_2(k7_relat_1(sK2,sK3),sK3,X2)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,X2)))
        | ~ v1_funct_2(sK4,sK3,X2) )
    | ~ spl6_61 ),
    inference(avatar_component_clause,[],[f917])).

fof(f917,plain,
    ( spl6_61
  <=> ! [X2] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,X2)))
        | r2_relset_1(sK3,X2,k7_relat_1(sK2,sK3),sK4)
        | ~ v1_funct_2(k7_relat_1(sK2,sK3),sK3,X2)
        | ~ m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,X2)))
        | ~ v1_funct_2(sK4,sK3,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f903,plain,
    ( ~ r2_relset_1(sK3,sK1,k7_relat_1(sK2,sK3),sK4)
    | spl6_57 ),
    inference(avatar_component_clause,[],[f902])).

fof(f902,plain,
    ( spl6_57
  <=> r2_relset_1(sK3,sK1,k7_relat_1(sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f910,plain,
    ( v1_funct_2(k7_relat_1(sK2,sK3),sK3,sK1)
    | ~ spl6_59 ),
    inference(avatar_component_clause,[],[f909])).

fof(f909,plain,
    ( spl6_59
  <=> v1_funct_2(k7_relat_1(sK2,sK3),sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f94,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl6_2
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f119,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl6_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f99,plain,
    ( v1_funct_2(sK4,sK3,sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl6_3
  <=> v1_funct_2(sK4,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f124,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl6_8
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f345,plain,
    ( k1_xboole_0 != sK1
    | spl6_33 ),
    inference(avatar_component_clause,[],[f344])).

fof(f344,plain,
    ( spl6_33
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f163,plain,
    ( r1_tarski(sK3,sK0)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl6_15
  <=> r1_tarski(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f1010,plain,
    ( ~ spl6_7
    | ~ spl6_8
    | ~ spl6_15
    | ~ spl6_58 ),
    inference(avatar_contradiction_clause,[],[f1009])).

fof(f1009,plain,
    ( $false
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_15
    | ~ spl6_58 ),
    inference(subsumption_resolution,[],[f1008,f163])).

fof(f1008,plain,
    ( ~ r1_tarski(sK3,sK0)
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_58 ),
    inference(subsumption_resolution,[],[f1006,f124])).

fof(f1006,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ r1_tarski(sK3,sK0)
    | ~ spl6_7
    | ~ spl6_58 ),
    inference(resolution,[],[f907,f119])).

fof(f907,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
        | ~ v1_funct_2(sK2,X3,sK1)
        | ~ r1_tarski(sK3,X3) )
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f906])).

fof(f906,plain,
    ( spl6_58
  <=> ! [X3] :
        ( ~ r1_tarski(sK3,X3)
        | ~ v1_funct_2(sK2,X3,sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f972,plain,
    ( ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_15
    | spl6_33
    | spl6_57
    | ~ spl6_59
    | spl6_60 ),
    inference(avatar_contradiction_clause,[],[f971])).

fof(f971,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_15
    | spl6_33
    | spl6_57
    | ~ spl6_59
    | spl6_60 ),
    inference(unit_resulting_resolution,[],[f129,f163,f124,f119,f910,f915,f903,f805])).

fof(f805,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(sK3,k7_relat_1(X0,sK3),sK4),sK3)
        | ~ v1_funct_2(k7_relat_1(X0,sK3),sK3,sK1)
        | ~ r1_tarski(sK3,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
        | ~ v1_funct_2(X0,X1,sK1)
        | ~ v1_funct_1(X0)
        | r2_relset_1(sK3,sK1,k7_relat_1(X0,sK3),sK4) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_6
    | spl6_33 ),
    inference(subsumption_resolution,[],[f804,f114])).

fof(f114,plain,
    ( ~ v1_xboole_0(sK3)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl6_6
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f804,plain,
    ( ! [X0,X1] :
        ( r2_relset_1(sK3,sK1,k7_relat_1(X0,sK3),sK4)
        | ~ v1_funct_2(k7_relat_1(X0,sK3),sK3,sK1)
        | ~ r1_tarski(sK3,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
        | ~ v1_funct_2(X0,X1,sK1)
        | ~ v1_funct_1(X0)
        | v1_xboole_0(sK3)
        | r2_hidden(sK5(sK3,k7_relat_1(X0,sK3),sK4),sK3) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_33 ),
    inference(resolution,[],[f700,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f700,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK5(sK3,k7_relat_1(X1,sK3),sK4),sK3)
        | r2_relset_1(sK3,sK1,k7_relat_1(X1,sK3),sK4)
        | ~ v1_funct_2(k7_relat_1(X1,sK3),sK3,sK1)
        | ~ r1_tarski(sK3,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ v1_funct_1(X1) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_33 ),
    inference(duplicate_literal_removal,[],[f699])).

fof(f699,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK5(sK3,k7_relat_1(X1,sK3),sK4),sK3)
        | r2_relset_1(sK3,sK1,k7_relat_1(X1,sK3),sK4)
        | ~ v1_funct_2(k7_relat_1(X1,sK3),sK3,sK1)
        | ~ r1_tarski(sK3,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | ~ v1_funct_1(X1) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_33 ),
    inference(superposition,[],[f392,f62])).

fof(f392,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(sK5(sK3,k2_partfun1(X2,sK1,X3,sK3),sK4),sK3)
        | r2_relset_1(sK3,sK1,k2_partfun1(X2,sK1,X3,sK3),sK4)
        | ~ v1_funct_2(k2_partfun1(X2,sK1,X3,sK3),sK3,sK1)
        | ~ r1_tarski(sK3,X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
        | ~ v1_funct_2(X3,X2,sK1)
        | ~ v1_funct_1(X3) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_33 ),
    inference(subsumption_resolution,[],[f391,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f391,plain,
    ( ! [X2,X3] :
        ( r2_relset_1(sK3,sK1,k2_partfun1(X2,sK1,X3,sK3),sK4)
        | m1_subset_1(sK5(sK3,k2_partfun1(X2,sK1,X3,sK3),sK4),sK3)
        | ~ v1_funct_2(k2_partfun1(X2,sK1,X3,sK3),sK3,sK1)
        | ~ v1_funct_1(k2_partfun1(X2,sK1,X3,sK3))
        | ~ r1_tarski(sK3,X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
        | ~ v1_funct_2(X3,X2,sK1)
        | ~ v1_funct_1(X3) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_33 ),
    inference(subsumption_resolution,[],[f387,f345])).

fof(f387,plain,
    ( ! [X2,X3] :
        ( r2_relset_1(sK3,sK1,k2_partfun1(X2,sK1,X3,sK3),sK4)
        | m1_subset_1(sK5(sK3,k2_partfun1(X2,sK1,X3,sK3),sK4),sK3)
        | ~ v1_funct_2(k2_partfun1(X2,sK1,X3,sK3),sK3,sK1)
        | ~ v1_funct_1(k2_partfun1(X2,sK1,X3,sK3))
        | k1_xboole_0 = sK1
        | ~ r1_tarski(sK3,X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
        | ~ v1_funct_2(X3,X2,sK1)
        | ~ v1_funct_1(X3) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(resolution,[],[f305,f67])).

fof(f305,plain,
    ( ! [X15] :
        ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
        | r2_relset_1(sK3,sK1,X15,sK4)
        | m1_subset_1(sK5(sK3,X15,sK4),sK3)
        | ~ v1_funct_2(X15,sK3,sK1)
        | ~ v1_funct_1(X15) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f304,f104])).

fof(f104,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl6_4
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f304,plain,
    ( ! [X15] :
        ( m1_subset_1(sK5(sK3,X15,sK4),sK3)
        | r2_relset_1(sK3,sK1,X15,sK4)
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
        | ~ v1_funct_2(X15,sK3,sK1)
        | ~ v1_funct_1(X15) )
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f296,f99])).

fof(f296,plain,
    ( ! [X15] :
        ( m1_subset_1(sK5(sK3,X15,sK4),sK3)
        | r2_relset_1(sK3,sK1,X15,sK4)
        | ~ v1_funct_2(sK4,sK3,sK1)
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
        | ~ v1_funct_2(X15,sK3,sK1)
        | ~ v1_funct_1(X15) )
    | ~ spl6_2 ),
    inference(resolution,[],[f72,f94])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(sK5(X0,X2,X3),X0)
      | r2_relset_1(X0,X1,X2,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ( k1_funct_1(X2,sK5(X0,X2,X3)) != k1_funct_1(X3,sK5(X0,X2,X3))
            & m1_subset_1(sK5(X0,X2,X3),X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f46])).

fof(f46,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & m1_subset_1(X4,X0) )
     => ( k1_funct_1(X2,sK5(X0,X2,X3)) != k1_funct_1(X3,sK5(X0,X2,X3))
        & m1_subset_1(sK5(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).

fof(f915,plain,
    ( ~ r2_hidden(sK5(sK3,k7_relat_1(sK2,sK3),sK4),sK3)
    | spl6_60 ),
    inference(avatar_component_clause,[],[f913])).

fof(f913,plain,
    ( spl6_60
  <=> r2_hidden(sK5(sK3,k7_relat_1(sK2,sK3),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f962,plain,
    ( ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_15
    | spl6_28
    | spl6_33
    | ~ spl6_57 ),
    inference(avatar_contradiction_clause,[],[f959])).

fof(f959,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_15
    | spl6_28
    | spl6_33
    | ~ spl6_57 ),
    inference(unit_resulting_resolution,[],[f129,f163,f124,f242,f119,f904,f522])).

fof(f522,plain,
    ( ! [X43,X44] :
        ( ~ r2_relset_1(sK3,sK1,k7_relat_1(X44,sK3),sK4)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X43,sK1)))
        | ~ v1_funct_2(X44,X43,sK1)
        | ~ v1_funct_1(X44)
        | sK4 = k7_relat_1(X44,sK3)
        | ~ r1_tarski(sK3,X43) )
    | ~ spl6_2
    | spl6_33 ),
    inference(subsumption_resolution,[],[f511,f345])).

fof(f511,plain,
    ( ! [X43,X44] :
        ( k1_xboole_0 = sK1
        | ~ r1_tarski(sK3,X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X43,sK1)))
        | ~ v1_funct_2(X44,X43,sK1)
        | ~ v1_funct_1(X44)
        | sK4 = k7_relat_1(X44,sK3)
        | ~ r2_relset_1(sK3,sK1,k7_relat_1(X44,sK3),sK4) )
    | ~ spl6_2 ),
    inference(resolution,[],[f290,f255])).

fof(f255,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
        | sK4 = X6
        | ~ r2_relset_1(sK3,sK1,X6,sK4) )
    | ~ spl6_2 ),
    inference(resolution,[],[f69,f94])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f904,plain,
    ( r2_relset_1(sK3,sK1,k7_relat_1(sK2,sK3),sK4)
    | ~ spl6_57 ),
    inference(avatar_component_clause,[],[f902])).

fof(f242,plain,
    ( sK4 != k7_relat_1(sK2,sK3)
    | spl6_28 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl6_28
  <=> sK4 = k7_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f956,plain,
    ( ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_15
    | spl6_33
    | spl6_59 ),
    inference(avatar_contradiction_clause,[],[f955])).

fof(f955,plain,
    ( $false
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_15
    | spl6_33
    | spl6_59 ),
    inference(subsumption_resolution,[],[f952,f163])).

fof(f952,plain,
    ( ~ r1_tarski(sK3,sK0)
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_33
    | spl6_59 ),
    inference(resolution,[],[f911,f491])).

fof(f491,plain,
    ( ! [X23] :
        ( v1_funct_2(k7_relat_1(sK2,X23),X23,sK1)
        | ~ r1_tarski(X23,sK0) )
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_33 ),
    inference(subsumption_resolution,[],[f490,f129])).

fof(f490,plain,
    ( ! [X23] :
        ( ~ r1_tarski(X23,sK0)
        | v1_funct_2(k7_relat_1(sK2,X23),X23,sK1)
        | ~ v1_funct_1(sK2) )
    | ~ spl6_7
    | ~ spl6_8
    | spl6_33 ),
    inference(subsumption_resolution,[],[f489,f124])).

fof(f489,plain,
    ( ! [X23] :
        ( ~ r1_tarski(X23,sK0)
        | v1_funct_2(k7_relat_1(sK2,X23),X23,sK1)
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
    | ~ spl6_7
    | spl6_33 ),
    inference(subsumption_resolution,[],[f480,f345])).

fof(f480,plain,
    ( ! [X23] :
        ( k1_xboole_0 = sK1
        | ~ r1_tarski(X23,sK0)
        | v1_funct_2(k7_relat_1(sK2,X23),X23,sK1)
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
    | ~ spl6_7 ),
    inference(resolution,[],[f269,f119])).

fof(f269,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X3,X0)
      | v1_funct_2(k7_relat_1(X2,X3),X3,X1)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f268])).

fof(f268,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k7_relat_1(X2,X3),X3,X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(superposition,[],[f65,f62])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f911,plain,
    ( ~ v1_funct_2(k7_relat_1(sK2,sK3),sK3,sK1)
    | spl6_59 ),
    inference(avatar_component_clause,[],[f909])).

fof(f919,plain,
    ( spl6_57
    | spl6_58
    | ~ spl6_59
    | ~ spl6_60
    | spl6_61
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_11
    | ~ spl6_25
    | spl6_33 ),
    inference(avatar_split_clause,[],[f900,f344,f213,f137,f127,f122,f117,f112,f107,f102,f97,f92,f917,f913,f909,f906,f902])).

fof(f107,plain,
    ( spl6_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f137,plain,
    ( spl6_11
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f213,plain,
    ( spl6_25
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f900,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,X2)))
        | ~ v1_funct_2(sK4,sK3,X2)
        | ~ m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,X2)))
        | ~ v1_funct_2(k7_relat_1(sK2,sK3),sK3,X2)
        | ~ r2_hidden(sK5(sK3,k7_relat_1(sK2,sK3),sK4),sK3)
        | r2_relset_1(sK3,X2,k7_relat_1(sK2,sK3),sK4)
        | ~ v1_funct_2(k7_relat_1(sK2,sK3),sK3,sK1)
        | ~ r1_tarski(sK3,X3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
        | ~ v1_funct_2(sK2,X3,sK1)
        | r2_relset_1(sK3,sK1,k7_relat_1(sK2,sK3),sK4) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_11
    | ~ spl6_25
    | spl6_33 ),
    inference(subsumption_resolution,[],[f890,f129])).

fof(f890,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,X2)))
        | ~ v1_funct_2(sK4,sK3,X2)
        | ~ m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,X2)))
        | ~ v1_funct_2(k7_relat_1(sK2,sK3),sK3,X2)
        | ~ r2_hidden(sK5(sK3,k7_relat_1(sK2,sK3),sK4),sK3)
        | r2_relset_1(sK3,X2,k7_relat_1(sK2,sK3),sK4)
        | ~ v1_funct_2(k7_relat_1(sK2,sK3),sK3,sK1)
        | ~ r1_tarski(sK3,X3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
        | ~ v1_funct_2(sK2,X3,sK1)
        | ~ v1_funct_1(sK2)
        | r2_relset_1(sK3,sK1,k7_relat_1(sK2,sK3),sK4) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_11
    | ~ spl6_25
    | spl6_33 ),
    inference(resolution,[],[f767,f805])).

fof(f767,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK5(X0,k7_relat_1(sK2,X2),sK4),sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK4,X0,X1)
        | ~ m1_subset_1(k7_relat_1(sK2,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(k7_relat_1(sK2,X2),X0,X1)
        | ~ r2_hidden(sK5(X0,k7_relat_1(sK2,X2),sK4),X2)
        | r2_relset_1(X0,X1,k7_relat_1(sK2,X2),sK4) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_11
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f766,f215])).

fof(f215,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f213])).

fof(f766,plain,
    ( ! [X2,X0,X1] :
        ( r2_relset_1(X0,X1,k7_relat_1(sK2,X2),sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK4,X0,X1)
        | ~ m1_subset_1(k7_relat_1(sK2,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(k7_relat_1(sK2,X2),X0,X1)
        | ~ r2_hidden(sK5(X0,k7_relat_1(sK2,X2),sK4),X2)
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(sK5(X0,k7_relat_1(sK2,X2),sK4),sK3) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_11 ),
    inference(subsumption_resolution,[],[f765,f129])).

fof(f765,plain,
    ( ! [X2,X0,X1] :
        ( r2_relset_1(X0,X1,k7_relat_1(sK2,X2),sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK4,X0,X1)
        | ~ m1_subset_1(k7_relat_1(sK2,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(k7_relat_1(sK2,X2),X0,X1)
        | ~ r2_hidden(sK5(X0,k7_relat_1(sK2,X2),sK4),X2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(sK5(X0,k7_relat_1(sK2,X2),sK4),sK3) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_11 ),
    inference(subsumption_resolution,[],[f759,f315])).

fof(f315,plain,
    ( ! [X0] : v1_funct_1(k7_relat_1(sK2,X0))
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f314,f129])).

fof(f314,plain,
    ( ! [X0] :
        ( v1_funct_1(k7_relat_1(sK2,X0))
        | ~ v1_funct_1(sK2) )
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f313,f119])).

fof(f313,plain,
    ( ! [X0] :
        ( v1_funct_1(k7_relat_1(sK2,X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(sK2) )
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(superposition,[],[f235,f62])).

fof(f235,plain,
    ( ! [X1] : v1_funct_1(k2_partfun1(sK0,sK1,sK2,X1))
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f233,f129])).

fof(f233,plain,
    ( ! [X1] :
        ( v1_funct_1(k2_partfun1(sK0,sK1,sK2,X1))
        | ~ v1_funct_1(sK2) )
    | ~ spl6_7 ),
    inference(resolution,[],[f60,f119])).

fof(f759,plain,
    ( ! [X2,X0,X1] :
        ( r2_relset_1(X0,X1,k7_relat_1(sK2,X2),sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK4,X0,X1)
        | ~ m1_subset_1(k7_relat_1(sK2,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(k7_relat_1(sK2,X2),X0,X1)
        | ~ v1_funct_1(k7_relat_1(sK2,X2))
        | ~ r2_hidden(sK5(X0,k7_relat_1(sK2,X2),sK4),X2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(sK5(X0,k7_relat_1(sK2,X2),sK4),sK3) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_11 ),
    inference(equality_resolution,[],[f662])).

fof(f662,plain,
    ( ! [X6,X8,X7,X9] :
        ( k1_funct_1(sK2,sK5(X6,k7_relat_1(X7,X8),sK4)) != k1_funct_1(X7,sK5(X6,k7_relat_1(X7,X8),sK4))
        | r2_relset_1(X6,X9,k7_relat_1(X7,X8),sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X6,X9)))
        | ~ v1_funct_2(sK4,X6,X9)
        | ~ m1_subset_1(k7_relat_1(X7,X8),k1_zfmisc_1(k2_zfmisc_1(X6,X9)))
        | ~ v1_funct_2(k7_relat_1(X7,X8),X6,X9)
        | ~ v1_funct_1(k7_relat_1(X7,X8))
        | ~ r2_hidden(sK5(X6,k7_relat_1(X7,X8),sK4),X8)
        | ~ v1_funct_1(X7)
        | ~ v1_relat_1(X7)
        | ~ r2_hidden(sK5(X6,k7_relat_1(X7,X8),sK4),sK3) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_11 ),
    inference(subsumption_resolution,[],[f656,f104])).

fof(f656,plain,
    ( ! [X6,X8,X7,X9] :
        ( k1_funct_1(sK2,sK5(X6,k7_relat_1(X7,X8),sK4)) != k1_funct_1(X7,sK5(X6,k7_relat_1(X7,X8),sK4))
        | r2_relset_1(X6,X9,k7_relat_1(X7,X8),sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X6,X9)))
        | ~ v1_funct_2(sK4,X6,X9)
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(k7_relat_1(X7,X8),k1_zfmisc_1(k2_zfmisc_1(X6,X9)))
        | ~ v1_funct_2(k7_relat_1(X7,X8),X6,X9)
        | ~ v1_funct_1(k7_relat_1(X7,X8))
        | ~ r2_hidden(sK5(X6,k7_relat_1(X7,X8),sK4),X8)
        | ~ v1_funct_1(X7)
        | ~ v1_relat_1(X7)
        | ~ r2_hidden(sK5(X6,k7_relat_1(X7,X8),sK4),sK3) )
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_11 ),
    inference(superposition,[],[f306,f334])).

fof(f334,plain,
    ( ! [X0] :
        ( k1_funct_1(sK4,X0) = k1_funct_1(sK2,X0)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_11 ),
    inference(subsumption_resolution,[],[f277,f217])).

fof(f217,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | m1_subset_1(X0,sK0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f76,f109])).

fof(f109,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f277,plain,
    ( ! [X0] :
        ( k1_funct_1(sK4,X0) = k1_funct_1(sK2,X0)
        | ~ m1_subset_1(X0,sK0)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_11 ),
    inference(subsumption_resolution,[],[f276,f139])).

fof(f139,plain,
    ( ~ v1_xboole_0(sK0)
    | spl6_11 ),
    inference(avatar_component_clause,[],[f137])).

fof(f276,plain,
    ( ! [X0] :
        ( k1_funct_1(sK4,X0) = k1_funct_1(sK2,X0)
        | ~ m1_subset_1(X0,sK0)
        | v1_xboole_0(sK0)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f275,f129])).

fof(f275,plain,
    ( ! [X0] :
        ( k1_funct_1(sK4,X0) = k1_funct_1(sK2,X0)
        | ~ m1_subset_1(X0,sK0)
        | ~ v1_funct_1(sK2)
        | v1_xboole_0(sK0)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f274,f124])).

fof(f274,plain,
    ( ! [X0] :
        ( k1_funct_1(sK4,X0) = k1_funct_1(sK2,X0)
        | ~ m1_subset_1(X0,sK0)
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2)
        | v1_xboole_0(sK0)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f273,f119])).

fof(f273,plain,(
    ! [X0] :
      ( k1_funct_1(sK4,X0) = k1_funct_1(sK2,X0)
      | ~ m1_subset_1(X0,sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2)
      | v1_xboole_0(sK0)
      | ~ r2_hidden(X0,sK3) ) ),
    inference(duplicate_literal_removal,[],[f270])).

fof(f270,plain,(
    ! [X0] :
      ( k1_funct_1(sK4,X0) = k1_funct_1(sK2,X0)
      | ~ m1_subset_1(X0,sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2)
      | v1_xboole_0(sK0)
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(superposition,[],[f71,f58])).

fof(f58,plain,(
    ! [X5] :
      ( k3_funct_2(sK0,sK1,sK2,X5) = k1_funct_1(sK4,X5)
      | ~ r2_hidden(X5,sK3)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( k2_partfun1(sK0,sK1,sK2,sK3) != sK4
    & ! [X5] :
        ( k3_funct_2(sK0,sK1,sK2,X5) = k1_funct_1(sK4,X5)
        | ~ r2_hidden(X5,sK3)
        | ~ m1_subset_1(X5,sK0) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    & v1_funct_2(sK4,sK3,sK1)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(sK0))
    & ~ v1_xboole_0(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f18,f43,f42,f41,f40,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( k2_partfun1(X0,X1,X2,X3) != X4
                        & ! [X5] :
                            ( k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5)
                            | ~ r2_hidden(X5,X3)
                            | ~ m1_subset_1(X5,X0) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                        & v1_funct_2(X4,X3,X1)
                        & v1_funct_1(X4) )
                    & m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k2_partfun1(sK0,X1,X2,X3) != X4
                      & ! [X5] :
                          ( k1_funct_1(X4,X5) = k3_funct_2(sK0,X1,X2,X5)
                          | ~ r2_hidden(X5,X3)
                          | ~ m1_subset_1(X5,sK0) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      & v1_funct_2(X4,X3,X1)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(sK0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
              & v1_funct_2(X2,sK0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( k2_partfun1(sK0,X1,X2,X3) != X4
                    & ! [X5] :
                        ( k1_funct_1(X4,X5) = k3_funct_2(sK0,X1,X2,X5)
                        | ~ r2_hidden(X5,X3)
                        | ~ m1_subset_1(X5,sK0) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                    & v1_funct_2(X4,X3,X1)
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(sK0))
                & ~ v1_xboole_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
            & v1_funct_2(X2,sK0,X1)
            & v1_funct_1(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( k2_partfun1(sK0,sK1,X2,X3) != X4
                  & ! [X5] :
                      ( k1_funct_1(X4,X5) = k3_funct_2(sK0,sK1,X2,X5)
                      | ~ r2_hidden(X5,X3)
                      | ~ m1_subset_1(X5,sK0) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
                  & v1_funct_2(X4,X3,sK1)
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(sK0))
              & ~ v1_xboole_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X2,sK0,sK1)
          & v1_funct_1(X2) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( k2_partfun1(sK0,sK1,X2,X3) != X4
                & ! [X5] :
                    ( k1_funct_1(X4,X5) = k3_funct_2(sK0,sK1,X2,X5)
                    | ~ r2_hidden(X5,X3)
                    | ~ m1_subset_1(X5,sK0) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
                & v1_funct_2(X4,X3,sK1)
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(sK0))
            & ~ v1_xboole_0(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X2,sK0,sK1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( k2_partfun1(sK0,sK1,sK2,X3) != X4
              & ! [X5] :
                  ( k1_funct_1(X4,X5) = k3_funct_2(sK0,sK1,sK2,X5)
                  | ~ r2_hidden(X5,X3)
                  | ~ m1_subset_1(X5,sK0) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
              & v1_funct_2(X4,X3,sK1)
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(sK0))
          & ~ v1_xboole_0(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( k2_partfun1(sK0,sK1,sK2,X3) != X4
            & ! [X5] :
                ( k1_funct_1(X4,X5) = k3_funct_2(sK0,sK1,sK2,X5)
                | ~ r2_hidden(X5,X3)
                | ~ m1_subset_1(X5,sK0) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
            & v1_funct_2(X4,X3,sK1)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(sK0))
        & ~ v1_xboole_0(X3) )
   => ( ? [X4] :
          ( k2_partfun1(sK0,sK1,sK2,sK3) != X4
          & ! [X5] :
              ( k1_funct_1(X4,X5) = k3_funct_2(sK0,sK1,sK2,X5)
              | ~ r2_hidden(X5,sK3)
              | ~ m1_subset_1(X5,sK0) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
          & v1_funct_2(X4,sK3,sK1)
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK0))
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X4] :
        ( k2_partfun1(sK0,sK1,sK2,sK3) != X4
        & ! [X5] :
            ( k1_funct_1(X4,X5) = k3_funct_2(sK0,sK1,sK2,X5)
            | ~ r2_hidden(X5,sK3)
            | ~ m1_subset_1(X5,sK0) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
        & v1_funct_2(X4,sK3,sK1)
        & v1_funct_1(X4) )
   => ( k2_partfun1(sK0,sK1,sK2,sK3) != sK4
      & ! [X5] :
          ( k3_funct_2(sK0,sK1,sK2,X5) = k1_funct_1(sK4,X5)
          | ~ r2_hidden(X5,sK3)
          | ~ m1_subset_1(X5,sK0) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      & v1_funct_2(sK4,sK3,sK1)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) != X4
                      & ! [X5] :
                          ( k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5)
                          | ~ r2_hidden(X5,X3)
                          | ~ m1_subset_1(X5,X0) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      & v1_funct_2(X4,X3,X1)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) != X4
                      & ! [X5] :
                          ( k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5)
                          | ~ r2_hidden(X5,X3)
                          | ~ m1_subset_1(X5,X0) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      & v1_funct_2(X4,X3,X1)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                      & ~ v1_xboole_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X4,X3,X1)
                          & v1_funct_1(X4) )
                       => ( ! [X5] :
                              ( m1_subset_1(X5,X0)
                             => ( r2_hidden(X5,X3)
                               => k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5) ) )
                         => k2_partfun1(X0,X1,X2,X3) = X4 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                        & v1_funct_2(X4,X3,X1)
                        & v1_funct_1(X4) )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,X0)
                           => ( r2_hidden(X5,X3)
                             => k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5) ) )
                       => k2_partfun1(X0,X1,X2,X3) = X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_funct_2)).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f306,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_funct_1(X0,sK5(X2,k7_relat_1(X0,X1),X3)) != k1_funct_1(X3,sK5(X2,k7_relat_1(X0,X1),X3))
      | r2_relset_1(X2,X4,k7_relat_1(X0,X1),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
      | ~ v1_funct_2(X3,X2,X4)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
      | ~ v1_funct_2(k7_relat_1(X0,X1),X2,X4)
      | ~ v1_funct_1(k7_relat_1(X0,X1))
      | ~ r2_hidden(sK5(X2,k7_relat_1(X0,X1),X3),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f73,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,sK5(X0,X2,X3)) != k1_funct_1(X3,sK5(X0,X2,X3))
      | r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f359,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != o_0_0_xboole_0
    | v1_xboole_0(sK1)
    | ~ v1_xboole_0(o_0_0_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f243,plain,
    ( ~ spl6_28
    | spl6_1
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f238,f127,f117,f87,f240])).

fof(f87,plain,
    ( spl6_1
  <=> k2_partfun1(sK0,sK1,sK2,sK3) = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f238,plain,
    ( sK4 != k7_relat_1(sK2,sK3)
    | spl6_1
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f237,f129])).

fof(f237,plain,
    ( sK4 != k7_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | spl6_1
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f236,f119])).

fof(f236,plain,
    ( sK4 != k7_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl6_1 ),
    inference(superposition,[],[f89,f62])).

fof(f89,plain,
    ( k2_partfun1(sK0,sK1,sK2,sK3) != sK4
    | spl6_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f216,plain,
    ( spl6_25
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f206,f117,f213])).

fof(f206,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_7 ),
    inference(resolution,[],[f78,f119])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f164,plain,
    ( spl6_15
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f157,f107,f161])).

fof(f157,plain,
    ( r1_tarski(sK3,sK0)
    | ~ spl6_5 ),
    inference(resolution,[],[f79,f109])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f150,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f80,f147])).

fof(f147,plain,
    ( spl6_13
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f80,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f145,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f75,f142])).

fof(f142,plain,
    ( spl6_12
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f75,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f140,plain,(
    ~ spl6_11 ),
    inference(avatar_split_clause,[],[f48,f137])).

fof(f48,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f135,plain,(
    ~ spl6_10 ),
    inference(avatar_split_clause,[],[f49,f132])).

fof(f132,plain,
    ( spl6_10
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f49,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f130,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f50,f127])).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f125,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f51,f122])).

fof(f51,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f120,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f52,f117])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f115,plain,(
    ~ spl6_6 ),
    inference(avatar_split_clause,[],[f53,f112])).

fof(f53,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f110,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f54,f107])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f105,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f55,f102])).

fof(f55,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f100,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f56,f97])).

fof(f56,plain,(
    v1_funct_2(sK4,sK3,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f95,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f57,f92])).

fof(f57,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f90,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f59,f87])).

fof(f59,plain,(
    k2_partfun1(sK0,sK1,sK2,sK3) != sK4 ),
    inference(cnf_transformation,[],[f44])).

%------------------------------------------------------------------------------
