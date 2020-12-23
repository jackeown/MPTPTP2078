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
% DateTime   : Thu Dec  3 13:05:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 226 expanded)
%              Number of leaves         :   36 (  95 expanded)
%              Depth                    :    8
%              Number of atoms          :  428 ( 808 expanded)
%              Number of equality atoms :   58 (  75 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f316,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f79,f84,f94,f99,f104,f109,f120,f130,f135,f146,f151,f184,f203,f257,f269,f276,f298,f301,f311,f314,f315])).

fof(f315,plain,
    ( sK2 != k6_partfun1(sK0)
    | r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,sK2,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f314,plain,
    ( ~ spl3_9
    | ~ spl3_11
    | spl3_37 ),
    inference(avatar_contradiction_clause,[],[f312])).

fof(f312,plain,
    ( $false
    | ~ spl3_9
    | ~ spl3_11
    | spl3_37 ),
    inference(unit_resulting_resolution,[],[f119,f129,f310,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f310,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK0)
    | spl3_37 ),
    inference(avatar_component_clause,[],[f308])).

fof(f308,plain,
    ( spl3_37
  <=> r1_tarski(k2_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f129,plain,
    ( v5_relat_1(sK2,sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl3_11
  <=> v5_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f119,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl3_9
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f311,plain,
    ( ~ spl3_9
    | ~ spl3_37
    | spl3_30
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f302,f295,f242,f308,f117])).

fof(f242,plain,
    ( spl3_30
  <=> sK2 = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f295,plain,
    ( spl3_36
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f302,plain,
    ( sK2 = k6_partfun1(sK0)
    | ~ r1_tarski(k2_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl3_36 ),
    inference(superposition,[],[f297,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f52,f46])).

fof(f46,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f297,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k6_partfun1(sK0))
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f295])).

fof(f301,plain,
    ( ~ spl3_3
    | ~ spl3_13
    | spl3_35 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_13
    | spl3_35 ),
    inference(unit_resulting_resolution,[],[f145,f83,f293,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f293,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | spl3_35 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl3_35
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f83,plain,
    ( v1_funct_1(sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_3
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f145,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl3_13
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f298,plain,
    ( ~ spl3_13
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_35
    | spl3_36
    | ~ spl3_23
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f281,f274,f200,f295,f291,f81,f76,f143])).

fof(f76,plain,
    ( spl3_2
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f200,plain,
    ( spl3_23
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f274,plain,
    ( spl3_34
  <=> ! [X2] :
        ( k5_relat_1(sK1,X2) = k5_relat_1(sK2,k5_relat_1(sK1,X2))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f281,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k6_partfun1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_23
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f277,f202])).

fof(f202,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f200])).

fof(f277,plain,
    ( k6_partfun1(k1_relat_1(sK1)) = k5_relat_1(sK2,k6_partfun1(k1_relat_1(sK1)))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_34 ),
    inference(superposition,[],[f275,f66])).

fof(f66,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f50,f46])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f275,plain,
    ( ! [X2] :
        ( k5_relat_1(sK1,X2) = k5_relat_1(sK2,k5_relat_1(sK1,X2))
        | ~ v1_relat_1(X2) )
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f274])).

fof(f276,plain,
    ( ~ spl3_9
    | ~ spl3_13
    | spl3_34
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f272,f266,f274,f143,f117])).

fof(f266,plain,
    ( spl3_33
  <=> sK1 = k5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f272,plain,
    ( ! [X2] :
        ( k5_relat_1(sK1,X2) = k5_relat_1(sK2,k5_relat_1(sK1,X2))
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_33 ),
    inference(superposition,[],[f47,f268])).

fof(f268,plain,
    ( sK1 = k5_relat_1(sK2,sK1)
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f266])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f269,plain,
    ( ~ spl3_1
    | ~ spl3_8
    | ~ spl3_3
    | ~ spl3_6
    | spl3_33
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f259,f254,f266,f96,f81,f106,f71])).

fof(f71,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f106,plain,
    ( spl3_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f96,plain,
    ( spl3_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f254,plain,
    ( spl3_32
  <=> sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f259,plain,
    ( sK1 = k5_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl3_32 ),
    inference(superposition,[],[f256,f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f256,plain,
    ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f254])).

fof(f257,plain,
    ( ~ spl3_1
    | ~ spl3_8
    | ~ spl3_3
    | ~ spl3_6
    | spl3_32
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f250,f148,f106,f254,f96,f81,f106,f71])).

fof(f148,plain,
    ( spl3_14
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f250,plain,
    ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(resolution,[],[f204,f150])).

fof(f150,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f148])).

fof(f204,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,X0,X1,sK0,X2,X3),sK1)
        | sK1 = k1_partfun1(sK0,X0,X1,sK0,X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
        | ~ v1_funct_1(X2) )
    | ~ spl3_8 ),
    inference(resolution,[],[f138,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f138,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | sK1 = X0
        | ~ r2_relset_1(sK0,sK0,X0,sK1) )
    | ~ spl3_8 ),
    inference(resolution,[],[f108,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f108,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f203,plain,
    ( ~ spl3_8
    | spl3_23
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f185,f181,f200,f106])).

fof(f181,plain,
    ( spl3_20
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f185,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_20 ),
    inference(superposition,[],[f183,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f183,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f181])).

fof(f184,plain,
    ( spl3_20
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f136,f106,f91,f81,f181])).

fof(f91,plain,
    ( spl3_5
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f136,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl3_8 ),
    inference(resolution,[],[f108,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | k1_relset_1(X0,X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(f151,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f40,f148])).

fof(f40,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( ( v2_funct_1(X1)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
             => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
           => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_funct_2)).

fof(f146,plain,
    ( spl3_13
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f141,f106,f143])).

fof(f141,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_8 ),
    inference(resolution,[],[f108,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f135,plain,
    ( spl3_12
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f111,f96,f132])).

fof(f132,plain,
    ( spl3_12
  <=> r2_relset_1(sK0,sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f111,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ spl3_6 ),
    inference(resolution,[],[f98,f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f98,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f130,plain,
    ( spl3_11
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f114,f96,f127])).

fof(f114,plain,
    ( v5_relat_1(sK2,sK0)
    | ~ spl3_6 ),
    inference(resolution,[],[f98,f59])).

% (6610)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f120,plain,
    ( spl3_9
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f115,f96,f117])).

fof(f115,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_6 ),
    inference(resolution,[],[f98,f56])).

fof(f109,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f45,f106])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f104,plain,(
    ~ spl3_7 ),
    inference(avatar_split_clause,[],[f42,f101])).

fof(f101,plain,
    ( spl3_7
  <=> r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f42,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f99,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f39,f96])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f94,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f44,f91])).

fof(f44,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f84,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f43,f81])).

fof(f43,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f79,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f41,f76])).

fof(f41,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f74,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f37,f71])).

fof(f37,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:19:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (6585)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (6600)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.51  % (6588)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (6606)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (6592)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (6584)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (6600)Refutation not found, incomplete strategy% (6600)------------------------------
% 0.21/0.52  % (6600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (6600)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (6600)Memory used [KB]: 10746
% 0.21/0.52  % (6600)Time elapsed: 0.118 s
% 0.21/0.52  % (6600)------------------------------
% 0.21/0.52  % (6600)------------------------------
% 0.21/0.52  % (6605)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (6613)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (6596)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (6589)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (6598)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (6595)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (6599)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (6597)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (6612)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (6587)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (6603)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (6604)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (6586)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (6607)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (6594)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (6611)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (6591)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (6608)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (6590)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (6612)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % (6602)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (6609)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.56  % (6593)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.56  % (6601)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f316,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f74,f79,f84,f94,f99,f104,f109,f120,f130,f135,f146,f151,f184,f203,f257,f269,f276,f298,f301,f311,f314,f315])).
% 0.21/0.56  fof(f315,plain,(
% 0.21/0.56    sK2 != k6_partfun1(sK0) | r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,sK2,sK2)),
% 0.21/0.56    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.56  fof(f314,plain,(
% 0.21/0.56    ~spl3_9 | ~spl3_11 | spl3_37),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f312])).
% 0.21/0.56  fof(f312,plain,(
% 0.21/0.56    $false | (~spl3_9 | ~spl3_11 | spl3_37)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f119,f129,f310,f54])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.56  fof(f310,plain,(
% 0.21/0.56    ~r1_tarski(k2_relat_1(sK2),sK0) | spl3_37),
% 0.21/0.56    inference(avatar_component_clause,[],[f308])).
% 0.21/0.56  fof(f308,plain,(
% 0.21/0.56    spl3_37 <=> r1_tarski(k2_relat_1(sK2),sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.21/0.56  fof(f129,plain,(
% 0.21/0.56    v5_relat_1(sK2,sK0) | ~spl3_11),
% 0.21/0.56    inference(avatar_component_clause,[],[f127])).
% 0.21/0.56  fof(f127,plain,(
% 0.21/0.56    spl3_11 <=> v5_relat_1(sK2,sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.56  fof(f119,plain,(
% 0.21/0.56    v1_relat_1(sK2) | ~spl3_9),
% 0.21/0.56    inference(avatar_component_clause,[],[f117])).
% 0.21/0.56  fof(f117,plain,(
% 0.21/0.56    spl3_9 <=> v1_relat_1(sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.56  fof(f311,plain,(
% 0.21/0.56    ~spl3_9 | ~spl3_37 | spl3_30 | ~spl3_36),
% 0.21/0.56    inference(avatar_split_clause,[],[f302,f295,f242,f308,f117])).
% 0.21/0.56  fof(f242,plain,(
% 0.21/0.56    spl3_30 <=> sK2 = k6_partfun1(sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.56  fof(f295,plain,(
% 0.21/0.56    spl3_36 <=> k6_partfun1(sK0) = k5_relat_1(sK2,k6_partfun1(sK0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.21/0.56  fof(f302,plain,(
% 0.21/0.56    sK2 = k6_partfun1(sK0) | ~r1_tarski(k2_relat_1(sK2),sK0) | ~v1_relat_1(sK2) | ~spl3_36),
% 0.21/0.56    inference(superposition,[],[f297,f67])).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f52,f46])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,axiom,(
% 0.21/0.56    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.56    inference(flattening,[],[f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.21/0.56  fof(f297,plain,(
% 0.21/0.56    k6_partfun1(sK0) = k5_relat_1(sK2,k6_partfun1(sK0)) | ~spl3_36),
% 0.21/0.56    inference(avatar_component_clause,[],[f295])).
% 0.21/0.56  fof(f301,plain,(
% 0.21/0.56    ~spl3_3 | ~spl3_13 | spl3_35),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f299])).
% 0.21/0.56  fof(f299,plain,(
% 0.21/0.56    $false | (~spl3_3 | ~spl3_13 | spl3_35)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f145,f83,f293,f48])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f20])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(flattening,[],[f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.56  fof(f293,plain,(
% 0.21/0.56    ~v1_relat_1(k2_funct_1(sK1)) | spl3_35),
% 0.21/0.56    inference(avatar_component_clause,[],[f291])).
% 0.21/0.56  fof(f291,plain,(
% 0.21/0.56    spl3_35 <=> v1_relat_1(k2_funct_1(sK1))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.21/0.56  fof(f83,plain,(
% 0.21/0.56    v1_funct_1(sK1) | ~spl3_3),
% 0.21/0.56    inference(avatar_component_clause,[],[f81])).
% 0.21/0.56  fof(f81,plain,(
% 0.21/0.56    spl3_3 <=> v1_funct_1(sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.56  fof(f145,plain,(
% 0.21/0.56    v1_relat_1(sK1) | ~spl3_13),
% 0.21/0.56    inference(avatar_component_clause,[],[f143])).
% 0.21/0.56  fof(f143,plain,(
% 0.21/0.56    spl3_13 <=> v1_relat_1(sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.57  fof(f298,plain,(
% 0.21/0.57    ~spl3_13 | ~spl3_2 | ~spl3_3 | ~spl3_35 | spl3_36 | ~spl3_23 | ~spl3_34),
% 0.21/0.57    inference(avatar_split_clause,[],[f281,f274,f200,f295,f291,f81,f76,f143])).
% 0.21/0.57  fof(f76,plain,(
% 0.21/0.57    spl3_2 <=> v2_funct_1(sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.57  fof(f200,plain,(
% 0.21/0.57    spl3_23 <=> sK0 = k1_relat_1(sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.57  fof(f274,plain,(
% 0.21/0.57    spl3_34 <=> ! [X2] : (k5_relat_1(sK1,X2) = k5_relat_1(sK2,k5_relat_1(sK1,X2)) | ~v1_relat_1(X2))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.21/0.57  fof(f281,plain,(
% 0.21/0.57    k6_partfun1(sK0) = k5_relat_1(sK2,k6_partfun1(sK0)) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl3_23 | ~spl3_34)),
% 0.21/0.57    inference(forward_demodulation,[],[f277,f202])).
% 0.21/0.57  fof(f202,plain,(
% 0.21/0.57    sK0 = k1_relat_1(sK1) | ~spl3_23),
% 0.21/0.57    inference(avatar_component_clause,[],[f200])).
% 0.21/0.57  fof(f277,plain,(
% 0.21/0.57    k6_partfun1(k1_relat_1(sK1)) = k5_relat_1(sK2,k6_partfun1(k1_relat_1(sK1))) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl3_34),
% 0.21/0.57    inference(superposition,[],[f275,f66])).
% 0.21/0.57  fof(f66,plain,(
% 0.21/0.57    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f50,f46])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(flattening,[],[f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.21/0.57  fof(f275,plain,(
% 0.21/0.57    ( ! [X2] : (k5_relat_1(sK1,X2) = k5_relat_1(sK2,k5_relat_1(sK1,X2)) | ~v1_relat_1(X2)) ) | ~spl3_34),
% 0.21/0.57    inference(avatar_component_clause,[],[f274])).
% 0.21/0.57  fof(f276,plain,(
% 0.21/0.57    ~spl3_9 | ~spl3_13 | spl3_34 | ~spl3_33),
% 0.21/0.57    inference(avatar_split_clause,[],[f272,f266,f274,f143,f117])).
% 0.21/0.57  fof(f266,plain,(
% 0.21/0.57    spl3_33 <=> sK1 = k5_relat_1(sK2,sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.21/0.57  fof(f272,plain,(
% 0.21/0.57    ( ! [X2] : (k5_relat_1(sK1,X2) = k5_relat_1(sK2,k5_relat_1(sK1,X2)) | ~v1_relat_1(sK1) | ~v1_relat_1(X2) | ~v1_relat_1(sK2)) ) | ~spl3_33),
% 0.21/0.57    inference(superposition,[],[f47,f268])).
% 0.21/0.57  fof(f268,plain,(
% 0.21/0.57    sK1 = k5_relat_1(sK2,sK1) | ~spl3_33),
% 0.21/0.57    inference(avatar_component_clause,[],[f266])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 0.21/0.57  fof(f269,plain,(
% 0.21/0.57    ~spl3_1 | ~spl3_8 | ~spl3_3 | ~spl3_6 | spl3_33 | ~spl3_32),
% 0.21/0.57    inference(avatar_split_clause,[],[f259,f254,f266,f96,f81,f106,f71])).
% 0.21/0.57  fof(f71,plain,(
% 0.21/0.57    spl3_1 <=> v1_funct_1(sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.57  fof(f106,plain,(
% 0.21/0.57    spl3_8 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.57  fof(f96,plain,(
% 0.21/0.57    spl3_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.57  fof(f254,plain,(
% 0.21/0.57    spl3_32 <=> sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.57  fof(f259,plain,(
% 0.21/0.57    sK1 = k5_relat_1(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~spl3_32),
% 0.21/0.57    inference(superposition,[],[f256,f62])).
% 0.21/0.57  fof(f62,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.57    inference(flattening,[],[f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.57    inference(ennf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.21/0.57  fof(f256,plain,(
% 0.21/0.57    sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) | ~spl3_32),
% 0.21/0.57    inference(avatar_component_clause,[],[f254])).
% 0.21/0.57  fof(f257,plain,(
% 0.21/0.57    ~spl3_1 | ~spl3_8 | ~spl3_3 | ~spl3_6 | spl3_32 | ~spl3_8 | ~spl3_14),
% 0.21/0.57    inference(avatar_split_clause,[],[f250,f148,f106,f254,f96,f81,f106,f71])).
% 0.21/0.57  fof(f148,plain,(
% 0.21/0.57    spl3_14 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.57  fof(f250,plain,(
% 0.21/0.57    sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | (~spl3_8 | ~spl3_14)),
% 0.21/0.57    inference(resolution,[],[f204,f150])).
% 0.21/0.57  fof(f150,plain,(
% 0.21/0.57    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) | ~spl3_14),
% 0.21/0.57    inference(avatar_component_clause,[],[f148])).
% 0.21/0.57  fof(f204,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,X0,X1,sK0,X2,X3),sK1) | sK1 = k1_partfun1(sK0,X0,X1,sK0,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) | ~v1_funct_1(X2)) ) | ~spl3_8),
% 0.21/0.57    inference(resolution,[],[f138,f64])).
% 0.21/0.57  fof(f64,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f36])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.57    inference(flattening,[],[f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 0.21/0.57  fof(f138,plain,(
% 0.21/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK1 = X0 | ~r2_relset_1(sK0,sK0,X0,sK1)) ) | ~spl3_8),
% 0.21/0.57    inference(resolution,[],[f108,f61])).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(flattening,[],[f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.57    inference(ennf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.21/0.57  fof(f108,plain,(
% 0.21/0.57    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_8),
% 0.21/0.57    inference(avatar_component_clause,[],[f106])).
% 0.21/0.57  fof(f203,plain,(
% 0.21/0.57    ~spl3_8 | spl3_23 | ~spl3_20),
% 0.21/0.57    inference(avatar_split_clause,[],[f185,f181,f200,f106])).
% 0.21/0.57  fof(f181,plain,(
% 0.21/0.57    spl3_20 <=> sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.57  fof(f185,plain,(
% 0.21/0.57    sK0 = k1_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_20),
% 0.21/0.57    inference(superposition,[],[f183,f57])).
% 0.21/0.57  fof(f57,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.57  fof(f183,plain,(
% 0.21/0.57    sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl3_20),
% 0.21/0.57    inference(avatar_component_clause,[],[f181])).
% 0.21/0.57  fof(f184,plain,(
% 0.21/0.57    spl3_20 | ~spl3_3 | ~spl3_5 | ~spl3_8),
% 0.21/0.57    inference(avatar_split_clause,[],[f136,f106,f91,f81,f181])).
% 0.21/0.57  fof(f91,plain,(
% 0.21/0.57    spl3_5 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.57  fof(f136,plain,(
% 0.21/0.57    ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl3_8),
% 0.21/0.57    inference(resolution,[],[f108,f55])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | k1_relset_1(X0,X0,X1) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.57    inference(flattening,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,axiom,(
% 0.21/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).
% 0.21/0.57  fof(f151,plain,(
% 0.21/0.57    spl3_14),
% 0.21/0.57    inference(avatar_split_clause,[],[f40,f148])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.57    inference(flattening,[],[f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 0.21/0.57    inference(negated_conjecture,[],[f14])).
% 0.21/0.57  fof(f14,conjecture,(
% 0.21/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_funct_2)).
% 0.21/0.57  fof(f146,plain,(
% 0.21/0.57    spl3_13 | ~spl3_8),
% 0.21/0.57    inference(avatar_split_clause,[],[f141,f106,f143])).
% 0.21/0.57  fof(f141,plain,(
% 0.21/0.57    v1_relat_1(sK1) | ~spl3_8),
% 0.21/0.57    inference(resolution,[],[f108,f56])).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.57  fof(f135,plain,(
% 0.21/0.57    spl3_12 | ~spl3_6),
% 0.21/0.57    inference(avatar_split_clause,[],[f111,f96,f132])).
% 0.21/0.57  fof(f132,plain,(
% 0.21/0.57    spl3_12 <=> r2_relset_1(sK0,sK0,sK2,sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.57  fof(f111,plain,(
% 0.21/0.57    r2_relset_1(sK0,sK0,sK2,sK2) | ~spl3_6),
% 0.21/0.57    inference(resolution,[],[f98,f69])).
% 0.21/0.57  fof(f69,plain,(
% 0.21/0.57    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f68])).
% 0.21/0.57  fof(f68,plain,(
% 0.21/0.57    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.21/0.57    inference(equality_resolution,[],[f60])).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f32])).
% 0.21/0.57  fof(f98,plain,(
% 0.21/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_6),
% 0.21/0.57    inference(avatar_component_clause,[],[f96])).
% 0.21/0.57  fof(f130,plain,(
% 0.21/0.57    spl3_11 | ~spl3_6),
% 0.21/0.57    inference(avatar_split_clause,[],[f114,f96,f127])).
% 0.21/0.57  fof(f114,plain,(
% 0.21/0.57    v5_relat_1(sK2,sK0) | ~spl3_6),
% 0.21/0.57    inference(resolution,[],[f98,f59])).
% 0.21/0.57  % (6610)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.57  fof(f59,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.57  fof(f120,plain,(
% 0.21/0.57    spl3_9 | ~spl3_6),
% 0.21/0.57    inference(avatar_split_clause,[],[f115,f96,f117])).
% 0.21/0.57  fof(f115,plain,(
% 0.21/0.57    v1_relat_1(sK2) | ~spl3_6),
% 0.21/0.57    inference(resolution,[],[f98,f56])).
% 0.21/0.57  fof(f109,plain,(
% 0.21/0.57    spl3_8),
% 0.21/0.57    inference(avatar_split_clause,[],[f45,f106])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f104,plain,(
% 0.21/0.57    ~spl3_7),
% 0.21/0.57    inference(avatar_split_clause,[],[f42,f101])).
% 0.21/0.57  fof(f101,plain,(
% 0.21/0.57    spl3_7 <=> r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f99,plain,(
% 0.21/0.57    spl3_6),
% 0.21/0.57    inference(avatar_split_clause,[],[f39,f96])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f94,plain,(
% 0.21/0.57    spl3_5),
% 0.21/0.57    inference(avatar_split_clause,[],[f44,f91])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f84,plain,(
% 0.21/0.57    spl3_3),
% 0.21/0.57    inference(avatar_split_clause,[],[f43,f81])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    v1_funct_1(sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f79,plain,(
% 0.21/0.57    spl3_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f41,f76])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    v2_funct_1(sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f74,plain,(
% 0.21/0.57    spl3_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f37,f71])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    v1_funct_1(sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (6612)------------------------------
% 0.21/0.57  % (6612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (6612)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (6612)Memory used [KB]: 11001
% 0.21/0.57  % (6612)Time elapsed: 0.139 s
% 0.21/0.57  % (6612)------------------------------
% 0.21/0.57  % (6612)------------------------------
% 1.60/0.57  % (6583)Success in time 0.213 s
%------------------------------------------------------------------------------
