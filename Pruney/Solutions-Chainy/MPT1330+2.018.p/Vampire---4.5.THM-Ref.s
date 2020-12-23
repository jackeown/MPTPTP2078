%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:57 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 379 expanded)
%              Number of leaves         :   50 ( 165 expanded)
%              Depth                    :   12
%              Number of atoms          :  562 (1351 expanded)
%              Number of equality atoms :  110 ( 382 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f453,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f84,f88,f92,f96,f100,f104,f108,f116,f120,f128,f133,f154,f158,f164,f172,f200,f233,f278,f287,f312,f322,f327,f343,f345,f353,f378,f445,f448,f452])).

fof(f452,plain,
    ( ~ spl3_13
    | ~ spl3_35 ),
    inference(avatar_contradiction_clause,[],[f451])).

fof(f451,plain,
    ( $false
    | ~ spl3_13
    | ~ spl3_35 ),
    inference(subsumption_resolution,[],[f132,f342])).

fof(f342,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f341])).

fof(f341,plain,
    ( spl3_35
  <=> ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f132,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl3_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f448,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k2_struct_0(sK0)
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f445,plain,
    ( spl3_48
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f436,f376,f443])).

fof(f443,plain,
    ( spl3_48
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f376,plain,
    ( spl3_40
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f436,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_40 ),
    inference(resolution,[],[f377,f145])).

fof(f145,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f67,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f377,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f376])).

fof(f378,plain,
    ( spl3_40
    | ~ spl3_3
    | ~ spl3_13
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f374,f338,f131,f82,f376])).

fof(f82,plain,
    ( spl3_3
  <=> k1_xboole_0 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f338,plain,
    ( spl3_34
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f374,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_13
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f362,f350])).

fof(f350,plain,
    ( ! [X14] : k1_xboole_0 = k2_zfmisc_1(X14,k2_struct_0(sK1))
    | ~ spl3_34 ),
    inference(resolution,[],[f339,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k2_zfmisc_1(X1,X0) ) ),
    inference(resolution,[],[f63,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(f339,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f338])).

fof(f362,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1))))
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(superposition,[],[f132,f83])).

fof(f83,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f353,plain,
    ( spl3_2
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f351,f338,f79])).

fof(f79,plain,
    ( spl3_2
  <=> k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f351,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl3_34 ),
    inference(resolution,[],[f339,f56])).

fof(f345,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_struct_0(sK0) != u1_struct_0(sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f343,plain,
    ( spl3_29
    | spl3_34
    | ~ spl3_13
    | spl3_35
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f335,f310,f118,f114,f90,f341,f131,f338,f285])).

fof(f285,plain,
    ( spl3_29
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f90,plain,
    ( spl3_5
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f114,plain,
    ( spl3_10
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f118,plain,
    ( spl3_11
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f310,plain,
    ( spl3_32
  <=> ! [X1,X0] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | ~ v4_relat_1(sK2,X0)
        | k1_relat_1(sK2) = X0
        | v1_xboole_0(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f335,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | v1_xboole_0(k2_struct_0(sK1))
        | k2_struct_0(sK0) = k1_relat_1(sK2) )
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_32 ),
    inference(forward_demodulation,[],[f334,f119])).

fof(f119,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f118])).

fof(f334,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | v1_xboole_0(k2_struct_0(sK1))
        | k2_struct_0(sK0) = k1_relat_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))) )
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_32 ),
    inference(forward_demodulation,[],[f333,f119])).

fof(f333,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
        | v1_xboole_0(k2_struct_0(sK1))
        | k2_struct_0(sK0) = k1_relat_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))) )
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_32 ),
    inference(forward_demodulation,[],[f332,f115])).

fof(f115,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f332,plain,
    ( ! [X0] :
        ( v1_xboole_0(k2_struct_0(sK1))
        | k2_struct_0(sK0) = k1_relat_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))) )
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_32 ),
    inference(forward_demodulation,[],[f331,f115])).

fof(f331,plain,
    ( ! [X0] :
        ( k2_struct_0(sK0) = k1_relat_1(sK2)
        | v1_xboole_0(u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))) )
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_32 ),
    inference(forward_demodulation,[],[f329,f119])).

fof(f329,plain,
    ( ! [X0] :
        ( u1_struct_0(sK0) = k1_relat_1(sK2)
        | v1_xboole_0(u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))) )
    | ~ spl3_5
    | ~ spl3_32 ),
    inference(resolution,[],[f328,f91])).

fof(f91,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f328,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | k1_relat_1(sK2) = X0
        | v1_xboole_0(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
    | ~ spl3_32 ),
    inference(resolution,[],[f311,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f311,plain,
    ( ! [X0,X1] :
        ( ~ v4_relat_1(sK2,X0)
        | ~ v1_funct_2(sK2,X0,X1)
        | k1_relat_1(sK2) = X0
        | v1_xboole_0(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f310])).

fof(f327,plain,(
    spl3_33 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | spl3_33 ),
    inference(resolution,[],[f321,f58])).

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f321,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | spl3_33 ),
    inference(avatar_component_clause,[],[f320])).

fof(f320,plain,
    ( spl3_33
  <=> v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f322,plain,
    ( ~ spl3_33
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | spl3_31 ),
    inference(avatar_split_clause,[],[f318,f307,f118,f114,f86,f320])).

fof(f86,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f307,plain,
    ( spl3_31
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f318,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | spl3_31 ),
    inference(forward_demodulation,[],[f317,f119])).

fof(f317,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))
    | ~ spl3_4
    | ~ spl3_10
    | spl3_31 ),
    inference(forward_demodulation,[],[f314,f115])).

fof(f314,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ spl3_4
    | spl3_31 ),
    inference(resolution,[],[f313,f87])).

fof(f87,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f313,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl3_31 ),
    inference(resolution,[],[f308,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f308,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_31 ),
    inference(avatar_component_clause,[],[f307])).

fof(f312,plain,
    ( ~ spl3_31
    | spl3_32
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f305,f94,f310,f307])).

fof(f94,plain,
    ( spl3_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f305,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | k1_relat_1(sK2) = X0
        | ~ v4_relat_1(sK2,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_6 ),
    inference(resolution,[],[f304,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f304,plain,
    ( ! [X0,X1] :
        ( v1_partfun1(sK2,X0)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1) )
    | ~ spl3_6 ),
    inference(resolution,[],[f60,f95])).

fof(f95,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f287,plain,
    ( ~ spl3_28
    | ~ spl3_29
    | spl3_27 ),
    inference(avatar_split_clause,[],[f280,f276,f285,f282])).

fof(f282,plain,
    ( spl3_28
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f276,plain,
    ( spl3_27
  <=> k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f280,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | spl3_27 ),
    inference(inner_rewriting,[],[f279])).

fof(f279,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | spl3_27 ),
    inference(superposition,[],[f277,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f277,plain,
    ( k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | spl3_27 ),
    inference(avatar_component_clause,[],[f276])).

fof(f278,plain,
    ( ~ spl3_13
    | ~ spl3_27
    | spl3_12 ),
    inference(avatar_split_clause,[],[f273,f126,f276,f131])).

fof(f126,plain,
    ( spl3_12
  <=> k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f273,plain,
    ( k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | spl3_12 ),
    inference(superposition,[],[f127,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f127,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f126])).

fof(f233,plain,
    ( ~ spl3_18
    | ~ spl3_9
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f232,f198,f106,f168])).

fof(f168,plain,
    ( spl3_18
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f106,plain,
    ( spl3_9
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f198,plain,
    ( spl3_20
  <=> ! [X6] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f232,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_9
    | ~ spl3_20 ),
    inference(superposition,[],[f199,f146])).

fof(f146,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl3_9 ),
    inference(resolution,[],[f110,f107])).

fof(f107,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f199,plain,
    ( ! [X6] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X6)))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f198])).

fof(f200,plain,
    ( spl3_19
    | spl3_20
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f193,f152,f198,f195])).

fof(f195,plain,
    ( spl3_19
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f152,plain,
    ( spl3_15
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f193,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X6)))
        | k1_xboole_0 = k1_relat_1(k1_xboole_0) )
    | ~ spl3_15 ),
    inference(resolution,[],[f189,f153])).

fof(f153,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f152])).

fof(f189,plain,(
    ! [X4,X3] :
      ( ~ v1_relat_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
      | k1_xboole_0 = k1_relat_1(X3) ) ),
    inference(resolution,[],[f175,f57])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_relat_1(X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f70,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f172,plain,
    ( spl3_18
    | ~ spl3_9
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f171,f162,f106,f168])).

fof(f162,plain,
    ( spl3_17
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f171,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_9
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f166,f146])).

fof(f166,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_17 ),
    inference(superposition,[],[f53,f163])).

fof(f163,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f162])).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f164,plain,
    ( spl3_17
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f159,f156,f162])).

fof(f156,plain,
    ( spl3_16
  <=> m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f159,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl3_16 ),
    inference(resolution,[],[f145,f157])).

fof(f157,plain,
    ( m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f156])).

fof(f158,plain,
    ( spl3_16
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f150,f106,f156])).

fof(f150,plain,
    ( m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_9 ),
    inference(superposition,[],[f53,f146])).

fof(f154,plain,
    ( spl3_15
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f149,f106,f152])).

fof(f149,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_9 ),
    inference(superposition,[],[f58,f146])).

fof(f133,plain,
    ( spl3_13
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f129,f118,f114,f86,f131])).

fof(f129,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f122,f119])).

fof(f122,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(superposition,[],[f87,f115])).

fof(f128,plain,
    ( ~ spl3_12
    | spl3_1
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f124,f118,f114,f75,f126])).

fof(f75,plain,
    ( spl3_1
  <=> k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f124,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_1
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f121,f119])).

fof(f121,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_1
    | ~ spl3_10 ),
    inference(superposition,[],[f76,f115])).

fof(f76,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f120,plain,
    ( spl3_11
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f112,f102,f118])).

fof(f102,plain,
    ( spl3_8
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f112,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_8 ),
    inference(resolution,[],[f54,f103])).

fof(f103,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f102])).

fof(f54,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f116,plain,
    ( spl3_10
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f111,f98,f114])).

fof(f98,plain,
    ( spl3_7
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f111,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f54,f99])).

fof(f99,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f98])).

fof(f108,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f51,f106])).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f104,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f44,f102])).

fof(f44,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    & ( k1_xboole_0 = k2_struct_0(sK0)
      | k1_xboole_0 != k2_struct_0(sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f39,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
                & ( k1_xboole_0 = k2_struct_0(X0)
                  | k1_xboole_0 != k2_struct_0(X1) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(sK0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1))
            & ( k1_xboole_0 = k2_struct_0(sK0)
              | k1_xboole_0 != k2_struct_0(X1) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1))
          & ( k1_xboole_0 = k2_struct_0(sK0)
            | k1_xboole_0 != k2_struct_0(sK1) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X2] :
        ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1))
        & ( k1_xboole_0 = k2_struct_0(sK0)
          | k1_xboole_0 != k2_struct_0(sK1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
      & ( k1_xboole_0 = k2_struct_0(sK0)
        | k1_xboole_0 != k2_struct_0(sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( k1_xboole_0 = k2_struct_0(X1)
                   => k1_xboole_0 = k2_struct_0(X0) )
                 => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).

fof(f100,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f45,f98])).

fof(f45,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f96,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f46,f94])).

fof(f46,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f92,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f47,f90])).

fof(f47,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f88,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f48,f86])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f84,plain,
    ( ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f49,f82,f79])).

fof(f49,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f77,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f50,f75])).

fof(f50,plain,(
    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:17:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (24884)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.47  % (24886)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.48  % (24892)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (24878)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (24878)Refutation not found, incomplete strategy% (24878)------------------------------
% 0.22/0.49  % (24878)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (24878)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (24878)Memory used [KB]: 6268
% 0.22/0.49  % (24878)Time elapsed: 0.060 s
% 0.22/0.49  % (24878)------------------------------
% 0.22/0.49  % (24878)------------------------------
% 0.22/0.49  % (24883)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (24879)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (24887)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (24884)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f453,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f77,f84,f88,f92,f96,f100,f104,f108,f116,f120,f128,f133,f154,f158,f164,f172,f200,f233,f278,f287,f312,f322,f327,f343,f345,f353,f378,f445,f448,f452])).
% 0.22/0.50  fof(f452,plain,(
% 0.22/0.50    ~spl3_13 | ~spl3_35),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f451])).
% 0.22/0.50  fof(f451,plain,(
% 0.22/0.50    $false | (~spl3_13 | ~spl3_35)),
% 0.22/0.50    inference(subsumption_resolution,[],[f132,f342])).
% 0.22/0.50  fof(f342,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))) ) | ~spl3_35),
% 0.22/0.50    inference(avatar_component_clause,[],[f341])).
% 0.22/0.50  fof(f341,plain,(
% 0.22/0.50    spl3_35 <=> ! [X0] : ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f131])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    spl3_13 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.50  fof(f448,plain,(
% 0.22/0.50    k1_xboole_0 != sK2 | k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != k2_struct_0(sK0) | k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.22/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.50  fof(f445,plain,(
% 0.22/0.50    spl3_48 | ~spl3_40),
% 0.22/0.50    inference(avatar_split_clause,[],[f436,f376,f443])).
% 0.22/0.50  fof(f443,plain,(
% 0.22/0.50    spl3_48 <=> k1_xboole_0 = sK2),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.22/0.50  fof(f376,plain,(
% 0.22/0.50    spl3_40 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.22/0.50  fof(f436,plain,(
% 0.22/0.50    k1_xboole_0 = sK2 | ~spl3_40),
% 0.22/0.50    inference(resolution,[],[f377,f145])).
% 0.22/0.50  fof(f145,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(resolution,[],[f67,f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.50    inference(nnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.50  fof(f377,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl3_40),
% 0.22/0.50    inference(avatar_component_clause,[],[f376])).
% 0.22/0.50  fof(f378,plain,(
% 0.22/0.50    spl3_40 | ~spl3_3 | ~spl3_13 | ~spl3_34),
% 0.22/0.50    inference(avatar_split_clause,[],[f374,f338,f131,f82,f376])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    spl3_3 <=> k1_xboole_0 = k2_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.50  fof(f338,plain,(
% 0.22/0.50    spl3_34 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.22/0.50  fof(f374,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl3_3 | ~spl3_13 | ~spl3_34)),
% 0.22/0.50    inference(forward_demodulation,[],[f362,f350])).
% 0.22/0.50  fof(f350,plain,(
% 0.22/0.50    ( ! [X14] : (k1_xboole_0 = k2_zfmisc_1(X14,k2_struct_0(sK1))) ) | ~spl3_34),
% 0.22/0.50    inference(resolution,[],[f339,f110])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_xboole_0(X0) | k1_xboole_0 = k2_zfmisc_1(X1,X0)) )),
% 0.22/0.50    inference(resolution,[],[f63,f56])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).
% 0.22/0.50  fof(f339,plain,(
% 0.22/0.50    v1_xboole_0(k2_struct_0(sK1)) | ~spl3_34),
% 0.22/0.50    inference(avatar_component_clause,[],[f338])).
% 0.22/0.50  fof(f362,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))) | (~spl3_3 | ~spl3_13)),
% 0.22/0.50    inference(superposition,[],[f132,f83])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    k1_xboole_0 = k2_struct_0(sK0) | ~spl3_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f82])).
% 0.22/0.50  fof(f353,plain,(
% 0.22/0.50    spl3_2 | ~spl3_34),
% 0.22/0.50    inference(avatar_split_clause,[],[f351,f338,f79])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    spl3_2 <=> k1_xboole_0 = k2_struct_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.50  fof(f351,plain,(
% 0.22/0.50    k1_xboole_0 = k2_struct_0(sK1) | ~spl3_34),
% 0.22/0.50    inference(resolution,[],[f339,f56])).
% 0.22/0.50  fof(f345,plain,(
% 0.22/0.50    u1_struct_0(sK1) != k2_struct_0(sK1) | k2_struct_0(sK0) != k1_relat_1(sK2) | k2_struct_0(sK0) != u1_struct_0(sK0) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.50  fof(f343,plain,(
% 0.22/0.50    spl3_29 | spl3_34 | ~spl3_13 | spl3_35 | ~spl3_5 | ~spl3_10 | ~spl3_11 | ~spl3_32),
% 0.22/0.50    inference(avatar_split_clause,[],[f335,f310,f118,f114,f90,f341,f131,f338,f285])).
% 0.22/0.50  fof(f285,plain,(
% 0.22/0.50    spl3_29 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    spl3_5 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    spl3_10 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    spl3_11 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.50  fof(f310,plain,(
% 0.22/0.50    spl3_32 <=> ! [X1,X0] : (~v1_funct_2(sK2,X0,X1) | ~v4_relat_1(sK2,X0) | k1_relat_1(sK2) = X0 | v1_xboole_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.22/0.50  fof(f335,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v1_xboole_0(k2_struct_0(sK1)) | k2_struct_0(sK0) = k1_relat_1(sK2)) ) | (~spl3_5 | ~spl3_10 | ~spl3_11 | ~spl3_32)),
% 0.22/0.50    inference(forward_demodulation,[],[f334,f119])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f118])).
% 0.22/0.50  fof(f334,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v1_xboole_0(k2_struct_0(sK1)) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))) ) | (~spl3_5 | ~spl3_10 | ~spl3_11 | ~spl3_32)),
% 0.22/0.50    inference(forward_demodulation,[],[f333,f119])).
% 0.22/0.50  fof(f333,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | v1_xboole_0(k2_struct_0(sK1)) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))) ) | (~spl3_5 | ~spl3_10 | ~spl3_11 | ~spl3_32)),
% 0.22/0.50    inference(forward_demodulation,[],[f332,f115])).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f114])).
% 0.22/0.50  fof(f332,plain,(
% 0.22/0.50    ( ! [X0] : (v1_xboole_0(k2_struct_0(sK1)) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))) ) | (~spl3_5 | ~spl3_10 | ~spl3_11 | ~spl3_32)),
% 0.22/0.50    inference(forward_demodulation,[],[f331,f115])).
% 0.22/0.50  fof(f331,plain,(
% 0.22/0.50    ( ! [X0] : (k2_struct_0(sK0) = k1_relat_1(sK2) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))) ) | (~spl3_5 | ~spl3_11 | ~spl3_32)),
% 0.22/0.50    inference(forward_demodulation,[],[f329,f119])).
% 0.22/0.50  fof(f329,plain,(
% 0.22/0.50    ( ! [X0] : (u1_struct_0(sK0) = k1_relat_1(sK2) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))) ) | (~spl3_5 | ~spl3_32)),
% 0.22/0.50    inference(resolution,[],[f328,f91])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f90])).
% 0.22/0.50  fof(f328,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_funct_2(sK2,X0,X1) | k1_relat_1(sK2) = X0 | v1_xboole_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) ) | ~spl3_32),
% 0.22/0.50    inference(resolution,[],[f311,f70])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.50  fof(f311,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v4_relat_1(sK2,X0) | ~v1_funct_2(sK2,X0,X1) | k1_relat_1(sK2) = X0 | v1_xboole_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_32),
% 0.22/0.50    inference(avatar_component_clause,[],[f310])).
% 0.22/0.50  fof(f327,plain,(
% 0.22/0.50    spl3_33),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f325])).
% 0.22/0.50  fof(f325,plain,(
% 0.22/0.50    $false | spl3_33),
% 0.22/0.50    inference(resolution,[],[f321,f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.50  fof(f321,plain,(
% 0.22/0.50    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | spl3_33),
% 0.22/0.50    inference(avatar_component_clause,[],[f320])).
% 0.22/0.50  fof(f320,plain,(
% 0.22/0.50    spl3_33 <=> v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.22/0.50  fof(f322,plain,(
% 0.22/0.50    ~spl3_33 | ~spl3_4 | ~spl3_10 | ~spl3_11 | spl3_31),
% 0.22/0.50    inference(avatar_split_clause,[],[f318,f307,f118,f114,f86,f320])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.50  fof(f307,plain,(
% 0.22/0.50    spl3_31 <=> v1_relat_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.22/0.50  fof(f318,plain,(
% 0.22/0.50    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | (~spl3_4 | ~spl3_10 | ~spl3_11 | spl3_31)),
% 0.22/0.50    inference(forward_demodulation,[],[f317,f119])).
% 0.22/0.50  fof(f317,plain,(
% 0.22/0.50    ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))) | (~spl3_4 | ~spl3_10 | spl3_31)),
% 0.22/0.50    inference(forward_demodulation,[],[f314,f115])).
% 0.22/0.50  fof(f314,plain,(
% 0.22/0.50    ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | (~spl3_4 | spl3_31)),
% 0.22/0.50    inference(resolution,[],[f313,f87])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f86])).
% 0.22/0.50  fof(f313,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl3_31),
% 0.22/0.50    inference(resolution,[],[f308,f55])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.50  fof(f308,plain,(
% 0.22/0.50    ~v1_relat_1(sK2) | spl3_31),
% 0.22/0.50    inference(avatar_component_clause,[],[f307])).
% 0.22/0.50  fof(f312,plain,(
% 0.22/0.50    ~spl3_31 | spl3_32 | ~spl3_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f305,f94,f310,f307])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    spl3_6 <=> v1_funct_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.50  fof(f305,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | k1_relat_1(sK2) = X0 | ~v4_relat_1(sK2,X0) | ~v1_relat_1(sK2)) ) | ~spl3_6),
% 0.22/0.50    inference(resolution,[],[f304,f65])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.22/0.50  fof(f304,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_partfun1(sK2,X0) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) ) | ~spl3_6),
% 0.22/0.50    inference(resolution,[],[f60,f95])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    v1_funct_1(sK2) | ~spl3_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f94])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.50    inference(flattening,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,axiom,(
% 0.22/0.50    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.22/0.50  fof(f287,plain,(
% 0.22/0.50    ~spl3_28 | ~spl3_29 | spl3_27),
% 0.22/0.50    inference(avatar_split_clause,[],[f280,f276,f285,f282])).
% 0.22/0.50  fof(f282,plain,(
% 0.22/0.50    spl3_28 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.50  fof(f276,plain,(
% 0.22/0.50    spl3_27 <=> k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.22/0.50  fof(f280,plain,(
% 0.22/0.50    k2_struct_0(sK0) != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | spl3_27),
% 0.22/0.50    inference(inner_rewriting,[],[f279])).
% 0.22/0.50  fof(f279,plain,(
% 0.22/0.50    k2_struct_0(sK0) != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | spl3_27),
% 0.22/0.50    inference(superposition,[],[f277,f69])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.50  fof(f277,plain,(
% 0.22/0.50    k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | spl3_27),
% 0.22/0.50    inference(avatar_component_clause,[],[f276])).
% 0.22/0.50  fof(f278,plain,(
% 0.22/0.50    ~spl3_13 | ~spl3_27 | spl3_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f273,f126,f276,f131])).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    spl3_12 <=> k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.50  fof(f273,plain,(
% 0.22/0.50    k2_struct_0(sK0) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | spl3_12),
% 0.22/0.50    inference(superposition,[],[f127,f72])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | spl3_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f126])).
% 0.22/0.50  fof(f233,plain,(
% 0.22/0.50    ~spl3_18 | ~spl3_9 | ~spl3_20),
% 0.22/0.50    inference(avatar_split_clause,[],[f232,f198,f106,f168])).
% 0.22/0.50  fof(f168,plain,(
% 0.22/0.50    spl3_18 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    spl3_9 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.50  fof(f198,plain,(
% 0.22/0.50    spl3_20 <=> ! [X6] : ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X6)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.50  fof(f232,plain,(
% 0.22/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl3_9 | ~spl3_20)),
% 0.22/0.50    inference(superposition,[],[f199,f146])).
% 0.22/0.50  fof(f146,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl3_9),
% 0.22/0.50    inference(resolution,[],[f110,f107])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0) | ~spl3_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f106])).
% 0.22/0.50  fof(f199,plain,(
% 0.22/0.50    ( ! [X6] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X6)))) ) | ~spl3_20),
% 0.22/0.50    inference(avatar_component_clause,[],[f198])).
% 0.22/0.50  fof(f200,plain,(
% 0.22/0.50    spl3_19 | spl3_20 | ~spl3_15),
% 0.22/0.50    inference(avatar_split_clause,[],[f193,f152,f198,f195])).
% 0.22/0.50  fof(f195,plain,(
% 0.22/0.50    spl3_19 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.50  fof(f152,plain,(
% 0.22/0.50    spl3_15 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.50  fof(f193,plain,(
% 0.22/0.50    ( ! [X6] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X6))) | k1_xboole_0 = k1_relat_1(k1_xboole_0)) ) | ~spl3_15),
% 0.22/0.50    inference(resolution,[],[f189,f153])).
% 0.22/0.50  fof(f153,plain,(
% 0.22/0.50    v1_relat_1(k1_xboole_0) | ~spl3_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f152])).
% 0.22/0.50  fof(f189,plain,(
% 0.22/0.50    ( ! [X4,X3] : (~v1_relat_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4))) | k1_xboole_0 = k1_relat_1(X3)) )),
% 0.22/0.50    inference(resolution,[],[f175,f57])).
% 0.22/0.50  fof(f175,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_tarski(k1_relat_1(X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(resolution,[],[f70,f61])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.22/0.50  fof(f172,plain,(
% 0.22/0.50    spl3_18 | ~spl3_9 | ~spl3_17),
% 0.22/0.50    inference(avatar_split_clause,[],[f171,f162,f106,f168])).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    spl3_17 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.50  fof(f171,plain,(
% 0.22/0.50    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl3_9 | ~spl3_17)),
% 0.22/0.50    inference(forward_demodulation,[],[f166,f146])).
% 0.22/0.50  fof(f166,plain,(
% 0.22/0.50    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl3_17),
% 0.22/0.50    inference(superposition,[],[f53,f163])).
% 0.22/0.50  fof(f163,plain,(
% 0.22/0.50    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl3_17),
% 0.22/0.50    inference(avatar_component_clause,[],[f162])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,axiom,(
% 0.22/0.50    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 0.22/0.50  fof(f164,plain,(
% 0.22/0.50    spl3_17 | ~spl3_16),
% 0.22/0.50    inference(avatar_split_clause,[],[f159,f156,f162])).
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    spl3_16 <=> m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl3_16),
% 0.22/0.50    inference(resolution,[],[f145,f157])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl3_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f156])).
% 0.22/0.50  fof(f158,plain,(
% 0.22/0.50    spl3_16 | ~spl3_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f150,f106,f156])).
% 0.22/0.50  fof(f150,plain,(
% 0.22/0.50    m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl3_9),
% 0.22/0.50    inference(superposition,[],[f53,f146])).
% 0.22/0.50  fof(f154,plain,(
% 0.22/0.50    spl3_15 | ~spl3_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f149,f106,f152])).
% 0.22/0.50  fof(f149,plain,(
% 0.22/0.50    v1_relat_1(k1_xboole_0) | ~spl3_9),
% 0.22/0.50    inference(superposition,[],[f58,f146])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    spl3_13 | ~spl3_4 | ~spl3_10 | ~spl3_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f129,f118,f114,f86,f131])).
% 0.22/0.50  fof(f129,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_10 | ~spl3_11)),
% 0.22/0.50    inference(forward_demodulation,[],[f122,f119])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_10)),
% 0.22/0.50    inference(superposition,[],[f87,f115])).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    ~spl3_12 | spl3_1 | ~spl3_10 | ~spl3_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f124,f118,f114,f75,f126])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    spl3_1 <=> k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | (spl3_1 | ~spl3_10 | ~spl3_11)),
% 0.22/0.50    inference(forward_demodulation,[],[f121,f119])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | (spl3_1 | ~spl3_10)),
% 0.22/0.50    inference(superposition,[],[f76,f115])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) | spl3_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f75])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    spl3_11 | ~spl3_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f112,f102,f118])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    spl3_8 <=> l1_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_8),
% 0.22/0.50    inference(resolution,[],[f54,f103])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    l1_struct_0(sK0) | ~spl3_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f102])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,axiom,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    spl3_10 | ~spl3_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f111,f98,f114])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    spl3_7 <=> l1_struct_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_7),
% 0.22/0.50    inference(resolution,[],[f54,f99])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    l1_struct_0(sK1) | ~spl3_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f98])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    spl3_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f51,f106])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    spl3_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f44,f102])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    l1_struct_0(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ((k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f39,f38,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ? [X1] : (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f18])).
% 0.22/0.50  fof(f18,conjecture,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    spl3_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f45,f98])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    l1_struct_0(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    spl3_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f46,f94])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    v1_funct_1(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    spl3_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f47,f90])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    spl3_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f48,f86])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    ~spl3_2 | spl3_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f49,f82,f79])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    ~spl3_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f50,f75])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (24884)------------------------------
% 0.22/0.50  % (24884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (24884)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (24884)Memory used [KB]: 10874
% 0.22/0.50  % (24884)Time elapsed: 0.060 s
% 0.22/0.50  % (24884)------------------------------
% 0.22/0.50  % (24884)------------------------------
% 0.22/0.50  % (24877)Success in time 0.135 s
%------------------------------------------------------------------------------
