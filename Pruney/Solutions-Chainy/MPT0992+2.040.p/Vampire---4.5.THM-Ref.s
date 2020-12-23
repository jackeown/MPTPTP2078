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
% DateTime   : Thu Dec  3 13:03:15 EST 2020

% Result     : Theorem 2.38s
% Output     : Refutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :  188 ( 319 expanded)
%              Number of leaves         :   49 ( 139 expanded)
%              Depth                    :    8
%              Number of atoms          :  526 ( 969 expanded)
%              Number of equality atoms :   90 ( 178 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3915,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f99,f104,f109,f118,f131,f161,f217,f233,f239,f257,f379,f449,f524,f536,f542,f543,f544,f558,f583,f615,f674,f946,f949,f957,f1020,f1034,f3866,f3872,f3890,f3891,f3914])).

fof(f3914,plain,
    ( sK3 != k7_relat_1(sK3,sK0)
    | k1_xboole_0 != sK2
    | k1_xboole_0 != sK0
    | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ v1_funct_2(sK3,sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3891,plain,
    ( spl5_213
    | ~ spl5_214
    | spl5_6
    | ~ spl5_61 ),
    inference(avatar_split_clause,[],[f3879,f612,f115,f3887,f3869])).

fof(f3869,plain,
    ( spl5_213
  <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_213])])).

fof(f3887,plain,
    ( spl5_214
  <=> sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_214])])).

fof(f115,plain,
    ( spl5_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f612,plain,
    ( spl5_61
  <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f3879,plain,
    ( k1_xboole_0 = sK1
    | sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ spl5_61 ),
    inference(resolution,[],[f613,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f613,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl5_61 ),
    inference(avatar_component_clause,[],[f612])).

fof(f3890,plain,
    ( spl5_214
    | ~ spl5_61
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f3885,f943,f612,f3887])).

fof(f943,plain,
    ( spl5_72
  <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).

fof(f3885,plain,
    ( sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | ~ spl5_61
    | ~ spl5_72 ),
    inference(forward_demodulation,[],[f3876,f945])).

fof(f945,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl5_72 ),
    inference(avatar_component_clause,[],[f943])).

fof(f3876,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | ~ spl5_61 ),
    inference(resolution,[],[f613,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f3872,plain,
    ( ~ spl5_213
    | spl5_8
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f3867,f414,f124,f3869])).

fof(f124,plain,
    ( spl5_8
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f414,plain,
    ( spl5_36
  <=> ! [X6] : k2_partfun1(sK0,sK1,sK3,X6) = k7_relat_1(sK3,X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f3867,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl5_8
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f126,f415])).

fof(f415,plain,
    ( ! [X6] : k2_partfun1(sK0,sK1,sK3,X6) = k7_relat_1(sK3,X6)
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f414])).

fof(f126,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f124])).

fof(f3866,plain,
    ( spl5_61
    | ~ spl5_12
    | ~ spl5_21
    | ~ spl5_81 ),
    inference(avatar_split_clause,[],[f3859,f1018,f236,f158,f612])).

fof(f158,plain,
    ( spl5_12
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f236,plain,
    ( spl5_21
  <=> r1_tarski(k2_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f1018,plain,
    ( spl5_81
  <=> ! [X1,X0] :
        ( ~ r1_tarski(sK2,X0)
        | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).

fof(f3859,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl5_12
    | ~ spl5_21
    | ~ spl5_81 ),
    inference(resolution,[],[f2432,f1333])).

fof(f1333,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
    | ~ spl5_12
    | ~ spl5_21 ),
    inference(resolution,[],[f436,f238])).

fof(f238,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f236])).

fof(f436,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),X1)
        | r1_tarski(k2_relat_1(k7_relat_1(sK3,X2)),X1) )
    | ~ spl5_12 ),
    inference(resolution,[],[f167,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f167,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),k2_relat_1(sK3))
    | ~ spl5_12 ),
    inference(resolution,[],[f53,f160])).

fof(f160,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f158])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

fof(f2432,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1)
        | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) )
    | ~ spl5_81 ),
    inference(resolution,[],[f1019,f150])).

fof(f150,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f149])).

fof(f149,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f62,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1019,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK2,X0)
        | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) )
    | ~ spl5_81 ),
    inference(avatar_component_clause,[],[f1018])).

fof(f1034,plain,
    ( ~ spl5_36
    | ~ spl5_37
    | spl5_80 ),
    inference(avatar_contradiction_clause,[],[f1033])).

fof(f1033,plain,
    ( $false
    | ~ spl5_36
    | ~ spl5_37
    | spl5_80 ),
    inference(resolution,[],[f1016,f623])).

fof(f623,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK3,X0))
    | ~ spl5_36
    | ~ spl5_37 ),
    inference(resolution,[],[f618,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f618,plain,
    ( ! [X6] : m1_subset_1(k7_relat_1(sK3,X6),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_36
    | ~ spl5_37 ),
    inference(forward_demodulation,[],[f424,f415])).

fof(f424,plain,
    ( ! [X6] : m1_subset_1(k2_partfun1(sK0,sK1,sK3,X6),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f423])).

fof(f423,plain,
    ( spl5_37
  <=> ! [X6] : m1_subset_1(k2_partfun1(sK0,sK1,sK3,X6),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f1016,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | spl5_80 ),
    inference(avatar_component_clause,[],[f1014])).

fof(f1014,plain,
    ( spl5_80
  <=> v1_relat_1(k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).

fof(f1020,plain,
    ( ~ spl5_80
    | spl5_81
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f1009,f943,f1018,f1014])).

fof(f1009,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK2,X0)
        | ~ v1_relat_1(k7_relat_1(sK3,sK2))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1)
        | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_72 ),
    inference(superposition,[],[f68,f945])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f957,plain,
    ( spl5_67
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f685,f464,f689])).

fof(f689,plain,
    ( spl5_67
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f464,plain,
    ( spl5_39
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f685,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_39 ),
    inference(resolution,[],[f466,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f466,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f464])).

fof(f949,plain,
    ( sK3 != k7_relat_1(sK3,sK0)
    | k1_xboole_0 != k1_relat_1(k7_relat_1(sK3,k1_xboole_0))
    | k1_xboole_0 != sK0
    | sK0 = k1_relat_1(sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f946,plain,
    ( spl5_72
    | ~ spl5_1
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f940,f556,f91,f943])).

fof(f91,plain,
    ( spl5_1
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f556,plain,
    ( spl5_52
  <=> ! [X2] :
        ( ~ r1_tarski(X2,sK0)
        | k1_relat_1(k7_relat_1(sK3,X2)) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f940,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl5_1
    | ~ spl5_52 ),
    inference(resolution,[],[f557,f93])).

fof(f93,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f557,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK0)
        | k1_relat_1(k7_relat_1(sK3,X2)) = X2 )
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f556])).

fof(f674,plain,
    ( spl5_39
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f450,f111,f91,f464])).

fof(f111,plain,
    ( spl5_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f450,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f93,f113])).

fof(f113,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f111])).

fof(f615,plain,
    ( ~ spl5_61
    | spl5_7
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f609,f414,f120,f612])).

fof(f120,plain,
    ( spl5_7
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f609,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl5_7
    | ~ spl5_36 ),
    inference(backward_demodulation,[],[f122,f415])).

fof(f122,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f120])).

fof(f583,plain,
    ( spl5_55
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f576,f158,f580])).

fof(f580,plain,
    ( spl5_55
  <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).

fof(f576,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_xboole_0))
    | ~ spl5_12 ),
    inference(resolution,[],[f274,f160])).

fof(f274,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 = k1_relat_1(k7_relat_1(X1,k1_xboole_0)) ) ),
    inference(resolution,[],[f54,f51])).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f558,plain,
    ( ~ spl5_12
    | spl5_52
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f548,f446,f556,f158])).

fof(f446,plain,
    ( spl5_38
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f548,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK0)
        | ~ v1_relat_1(sK3)
        | k1_relat_1(k7_relat_1(sK3,X2)) = X2 )
    | ~ spl5_38 ),
    inference(superposition,[],[f54,f448])).

fof(f448,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f446])).

fof(f544,plain,
    ( spl5_37
    | ~ spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f534,f96,f106,f423])).

fof(f106,plain,
    ( spl5_4
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f96,plain,
    ( spl5_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f534,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(sK3)
        | m1_subset_1(k2_partfun1(sK0,sK1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
    | ~ spl5_2 ),
    inference(resolution,[],[f98,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f98,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f543,plain,
    ( spl5_34
    | ~ spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f533,f96,f106,f349])).

fof(f349,plain,
    ( spl5_34
  <=> ! [X6] : v1_funct_1(k2_partfun1(sK0,sK1,sK3,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f533,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK3)
        | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X1)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f98,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f542,plain,
    ( spl5_36
    | ~ spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f532,f96,f106,f414])).

fof(f532,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK3)
        | k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f98,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f536,plain,
    ( spl5_27
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f527,f96,f303])).

fof(f303,plain,
    ( spl5_27
  <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f527,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl5_2 ),
    inference(resolution,[],[f98,f70])).

fof(f524,plain,
    ( ~ spl5_12
    | spl5_19
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f523,f214,f220,f158])).

fof(f220,plain,
    ( spl5_19
  <=> r1_tarski(k1_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f214,plain,
    ( spl5_18
  <=> v4_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f523,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl5_18 ),
    inference(resolution,[],[f216,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f216,plain,
    ( v4_relat_1(sK3,sK0)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f214])).

fof(f449,plain,
    ( ~ spl5_3
    | spl5_6
    | spl5_38
    | ~ spl5_2
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f444,f303,f96,f446,f115,f101])).

fof(f101,plain,
    ( spl5_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f444,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl5_2
    | ~ spl5_27 ),
    inference(forward_demodulation,[],[f441,f305])).

fof(f305,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f303])).

fof(f441,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f78,f98])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f379,plain,
    ( spl5_9
    | ~ spl5_34 ),
    inference(avatar_contradiction_clause,[],[f378])).

fof(f378,plain,
    ( $false
    | spl5_9
    | ~ spl5_34 ),
    inference(resolution,[],[f350,f130])).

fof(f130,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl5_9
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f350,plain,
    ( ! [X6] : v1_funct_1(k2_partfun1(sK0,sK1,sK3,X6))
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f349])).

fof(f257,plain,
    ( spl5_22
    | ~ spl5_12
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f249,f220,f158,f254])).

fof(f254,plain,
    ( spl5_22
  <=> sK3 = k7_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f249,plain,
    ( ~ v1_relat_1(sK3)
    | sK3 = k7_relat_1(sK3,sK0)
    | ~ spl5_19 ),
    inference(resolution,[],[f222,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f222,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f220])).

fof(f239,plain,
    ( ~ spl5_12
    | spl5_21
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f234,f230,f236,f158])).

fof(f230,plain,
    ( spl5_20
  <=> v5_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f234,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3)
    | ~ spl5_20 ),
    inference(resolution,[],[f232,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f232,plain,
    ( v5_relat_1(sK3,sK1)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f230])).

fof(f233,plain,
    ( spl5_20
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f226,f96,f230])).

fof(f226,plain,
    ( v5_relat_1(sK3,sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f72,f98])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f217,plain,
    ( spl5_18
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f210,f96,f214])).

fof(f210,plain,
    ( v4_relat_1(sK3,sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f71,f98])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f161,plain,
    ( spl5_12
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f153,f96,f158])).

fof(f153,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_2 ),
    inference(resolution,[],[f69,f98])).

fof(f131,plain,
    ( ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f45,f128,f124,f120])).

fof(f45,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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

fof(f118,plain,
    ( spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f46,f115,f111])).

fof(f46,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f22])).

fof(f109,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f47,f106])).

fof(f47,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f104,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f48,f101])).

fof(f48,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f99,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f49,f96])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f94,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f50,f91])).

fof(f50,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:15:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (17096)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.48  % (17081)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.51  % (17075)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (17077)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (17080)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (17078)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (17082)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (17076)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (17085)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (17095)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (17087)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (17073)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (17091)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.33/0.54  % (17089)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.33/0.54  % (17100)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.33/0.54  % (17083)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.33/0.54  % (17074)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.33/0.54  % (17079)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.33/0.54  % (17099)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.33/0.54  % (17093)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.33/0.55  % (17084)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.33/0.55  % (17090)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.33/0.55  % (17088)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.33/0.55  % (17092)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.33/0.55  % (17102)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.33/0.55  % (17097)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.33/0.55  % (17098)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.33/0.56  % (17094)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.33/0.56  % (17086)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.33/0.56  % (17101)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 2.38/0.71  % (17089)Refutation found. Thanks to Tanya!
% 2.38/0.71  % SZS status Theorem for theBenchmark
% 2.38/0.71  % SZS output start Proof for theBenchmark
% 2.38/0.72  fof(f3915,plain,(
% 2.38/0.72    $false),
% 2.38/0.72    inference(avatar_sat_refutation,[],[f94,f99,f104,f109,f118,f131,f161,f217,f233,f239,f257,f379,f449,f524,f536,f542,f543,f544,f558,f583,f615,f674,f946,f949,f957,f1020,f1034,f3866,f3872,f3890,f3891,f3914])).
% 2.38/0.72  fof(f3914,plain,(
% 2.38/0.72    sK3 != k7_relat_1(sK3,sK0) | k1_xboole_0 != sK2 | k1_xboole_0 != sK0 | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~v1_funct_2(sK3,sK0,sK1)),
% 2.38/0.72    introduced(theory_tautology_sat_conflict,[])).
% 2.38/0.72  fof(f3891,plain,(
% 2.38/0.72    spl5_213 | ~spl5_214 | spl5_6 | ~spl5_61),
% 2.38/0.72    inference(avatar_split_clause,[],[f3879,f612,f115,f3887,f3869])).
% 2.38/0.72  fof(f3869,plain,(
% 2.38/0.72    spl5_213 <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)),
% 2.38/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_213])])).
% 2.38/0.72  fof(f3887,plain,(
% 2.38/0.72    spl5_214 <=> sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))),
% 2.38/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_214])])).
% 2.38/0.72  fof(f115,plain,(
% 2.38/0.72    spl5_6 <=> k1_xboole_0 = sK1),
% 2.38/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 2.38/0.72  fof(f612,plain,(
% 2.38/0.72    spl5_61 <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.38/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).
% 2.38/0.72  fof(f3879,plain,(
% 2.38/0.72    k1_xboole_0 = sK1 | sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~spl5_61),
% 2.38/0.72    inference(resolution,[],[f613,f77])).
% 2.38/0.72  fof(f77,plain,(
% 2.38/0.72    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 2.38/0.72    inference(cnf_transformation,[],[f38])).
% 2.38/0.72  fof(f38,plain,(
% 2.38/0.72    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.38/0.72    inference(flattening,[],[f37])).
% 2.38/0.72  fof(f37,plain,(
% 2.38/0.72    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.38/0.72    inference(ennf_transformation,[],[f16])).
% 2.38/0.72  fof(f16,axiom,(
% 2.38/0.72    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.38/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 2.38/0.72  fof(f613,plain,(
% 2.38/0.72    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl5_61),
% 2.38/0.72    inference(avatar_component_clause,[],[f612])).
% 2.38/0.72  fof(f3890,plain,(
% 2.38/0.72    spl5_214 | ~spl5_61 | ~spl5_72),
% 2.38/0.72    inference(avatar_split_clause,[],[f3885,f943,f612,f3887])).
% 2.38/0.72  fof(f943,plain,(
% 2.38/0.72    spl5_72 <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2))),
% 2.38/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).
% 2.38/0.72  fof(f3885,plain,(
% 2.38/0.72    sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | (~spl5_61 | ~spl5_72)),
% 2.38/0.72    inference(forward_demodulation,[],[f3876,f945])).
% 2.38/0.72  fof(f945,plain,(
% 2.38/0.72    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl5_72),
% 2.38/0.72    inference(avatar_component_clause,[],[f943])).
% 2.38/0.72  fof(f3876,plain,(
% 2.38/0.72    k1_relat_1(k7_relat_1(sK3,sK2)) = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | ~spl5_61),
% 2.38/0.72    inference(resolution,[],[f613,f70])).
% 2.38/0.72  fof(f70,plain,(
% 2.38/0.72    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 2.38/0.72    inference(cnf_transformation,[],[f35])).
% 2.38/0.72  fof(f35,plain,(
% 2.38/0.72    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.38/0.72    inference(ennf_transformation,[],[f14])).
% 2.38/0.72  fof(f14,axiom,(
% 2.38/0.72    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.38/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.38/0.72  fof(f3872,plain,(
% 2.38/0.72    ~spl5_213 | spl5_8 | ~spl5_36),
% 2.38/0.72    inference(avatar_split_clause,[],[f3867,f414,f124,f3869])).
% 2.38/0.72  fof(f124,plain,(
% 2.38/0.72    spl5_8 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 2.38/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 2.38/0.72  fof(f414,plain,(
% 2.38/0.72    spl5_36 <=> ! [X6] : k2_partfun1(sK0,sK1,sK3,X6) = k7_relat_1(sK3,X6)),
% 2.38/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 2.38/0.72  fof(f3867,plain,(
% 2.38/0.72    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | (spl5_8 | ~spl5_36)),
% 2.38/0.72    inference(forward_demodulation,[],[f126,f415])).
% 2.38/0.72  fof(f415,plain,(
% 2.38/0.72    ( ! [X6] : (k2_partfun1(sK0,sK1,sK3,X6) = k7_relat_1(sK3,X6)) ) | ~spl5_36),
% 2.38/0.72    inference(avatar_component_clause,[],[f414])).
% 2.38/0.72  fof(f126,plain,(
% 2.38/0.72    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl5_8),
% 2.38/0.72    inference(avatar_component_clause,[],[f124])).
% 2.38/0.72  fof(f3866,plain,(
% 2.38/0.72    spl5_61 | ~spl5_12 | ~spl5_21 | ~spl5_81),
% 2.38/0.72    inference(avatar_split_clause,[],[f3859,f1018,f236,f158,f612])).
% 2.38/0.72  fof(f158,plain,(
% 2.38/0.72    spl5_12 <=> v1_relat_1(sK3)),
% 2.38/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 2.38/0.72  fof(f236,plain,(
% 2.38/0.72    spl5_21 <=> r1_tarski(k2_relat_1(sK3),sK1)),
% 2.38/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 2.38/0.72  fof(f1018,plain,(
% 2.38/0.72    spl5_81 <=> ! [X1,X0] : (~r1_tarski(sK2,X0) | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1))),
% 2.38/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).
% 2.38/0.72  fof(f3859,plain,(
% 2.38/0.72    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl5_12 | ~spl5_21 | ~spl5_81)),
% 2.38/0.72    inference(resolution,[],[f2432,f1333])).
% 2.38/0.72  fof(f1333,plain,(
% 2.38/0.72    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)) ) | (~spl5_12 | ~spl5_21)),
% 2.38/0.72    inference(resolution,[],[f436,f238])).
% 2.38/0.72  fof(f238,plain,(
% 2.38/0.72    r1_tarski(k2_relat_1(sK3),sK1) | ~spl5_21),
% 2.38/0.72    inference(avatar_component_clause,[],[f236])).
% 2.38/0.72  fof(f436,plain,(
% 2.38/0.72    ( ! [X2,X1] : (~r1_tarski(k2_relat_1(sK3),X1) | r1_tarski(k2_relat_1(k7_relat_1(sK3,X2)),X1)) ) | ~spl5_12),
% 2.38/0.72    inference(resolution,[],[f167,f79])).
% 2.38/0.72  fof(f79,plain,(
% 2.38/0.72    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 2.38/0.72    inference(cnf_transformation,[],[f40])).
% 2.38/0.72  fof(f40,plain,(
% 2.38/0.72    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.38/0.72    inference(flattening,[],[f39])).
% 2.38/0.72  fof(f39,plain,(
% 2.38/0.72    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.38/0.72    inference(ennf_transformation,[],[f2])).
% 2.38/0.72  fof(f2,axiom,(
% 2.38/0.72    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.38/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.38/0.72  fof(f167,plain,(
% 2.38/0.72    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),k2_relat_1(sK3))) ) | ~spl5_12),
% 2.38/0.72    inference(resolution,[],[f53,f160])).
% 2.38/0.72  fof(f160,plain,(
% 2.38/0.72    v1_relat_1(sK3) | ~spl5_12),
% 2.38/0.72    inference(avatar_component_clause,[],[f158])).
% 2.38/0.72  fof(f53,plain,(
% 2.38/0.72    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))) )),
% 2.38/0.72    inference(cnf_transformation,[],[f24])).
% 2.38/0.72  fof(f24,plain,(
% 2.38/0.72    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.38/0.72    inference(ennf_transformation,[],[f11])).
% 2.38/0.72  fof(f11,axiom,(
% 2.38/0.72    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 2.38/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).
% 2.38/0.72  fof(f2432,plain,(
% 2.38/0.72    ( ! [X1] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))) ) | ~spl5_81),
% 2.38/0.72    inference(resolution,[],[f1019,f150])).
% 2.38/0.72  fof(f150,plain,(
% 2.38/0.72    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 2.38/0.72    inference(duplicate_literal_removal,[],[f149])).
% 2.38/0.72  fof(f149,plain,(
% 2.38/0.72    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 2.38/0.72    inference(resolution,[],[f62,f61])).
% 2.38/0.72  fof(f61,plain,(
% 2.38/0.72    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.38/0.72    inference(cnf_transformation,[],[f31])).
% 2.38/0.72  fof(f31,plain,(
% 2.38/0.72    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.38/0.72    inference(ennf_transformation,[],[f1])).
% 2.38/0.72  fof(f1,axiom,(
% 2.38/0.72    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.38/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.38/0.72  fof(f62,plain,(
% 2.38/0.72    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.38/0.72    inference(cnf_transformation,[],[f31])).
% 2.38/0.72  fof(f1019,plain,(
% 2.38/0.72    ( ! [X0,X1] : (~r1_tarski(sK2,X0) | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1)) ) | ~spl5_81),
% 2.38/0.72    inference(avatar_component_clause,[],[f1018])).
% 2.38/0.72  fof(f1034,plain,(
% 2.38/0.72    ~spl5_36 | ~spl5_37 | spl5_80),
% 2.38/0.72    inference(avatar_contradiction_clause,[],[f1033])).
% 2.38/0.72  fof(f1033,plain,(
% 2.38/0.72    $false | (~spl5_36 | ~spl5_37 | spl5_80)),
% 2.38/0.72    inference(resolution,[],[f1016,f623])).
% 2.38/0.72  fof(f623,plain,(
% 2.38/0.72    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0))) ) | (~spl5_36 | ~spl5_37)),
% 2.38/0.72    inference(resolution,[],[f618,f69])).
% 2.38/0.72  fof(f69,plain,(
% 2.38/0.72    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.38/0.72    inference(cnf_transformation,[],[f34])).
% 2.38/0.72  fof(f34,plain,(
% 2.38/0.72    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.38/0.72    inference(ennf_transformation,[],[f12])).
% 2.38/0.72  fof(f12,axiom,(
% 2.38/0.72    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.38/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.38/0.72  fof(f618,plain,(
% 2.38/0.72    ( ! [X6] : (m1_subset_1(k7_relat_1(sK3,X6),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | (~spl5_36 | ~spl5_37)),
% 2.38/0.72    inference(forward_demodulation,[],[f424,f415])).
% 2.38/0.72  fof(f424,plain,(
% 2.38/0.72    ( ! [X6] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X6),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | ~spl5_37),
% 2.38/0.72    inference(avatar_component_clause,[],[f423])).
% 2.38/0.72  fof(f423,plain,(
% 2.38/0.72    spl5_37 <=> ! [X6] : m1_subset_1(k2_partfun1(sK0,sK1,sK3,X6),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.38/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 2.38/0.72  fof(f1016,plain,(
% 2.38/0.72    ~v1_relat_1(k7_relat_1(sK3,sK2)) | spl5_80),
% 2.38/0.72    inference(avatar_component_clause,[],[f1014])).
% 2.38/0.72  fof(f1014,plain,(
% 2.38/0.72    spl5_80 <=> v1_relat_1(k7_relat_1(sK3,sK2))),
% 2.38/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).
% 2.38/0.72  fof(f1020,plain,(
% 2.38/0.72    ~spl5_80 | spl5_81 | ~spl5_72),
% 2.38/0.72    inference(avatar_split_clause,[],[f1009,f943,f1018,f1014])).
% 2.38/0.72  fof(f1009,plain,(
% 2.38/0.72    ( ! [X0,X1] : (~r1_tarski(sK2,X0) | ~v1_relat_1(k7_relat_1(sK3,sK2)) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl5_72),
% 2.38/0.72    inference(superposition,[],[f68,f945])).
% 2.38/0.72  fof(f68,plain,(
% 2.38/0.72    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.38/0.72    inference(cnf_transformation,[],[f33])).
% 2.38/0.72  fof(f33,plain,(
% 2.38/0.72    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 2.38/0.72    inference(flattening,[],[f32])).
% 2.38/0.72  fof(f32,plain,(
% 2.38/0.72    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 2.38/0.72    inference(ennf_transformation,[],[f15])).
% 2.38/0.72  fof(f15,axiom,(
% 2.38/0.72    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.38/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 2.38/0.72  fof(f957,plain,(
% 2.38/0.72    spl5_67 | ~spl5_39),
% 2.38/0.72    inference(avatar_split_clause,[],[f685,f464,f689])).
% 2.38/0.72  fof(f689,plain,(
% 2.38/0.72    spl5_67 <=> k1_xboole_0 = sK2),
% 2.38/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).
% 2.38/0.72  fof(f464,plain,(
% 2.38/0.72    spl5_39 <=> r1_tarski(sK2,k1_xboole_0)),
% 2.38/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 2.38/0.72  fof(f685,plain,(
% 2.38/0.72    k1_xboole_0 = sK2 | ~spl5_39),
% 2.38/0.72    inference(resolution,[],[f466,f52])).
% 2.38/0.72  fof(f52,plain,(
% 2.38/0.72    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.38/0.72    inference(cnf_transformation,[],[f23])).
% 2.38/0.72  fof(f23,plain,(
% 2.38/0.72    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.38/0.72    inference(ennf_transformation,[],[f4])).
% 2.38/0.72  fof(f4,axiom,(
% 2.38/0.72    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.38/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 2.38/0.72  fof(f466,plain,(
% 2.38/0.72    r1_tarski(sK2,k1_xboole_0) | ~spl5_39),
% 2.38/0.72    inference(avatar_component_clause,[],[f464])).
% 2.38/0.72  fof(f949,plain,(
% 2.38/0.72    sK3 != k7_relat_1(sK3,sK0) | k1_xboole_0 != k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) | k1_xboole_0 != sK0 | sK0 = k1_relat_1(sK3)),
% 2.38/0.72    introduced(theory_tautology_sat_conflict,[])).
% 2.38/0.72  fof(f946,plain,(
% 2.38/0.72    spl5_72 | ~spl5_1 | ~spl5_52),
% 2.38/0.72    inference(avatar_split_clause,[],[f940,f556,f91,f943])).
% 2.38/0.72  fof(f91,plain,(
% 2.38/0.72    spl5_1 <=> r1_tarski(sK2,sK0)),
% 2.38/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.38/0.72  fof(f556,plain,(
% 2.38/0.72    spl5_52 <=> ! [X2] : (~r1_tarski(X2,sK0) | k1_relat_1(k7_relat_1(sK3,X2)) = X2)),
% 2.38/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 2.38/0.72  fof(f940,plain,(
% 2.38/0.72    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | (~spl5_1 | ~spl5_52)),
% 2.38/0.72    inference(resolution,[],[f557,f93])).
% 2.38/0.72  fof(f93,plain,(
% 2.38/0.72    r1_tarski(sK2,sK0) | ~spl5_1),
% 2.38/0.72    inference(avatar_component_clause,[],[f91])).
% 2.38/0.72  fof(f557,plain,(
% 2.38/0.72    ( ! [X2] : (~r1_tarski(X2,sK0) | k1_relat_1(k7_relat_1(sK3,X2)) = X2) ) | ~spl5_52),
% 2.38/0.72    inference(avatar_component_clause,[],[f556])).
% 2.38/0.72  fof(f674,plain,(
% 2.38/0.72    spl5_39 | ~spl5_1 | ~spl5_5),
% 2.38/0.72    inference(avatar_split_clause,[],[f450,f111,f91,f464])).
% 2.38/0.72  fof(f111,plain,(
% 2.38/0.72    spl5_5 <=> k1_xboole_0 = sK0),
% 2.38/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.38/0.72  fof(f450,plain,(
% 2.38/0.72    r1_tarski(sK2,k1_xboole_0) | (~spl5_1 | ~spl5_5)),
% 2.38/0.72    inference(backward_demodulation,[],[f93,f113])).
% 2.38/0.72  fof(f113,plain,(
% 2.38/0.72    k1_xboole_0 = sK0 | ~spl5_5),
% 2.38/0.72    inference(avatar_component_clause,[],[f111])).
% 2.38/0.72  fof(f615,plain,(
% 2.38/0.72    ~spl5_61 | spl5_7 | ~spl5_36),
% 2.38/0.72    inference(avatar_split_clause,[],[f609,f414,f120,f612])).
% 2.38/0.72  fof(f120,plain,(
% 2.38/0.72    spl5_7 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.38/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.38/0.72  fof(f609,plain,(
% 2.38/0.72    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (spl5_7 | ~spl5_36)),
% 2.38/0.72    inference(backward_demodulation,[],[f122,f415])).
% 2.38/0.72  fof(f122,plain,(
% 2.38/0.72    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl5_7),
% 2.38/0.72    inference(avatar_component_clause,[],[f120])).
% 2.38/0.72  fof(f583,plain,(
% 2.38/0.72    spl5_55 | ~spl5_12),
% 2.38/0.72    inference(avatar_split_clause,[],[f576,f158,f580])).
% 2.38/0.72  fof(f580,plain,(
% 2.38/0.72    spl5_55 <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_xboole_0))),
% 2.38/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).
% 2.38/0.72  fof(f576,plain,(
% 2.38/0.72    k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) | ~spl5_12),
% 2.38/0.72    inference(resolution,[],[f274,f160])).
% 2.38/0.72  fof(f274,plain,(
% 2.38/0.72    ( ! [X1] : (~v1_relat_1(X1) | k1_xboole_0 = k1_relat_1(k7_relat_1(X1,k1_xboole_0))) )),
% 2.38/0.72    inference(resolution,[],[f54,f51])).
% 2.38/0.72  fof(f51,plain,(
% 2.38/0.72    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.38/0.72    inference(cnf_transformation,[],[f3])).
% 2.38/0.72  fof(f3,axiom,(
% 2.38/0.72    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.38/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.38/0.72  fof(f54,plain,(
% 2.38/0.72    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 2.38/0.72    inference(cnf_transformation,[],[f26])).
% 2.38/0.72  fof(f26,plain,(
% 2.38/0.72    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.38/0.72    inference(flattening,[],[f25])).
% 2.38/0.72  fof(f25,plain,(
% 2.38/0.72    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.38/0.72    inference(ennf_transformation,[],[f9])).
% 2.38/0.72  fof(f9,axiom,(
% 2.38/0.72    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 2.38/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 2.38/0.72  fof(f558,plain,(
% 2.38/0.72    ~spl5_12 | spl5_52 | ~spl5_38),
% 2.38/0.72    inference(avatar_split_clause,[],[f548,f446,f556,f158])).
% 2.38/0.72  fof(f446,plain,(
% 2.38/0.72    spl5_38 <=> sK0 = k1_relat_1(sK3)),
% 2.38/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 2.38/0.72  fof(f548,plain,(
% 2.38/0.72    ( ! [X2] : (~r1_tarski(X2,sK0) | ~v1_relat_1(sK3) | k1_relat_1(k7_relat_1(sK3,X2)) = X2) ) | ~spl5_38),
% 2.38/0.72    inference(superposition,[],[f54,f448])).
% 2.38/0.72  fof(f448,plain,(
% 2.38/0.72    sK0 = k1_relat_1(sK3) | ~spl5_38),
% 2.38/0.72    inference(avatar_component_clause,[],[f446])).
% 2.38/0.72  fof(f544,plain,(
% 2.38/0.72    spl5_37 | ~spl5_4 | ~spl5_2),
% 2.38/0.72    inference(avatar_split_clause,[],[f534,f96,f106,f423])).
% 2.38/0.72  fof(f106,plain,(
% 2.38/0.72    spl5_4 <=> v1_funct_1(sK3)),
% 2.38/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.38/0.72  fof(f96,plain,(
% 2.38/0.72    spl5_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.38/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.38/0.72  fof(f534,plain,(
% 2.38/0.72    ( ! [X2] : (~v1_funct_1(sK3) | m1_subset_1(k2_partfun1(sK0,sK1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | ~spl5_2),
% 2.38/0.72    inference(resolution,[],[f98,f82])).
% 2.38/0.72  fof(f82,plain,(
% 2.38/0.72    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.38/0.72    inference(cnf_transformation,[],[f44])).
% 2.38/0.72  fof(f44,plain,(
% 2.38/0.72    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.38/0.72    inference(flattening,[],[f43])).
% 2.38/0.72  fof(f43,plain,(
% 2.38/0.72    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.38/0.72    inference(ennf_transformation,[],[f17])).
% 2.38/0.72  fof(f17,axiom,(
% 2.38/0.72    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 2.38/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 2.38/0.72  fof(f98,plain,(
% 2.38/0.72    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_2),
% 2.38/0.72    inference(avatar_component_clause,[],[f96])).
% 2.38/0.72  fof(f543,plain,(
% 2.38/0.72    spl5_34 | ~spl5_4 | ~spl5_2),
% 2.38/0.72    inference(avatar_split_clause,[],[f533,f96,f106,f349])).
% 2.38/0.72  fof(f349,plain,(
% 2.38/0.72    spl5_34 <=> ! [X6] : v1_funct_1(k2_partfun1(sK0,sK1,sK3,X6))),
% 2.38/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 2.38/0.72  fof(f533,plain,(
% 2.38/0.72    ( ! [X1] : (~v1_funct_1(sK3) | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X1))) ) | ~spl5_2),
% 2.38/0.72    inference(resolution,[],[f98,f81])).
% 2.38/0.72  fof(f81,plain,(
% 2.38/0.72    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | v1_funct_1(k2_partfun1(X0,X1,X2,X3))) )),
% 2.38/0.72    inference(cnf_transformation,[],[f44])).
% 2.38/0.72  fof(f542,plain,(
% 2.38/0.72    spl5_36 | ~spl5_4 | ~spl5_2),
% 2.38/0.72    inference(avatar_split_clause,[],[f532,f96,f106,f414])).
% 2.38/0.72  fof(f532,plain,(
% 2.38/0.72    ( ! [X0] : (~v1_funct_1(sK3) | k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)) ) | ~spl5_2),
% 2.38/0.72    inference(resolution,[],[f98,f80])).
% 2.38/0.72  fof(f80,plain,(
% 2.38/0.72    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 2.38/0.72    inference(cnf_transformation,[],[f42])).
% 2.38/0.72  fof(f42,plain,(
% 2.38/0.72    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.38/0.72    inference(flattening,[],[f41])).
% 2.38/0.72  fof(f41,plain,(
% 2.38/0.72    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.38/0.72    inference(ennf_transformation,[],[f18])).
% 2.38/0.72  fof(f18,axiom,(
% 2.38/0.72    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 2.38/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 2.38/0.72  fof(f536,plain,(
% 2.38/0.72    spl5_27 | ~spl5_2),
% 2.38/0.72    inference(avatar_split_clause,[],[f527,f96,f303])).
% 2.38/0.72  fof(f303,plain,(
% 2.38/0.72    spl5_27 <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 2.38/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 2.38/0.72  fof(f527,plain,(
% 2.38/0.72    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl5_2),
% 2.38/0.72    inference(resolution,[],[f98,f70])).
% 2.38/0.72  fof(f524,plain,(
% 2.38/0.72    ~spl5_12 | spl5_19 | ~spl5_18),
% 2.38/0.72    inference(avatar_split_clause,[],[f523,f214,f220,f158])).
% 2.38/0.72  fof(f220,plain,(
% 2.38/0.72    spl5_19 <=> r1_tarski(k1_relat_1(sK3),sK0)),
% 2.38/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 2.38/0.72  fof(f214,plain,(
% 2.38/0.72    spl5_18 <=> v4_relat_1(sK3,sK0)),
% 2.38/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 2.38/0.72  fof(f523,plain,(
% 2.38/0.72    r1_tarski(k1_relat_1(sK3),sK0) | ~v1_relat_1(sK3) | ~spl5_18),
% 2.38/0.72    inference(resolution,[],[f216,f59])).
% 2.38/0.72  fof(f59,plain,(
% 2.38/0.72    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.38/0.72    inference(cnf_transformation,[],[f30])).
% 2.38/0.72  fof(f30,plain,(
% 2.38/0.72    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.38/0.72    inference(ennf_transformation,[],[f7])).
% 2.38/0.72  fof(f7,axiom,(
% 2.38/0.72    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.38/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 2.38/0.72  fof(f216,plain,(
% 2.38/0.72    v4_relat_1(sK3,sK0) | ~spl5_18),
% 2.38/0.72    inference(avatar_component_clause,[],[f214])).
% 2.38/0.72  fof(f449,plain,(
% 2.38/0.72    ~spl5_3 | spl5_6 | spl5_38 | ~spl5_2 | ~spl5_27),
% 2.38/0.72    inference(avatar_split_clause,[],[f444,f303,f96,f446,f115,f101])).
% 2.38/0.72  fof(f101,plain,(
% 2.38/0.72    spl5_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 2.38/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.38/0.72  fof(f444,plain,(
% 2.38/0.72    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1 | ~v1_funct_2(sK3,sK0,sK1) | (~spl5_2 | ~spl5_27)),
% 2.38/0.72    inference(forward_demodulation,[],[f441,f305])).
% 2.38/0.72  fof(f305,plain,(
% 2.38/0.72    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl5_27),
% 2.38/0.72    inference(avatar_component_clause,[],[f303])).
% 2.38/0.72  fof(f441,plain,(
% 2.38/0.72    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl5_2),
% 2.38/0.72    inference(resolution,[],[f78,f98])).
% 2.38/0.72  fof(f78,plain,(
% 2.38/0.72    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 2.38/0.72    inference(cnf_transformation,[],[f38])).
% 2.38/0.72  fof(f379,plain,(
% 2.38/0.72    spl5_9 | ~spl5_34),
% 2.38/0.72    inference(avatar_contradiction_clause,[],[f378])).
% 2.38/0.72  fof(f378,plain,(
% 2.38/0.72    $false | (spl5_9 | ~spl5_34)),
% 2.38/0.72    inference(resolution,[],[f350,f130])).
% 2.38/0.72  fof(f130,plain,(
% 2.38/0.72    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl5_9),
% 2.38/0.72    inference(avatar_component_clause,[],[f128])).
% 2.38/0.72  fof(f128,plain,(
% 2.38/0.72    spl5_9 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 2.38/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 2.38/0.72  fof(f350,plain,(
% 2.38/0.72    ( ! [X6] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X6))) ) | ~spl5_34),
% 2.38/0.72    inference(avatar_component_clause,[],[f349])).
% 2.38/0.72  fof(f257,plain,(
% 2.38/0.72    spl5_22 | ~spl5_12 | ~spl5_19),
% 2.38/0.72    inference(avatar_split_clause,[],[f249,f220,f158,f254])).
% 2.38/0.72  fof(f254,plain,(
% 2.38/0.72    spl5_22 <=> sK3 = k7_relat_1(sK3,sK0)),
% 2.38/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 2.38/0.72  fof(f249,plain,(
% 2.38/0.72    ~v1_relat_1(sK3) | sK3 = k7_relat_1(sK3,sK0) | ~spl5_19),
% 2.38/0.72    inference(resolution,[],[f222,f55])).
% 2.38/0.72  fof(f55,plain,(
% 2.38/0.72    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 2.38/0.72    inference(cnf_transformation,[],[f28])).
% 2.38/0.72  fof(f28,plain,(
% 2.38/0.72    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.38/0.72    inference(flattening,[],[f27])).
% 2.38/0.72  fof(f27,plain,(
% 2.38/0.72    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.38/0.72    inference(ennf_transformation,[],[f10])).
% 2.38/0.72  fof(f10,axiom,(
% 2.38/0.72    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 2.38/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 2.38/0.72  fof(f222,plain,(
% 2.38/0.72    r1_tarski(k1_relat_1(sK3),sK0) | ~spl5_19),
% 2.38/0.72    inference(avatar_component_clause,[],[f220])).
% 2.38/0.72  fof(f239,plain,(
% 2.38/0.72    ~spl5_12 | spl5_21 | ~spl5_20),
% 2.38/0.72    inference(avatar_split_clause,[],[f234,f230,f236,f158])).
% 2.38/0.72  fof(f230,plain,(
% 2.38/0.72    spl5_20 <=> v5_relat_1(sK3,sK1)),
% 2.38/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 2.38/0.72  fof(f234,plain,(
% 2.38/0.72    r1_tarski(k2_relat_1(sK3),sK1) | ~v1_relat_1(sK3) | ~spl5_20),
% 2.38/0.72    inference(resolution,[],[f232,f57])).
% 2.38/0.72  fof(f57,plain,(
% 2.38/0.72    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.38/0.72    inference(cnf_transformation,[],[f29])).
% 2.38/0.72  fof(f29,plain,(
% 2.38/0.72    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.38/0.72    inference(ennf_transformation,[],[f8])).
% 2.38/0.72  fof(f8,axiom,(
% 2.38/0.72    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.38/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 2.38/0.72  fof(f232,plain,(
% 2.38/0.72    v5_relat_1(sK3,sK1) | ~spl5_20),
% 2.38/0.72    inference(avatar_component_clause,[],[f230])).
% 2.38/0.72  fof(f233,plain,(
% 2.38/0.72    spl5_20 | ~spl5_2),
% 2.38/0.72    inference(avatar_split_clause,[],[f226,f96,f230])).
% 2.38/0.72  fof(f226,plain,(
% 2.38/0.72    v5_relat_1(sK3,sK1) | ~spl5_2),
% 2.38/0.72    inference(resolution,[],[f72,f98])).
% 2.38/0.72  fof(f72,plain,(
% 2.38/0.72    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.38/0.72    inference(cnf_transformation,[],[f36])).
% 2.38/0.72  fof(f36,plain,(
% 2.38/0.72    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.38/0.72    inference(ennf_transformation,[],[f13])).
% 2.38/0.72  fof(f13,axiom,(
% 2.38/0.72    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.38/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.38/0.72  fof(f217,plain,(
% 2.38/0.72    spl5_18 | ~spl5_2),
% 2.38/0.72    inference(avatar_split_clause,[],[f210,f96,f214])).
% 2.38/0.72  fof(f210,plain,(
% 2.38/0.72    v4_relat_1(sK3,sK0) | ~spl5_2),
% 2.38/0.72    inference(resolution,[],[f71,f98])).
% 2.38/0.72  fof(f71,plain,(
% 2.38/0.72    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.38/0.72    inference(cnf_transformation,[],[f36])).
% 2.38/0.72  fof(f161,plain,(
% 2.38/0.72    spl5_12 | ~spl5_2),
% 2.38/0.72    inference(avatar_split_clause,[],[f153,f96,f158])).
% 2.38/0.72  fof(f153,plain,(
% 2.38/0.72    v1_relat_1(sK3) | ~spl5_2),
% 2.38/0.72    inference(resolution,[],[f69,f98])).
% 2.38/0.72  fof(f131,plain,(
% 2.38/0.72    ~spl5_7 | ~spl5_8 | ~spl5_9),
% 2.38/0.72    inference(avatar_split_clause,[],[f45,f128,f124,f120])).
% 2.38/0.72  fof(f45,plain,(
% 2.38/0.72    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.38/0.72    inference(cnf_transformation,[],[f22])).
% 2.38/0.72  fof(f22,plain,(
% 2.38/0.72    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.38/0.72    inference(flattening,[],[f21])).
% 2.38/0.72  fof(f21,plain,(
% 2.38/0.72    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.38/0.72    inference(ennf_transformation,[],[f20])).
% 2.38/0.72  fof(f20,negated_conjecture,(
% 2.38/0.72    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.38/0.72    inference(negated_conjecture,[],[f19])).
% 2.38/0.72  fof(f19,conjecture,(
% 2.38/0.72    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.38/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).
% 2.38/0.72  fof(f118,plain,(
% 2.38/0.72    spl5_5 | ~spl5_6),
% 2.38/0.72    inference(avatar_split_clause,[],[f46,f115,f111])).
% 2.38/0.72  fof(f46,plain,(
% 2.38/0.72    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 2.38/0.72    inference(cnf_transformation,[],[f22])).
% 2.38/0.72  fof(f109,plain,(
% 2.38/0.72    spl5_4),
% 2.38/0.72    inference(avatar_split_clause,[],[f47,f106])).
% 2.38/0.72  fof(f47,plain,(
% 2.38/0.72    v1_funct_1(sK3)),
% 2.38/0.72    inference(cnf_transformation,[],[f22])).
% 2.38/0.72  fof(f104,plain,(
% 2.38/0.72    spl5_3),
% 2.38/0.72    inference(avatar_split_clause,[],[f48,f101])).
% 2.38/0.72  fof(f48,plain,(
% 2.38/0.72    v1_funct_2(sK3,sK0,sK1)),
% 2.38/0.72    inference(cnf_transformation,[],[f22])).
% 2.38/0.72  fof(f99,plain,(
% 2.38/0.72    spl5_2),
% 2.38/0.72    inference(avatar_split_clause,[],[f49,f96])).
% 2.38/0.72  fof(f49,plain,(
% 2.38/0.72    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.38/0.72    inference(cnf_transformation,[],[f22])).
% 2.38/0.72  fof(f94,plain,(
% 2.38/0.72    spl5_1),
% 2.38/0.72    inference(avatar_split_clause,[],[f50,f91])).
% 2.38/0.72  fof(f50,plain,(
% 2.38/0.72    r1_tarski(sK2,sK0)),
% 2.38/0.72    inference(cnf_transformation,[],[f22])).
% 2.38/0.72  % SZS output end Proof for theBenchmark
% 2.38/0.72  % (17089)------------------------------
% 2.38/0.72  % (17089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.38/0.72  % (17089)Termination reason: Refutation
% 2.38/0.72  
% 2.38/0.72  % (17089)Memory used [KB]: 13176
% 2.38/0.72  % (17089)Time elapsed: 0.301 s
% 2.38/0.72  % (17089)------------------------------
% 2.38/0.72  % (17089)------------------------------
% 2.38/0.72  % (17072)Success in time 0.358 s
%------------------------------------------------------------------------------
