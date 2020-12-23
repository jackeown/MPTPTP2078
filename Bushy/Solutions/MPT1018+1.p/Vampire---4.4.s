%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t85_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:50 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 345 expanded)
%              Number of leaves         :   39 ( 130 expanded)
%              Depth                    :   14
%              Number of atoms          :  441 (1044 expanded)
%              Number of equality atoms :   37 ( 106 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f515,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f71,f78,f85,f92,f99,f106,f113,f122,f123,f132,f133,f142,f149,f158,f165,f182,f203,f215,f228,f241,f248,f255,f268,f284,f293,f514])).

fof(f514,plain,
    ( ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | spl8_9
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_14 ),
    inference(avatar_contradiction_clause,[],[f513])).

fof(f513,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f512,f112])).

fof(f112,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl8_14
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f512,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f511,f105])).

fof(f105,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl8_12
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f511,plain,
    ( ~ r2_hidden(sK3,sK0)
    | ~ r2_hidden(sK2,sK0)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f510,f77])).

fof(f77,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl8_4
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f510,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ r2_hidden(sK3,sK0)
    | ~ r2_hidden(sK2,sK0)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(resolution,[],[f509,f70])).

fof(f70,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl8_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f509,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v1_funct_2(sK1,X0,X0)
        | ~ r2_hidden(sK3,X0)
        | ~ r2_hidden(sK2,X0) )
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f508,f91])).

fof(f91,plain,
    ( sK2 != sK3
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl8_9
  <=> sK2 != sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f508,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK1,X0,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ r2_hidden(sK3,X0)
        | ~ r2_hidden(sK2,X0)
        | sK2 = sK3 )
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_10 ),
    inference(equality_resolution,[],[f504])).

fof(f504,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
        | ~ v1_funct_2(sK1,X1,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
        | ~ r2_hidden(sK3,X1)
        | ~ r2_hidden(X0,X1)
        | sK3 = X0 )
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f503,f63])).

fof(f63,plain,
    ( v2_funct_1(sK1)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl8_0
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f503,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
        | ~ v1_funct_2(sK1,X1,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
        | ~ r2_hidden(sK3,X1)
        | ~ r2_hidden(X0,X1)
        | sK3 = X0
        | ~ v2_funct_1(sK1) )
    | ~ spl8_6
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f499,f84])).

fof(f84,plain,
    ( v1_funct_1(sK1)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl8_6
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f499,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
        | ~ v1_funct_2(sK1,X1,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
        | ~ r2_hidden(sK3,X1)
        | ~ r2_hidden(X0,X1)
        | ~ v1_funct_1(sK1)
        | sK3 = X0
        | ~ v2_funct_1(sK1) )
    | ~ spl8_10 ),
    inference(superposition,[],[f44,f98])).

fof(f98,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl8_10
  <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X0)
      | ~ v1_funct_1(X1)
      | X2 = X3
      | ~ v2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t85_funct_2.p',t77_funct_2)).

fof(f293,plain,
    ( ~ spl8_55
    | ~ spl8_2
    | spl8_35 ),
    inference(avatar_split_clause,[],[f286,f201,f69,f291])).

fof(f291,plain,
    ( spl8_55
  <=> ~ r2_hidden(k2_zfmisc_1(sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).

fof(f201,plain,
    ( spl8_35
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f286,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,sK0),sK1)
    | ~ spl8_2
    | ~ spl8_35 ),
    inference(duplicate_literal_removal,[],[f285])).

fof(f285,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,sK0),sK1)
    | ~ r2_hidden(k2_zfmisc_1(sK0,sK0),sK1)
    | ~ spl8_2
    | ~ spl8_35 ),
    inference(resolution,[],[f271,f270])).

fof(f270,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK0,sK0))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl8_2
    | ~ spl8_35 ),
    inference(subsumption_resolution,[],[f269,f202])).

fof(f202,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK0))
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f201])).

fof(f269,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | v1_xboole_0(k2_zfmisc_1(sK0,sK0))
        | r2_hidden(X0,k2_zfmisc_1(sK0,sK0)) )
    | ~ spl8_2 ),
    inference(resolution,[],[f256,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t85_funct_2.p',t2_subset)).

fof(f256,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(sK0,sK0))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl8_2 ),
    inference(resolution,[],[f53,f70])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t85_funct_2.p',t4_subset)).

fof(f271,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k2_zfmisc_1(sK0,sK0),X0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl8_2
    | ~ spl8_35 ),
    inference(resolution,[],[f270,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t85_funct_2.p',antisymmetry_r2_hidden)).

fof(f284,plain,
    ( ~ spl8_51
    | spl8_52
    | ~ spl8_2
    | spl8_35 ),
    inference(avatar_split_clause,[],[f274,f201,f69,f282,f279])).

fof(f279,plain,
    ( spl8_51
  <=> ~ sP7(k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).

fof(f282,plain,
    ( spl8_52
  <=> ! [X3] : ~ r2_hidden(X3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f274,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | ~ sP7(k2_zfmisc_1(sK0,sK0)) )
    | ~ spl8_2
    | ~ spl8_35 ),
    inference(resolution,[],[f270,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP7(X1) ) ),
    inference(general_splitting,[],[f52,f56_D])).

fof(f56,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP7(X1) ) ),
    inference(cnf_transformation,[],[f56_D])).

fof(f56_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP7(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t85_funct_2.p',t5_subset)).

fof(f268,plain,
    ( ~ spl8_49
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f258,f174,f266])).

fof(f266,plain,
    ( spl8_49
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f174,plain,
    ( spl8_28
  <=> r2_hidden(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f258,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK1)
    | ~ spl8_28 ),
    inference(resolution,[],[f175,f50])).

fof(f175,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f174])).

fof(f255,plain,
    ( spl8_46
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f220,f213,f253])).

fof(f253,plain,
    ( spl8_46
  <=> m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f213,plain,
    ( spl8_36
  <=> k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f220,plain,
    ( m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))
    | ~ spl8_36 ),
    inference(superposition,[],[f51,f214])).

fof(f214,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f213])).

fof(f51,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t85_funct_2.p',existence_m1_subset_1)).

fof(f248,plain,
    ( spl8_40
    | spl8_44
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f219,f213,f246,f233])).

fof(f233,plain,
    ( spl8_40
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f246,plain,
    ( spl8_44
  <=> r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f219,plain,
    ( r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))
    | ~ spl8_36 ),
    inference(superposition,[],[f169,f214])).

fof(f169,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f55,f51])).

fof(f241,plain,
    ( spl8_40
    | ~ spl8_43
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f218,f213,f239,f233])).

fof(f239,plain,
    ( spl8_43
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f218,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))
    | ~ spl8_36 ),
    inference(superposition,[],[f185,f214])).

fof(f185,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK6(X0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f169,f50])).

fof(f228,plain,
    ( spl8_38
    | ~ spl8_30
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f221,f213,f180,f226])).

fof(f226,plain,
    ( spl8_38
  <=> sP7(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f180,plain,
    ( spl8_30
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f221,plain,
    ( sP7(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl8_30
    | ~ spl8_36 ),
    inference(subsumption_resolution,[],[f217,f181])).

fof(f181,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f180])).

fof(f217,plain,
    ( sP7(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl8_36 ),
    inference(superposition,[],[f190,f214])).

fof(f190,plain,(
    ! [X0] :
      ( sP7(sK6(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f56,f51])).

fof(f215,plain,
    ( spl8_36
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f207,f180,f213])).

fof(f207,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))
    | ~ spl8_30 ),
    inference(resolution,[],[f205,f181])).

fof(f205,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = sK6(k1_zfmisc_1(X0)) )
    | ~ spl8_30 ),
    inference(resolution,[],[f204,f183])).

fof(f183,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = X0 )
    | ~ spl8_30 ),
    inference(resolution,[],[f181,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t85_funct_2.p',t8_boole)).

fof(f204,plain,(
    ! [X0] :
      ( v1_xboole_0(sK6(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f190,f188])).

fof(f188,plain,(
    ! [X3] :
      ( ~ sP7(X3)
      | v1_xboole_0(X3) ) ),
    inference(resolution,[],[f169,f57])).

fof(f203,plain,
    ( spl8_32
    | ~ spl8_35
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f189,f69,f201,f195])).

fof(f195,plain,
    ( spl8_32
  <=> sP7(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f189,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK0))
    | sP7(sK1)
    | ~ spl8_2 ),
    inference(resolution,[],[f56,f70])).

fof(f182,plain,
    ( spl8_28
    | spl8_30
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f166,f69,f180,f174])).

fof(f166,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | r2_hidden(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl8_2 ),
    inference(resolution,[],[f55,f70])).

fof(f165,plain,
    ( ~ spl8_27
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f151,f111,f163])).

fof(f163,plain,
    ( spl8_27
  <=> ~ r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f151,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl8_14 ),
    inference(resolution,[],[f50,f112])).

fof(f158,plain,
    ( ~ spl8_25
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f150,f104,f156])).

fof(f156,plain,
    ( spl8_25
  <=> ~ r2_hidden(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f150,plain,
    ( ~ r2_hidden(sK0,sK3)
    | ~ spl8_12 ),
    inference(resolution,[],[f50,f105])).

fof(f149,plain,
    ( spl8_22
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f135,f111,f147])).

fof(f147,plain,
    ( spl8_22
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f135,plain,
    ( m1_subset_1(sK2,sK0)
    | ~ spl8_14 ),
    inference(resolution,[],[f49,f112])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t85_funct_2.p',t1_subset)).

fof(f142,plain,
    ( spl8_20
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f134,f104,f140])).

fof(f140,plain,
    ( spl8_20
  <=> m1_subset_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f134,plain,
    ( m1_subset_1(sK3,sK0)
    | ~ spl8_12 ),
    inference(resolution,[],[f49,f105])).

fof(f133,plain,
    ( ~ spl8_19
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f125,f111,f130])).

fof(f130,plain,
    ( spl8_19
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f125,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl8_14 ),
    inference(resolution,[],[f54,f112])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t85_funct_2.p',t7_boole)).

fof(f132,plain,
    ( ~ spl8_19
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f124,f104,f130])).

fof(f124,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl8_12 ),
    inference(resolution,[],[f54,f105])).

fof(f123,plain,
    ( ~ spl8_17
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f115,f111,f120])).

fof(f120,plain,
    ( spl8_17
  <=> ~ sP7(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f115,plain,
    ( ~ sP7(sK0)
    | ~ spl8_14 ),
    inference(resolution,[],[f57,f112])).

fof(f122,plain,
    ( ~ spl8_17
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f114,f104,f120])).

fof(f114,plain,
    ( ~ sP7(sK0)
    | ~ spl8_12 ),
    inference(resolution,[],[f57,f105])).

fof(f113,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f35,f111])).

fof(f35,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t85_funct_2.p',t85_funct_2)).

fof(f106,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f36,f104])).

fof(f36,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f99,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f37,f97])).

fof(f37,plain,(
    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f92,plain,(
    ~ spl8_9 ),
    inference(avatar_split_clause,[],[f38,f90])).

fof(f38,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f23])).

fof(f85,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f39,f83])).

fof(f39,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f78,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f40,f76])).

fof(f40,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f41,f69])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,(
    spl8_0 ),
    inference(avatar_split_clause,[],[f42,f62])).

fof(f42,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
