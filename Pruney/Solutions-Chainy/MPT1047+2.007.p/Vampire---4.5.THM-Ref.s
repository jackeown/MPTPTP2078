%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:01 EST 2020

% Result     : Theorem 2.18s
% Output     : Refutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 310 expanded)
%              Number of leaves         :   31 ( 110 expanded)
%              Depth                    :   19
%              Number of atoms          :  727 (1355 expanded)
%              Number of equality atoms :  170 ( 292 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1068,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f97,f102,f107,f112,f117,f122,f217,f350,f361,f394,f503,f514,f1066,f1067])).

fof(f1067,plain,
    ( k1_xboole_0 != k5_partfun1(sK0,k1_tarski(sK1),sK2)
    | r2_hidden(sK3,k1_xboole_0)
    | ~ r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1066,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | spl6_14 ),
    inference(avatar_contradiction_clause,[],[f1065])).

fof(f1065,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | spl6_14 ),
    inference(subsumption_resolution,[],[f1064,f91])).

fof(f91,plain,
    ( k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl6_1
  <=> k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f1064,plain,
    ( k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(sK3)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | spl6_14 ),
    inference(equality_resolution,[],[f1061])).

fof(f1061,plain,
    ( ! [X10] :
        ( sK3 != X10
        | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X10) )
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | spl6_14 ),
    inference(subsumption_resolution,[],[f1051,f184])).

fof(f184,plain,
    ( k1_xboole_0 != k5_partfun1(sK0,k1_tarski(sK1),sK2)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl6_10
  <=> k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f1051,plain,
    ( ! [X10] :
        ( sK3 != X10
        | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
        | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X10) )
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | spl6_14 ),
    inference(duplicate_literal_removal,[],[f1048])).

fof(f1048,plain,
    ( ! [X10] :
        ( sK3 != X10
        | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
        | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X10)
        | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X10) )
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | spl6_14 ),
    inference(superposition,[],[f59,f1038])).

fof(f1038,plain,
    ( ! [X1] :
        ( sK3 = sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X1)
        | k1_tarski(X1) = k5_partfun1(sK0,k1_tarski(sK1),sK2) )
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | spl6_14 ),
    inference(subsumption_resolution,[],[f852,f863])).

fof(f863,plain,
    ( ! [X12] :
        ( v1_partfun1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12),sK0)
        | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X12) )
    | ~ spl6_5
    | ~ spl6_6
    | spl6_10
    | ~ spl6_11
    | spl6_14 ),
    inference(subsumption_resolution,[],[f862,f413])).

fof(f413,plain,
    ( ! [X0] :
        ( v1_funct_2(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),sK0,k1_tarski(sK1))
        | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) )
    | ~ spl6_5
    | ~ spl6_6
    | spl6_10 ),
    inference(subsumption_resolution,[],[f411,f184])).

fof(f411,plain,
    ( ! [X0] :
        ( v1_funct_2(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),sK0,k1_tarski(sK1))
        | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
        | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) )
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(resolution,[],[f195,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( sK5(X0,X1) != X1
        & r2_hidden(sK5(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK5(X0,X1) != X1
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f195,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2))
        | v1_funct_2(X1,sK0,k1_tarski(sK1)) )
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f191,f116])).

fof(f116,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl6_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f191,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2))
        | v1_funct_2(X1,sK0,k1_tarski(sK1))
        | ~ v1_funct_1(sK2) )
    | ~ spl6_5 ),
    inference(resolution,[],[f65,f111])).

fof(f111,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl6_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).

fof(f862,plain,
    ( ! [X12] :
        ( k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X12)
        | v1_partfun1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12),sK0)
        | ~ v1_funct_2(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12),sK0,k1_tarski(sK1)) )
    | ~ spl6_5
    | ~ spl6_6
    | spl6_10
    | ~ spl6_11
    | spl6_14 ),
    inference(subsumption_resolution,[],[f861,f188])).

fof(f188,plain,
    ( ! [X0] :
        ( v1_funct_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0))
        | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl6_11
  <=> ! [X0] :
        ( v1_funct_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0))
        | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f861,plain,
    ( ! [X12] :
        ( k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X12)
        | v1_partfun1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12),sK0)
        | ~ v1_funct_2(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12),sK0,k1_tarski(sK1))
        | ~ v1_funct_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12)) )
    | ~ spl6_5
    | ~ spl6_6
    | spl6_10
    | spl6_14 ),
    inference(subsumption_resolution,[],[f848,f215])).

fof(f215,plain,
    ( k1_xboole_0 != k1_tarski(sK1)
    | spl6_14 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl6_14
  <=> k1_xboole_0 = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f848,plain,
    ( ! [X12] :
        ( k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X12)
        | k1_xboole_0 = k1_tarski(sK1)
        | v1_partfun1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12),sK0)
        | ~ v1_funct_2(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12),sK0,k1_tarski(sK1))
        | ~ v1_funct_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12)) )
    | ~ spl6_5
    | ~ spl6_6
    | spl6_10 ),
    inference(resolution,[],[f470,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

fof(f470,plain,
    ( ! [X0] :
        ( m1_subset_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) )
    | ~ spl6_5
    | ~ spl6_6
    | spl6_10 ),
    inference(subsumption_resolution,[],[f468,f184])).

fof(f468,plain,
    ( ! [X0] :
        ( m1_subset_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
        | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) )
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(resolution,[],[f233,f58])).

fof(f233,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2))
        | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) )
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f229,f116])).

fof(f229,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2))
        | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(sK2) )
    | ~ spl6_5 ),
    inference(resolution,[],[f66,f111])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f852,plain,
    ( ! [X1] :
        ( k1_tarski(X1) = k5_partfun1(sK0,k1_tarski(sK1),sK2)
        | sK3 = sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X1)
        | ~ v1_partfun1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X1),sK0) )
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_10
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f841,f188])).

fof(f841,plain,
    ( ! [X1] :
        ( k1_tarski(X1) = k5_partfun1(sK0,k1_tarski(sK1),sK2)
        | sK3 = sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X1)
        | ~ v1_partfun1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X1),sK0)
        | ~ v1_funct_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X1)) )
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_10
    | ~ spl6_13 ),
    inference(resolution,[],[f470,f476])).

fof(f476,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | sK3 = X0
        | ~ v1_partfun1(X0,sK0)
        | ~ v1_funct_1(X0) )
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f251,f239])).

fof(f239,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | r1_partfun1(X0,sK3)
        | ~ v1_funct_1(X0) )
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f236,f106])).

fof(f106,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl6_4
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f236,plain,
    ( ! [X0] :
        ( r1_partfun1(X0,sK3)
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(X0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f69,f96])).

fof(f96,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl6_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | r1_partfun1(X2,X3)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_1(X3) )
         => r1_partfun1(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_partfun1)).

fof(f251,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(X0,sK3)
        | ~ v1_partfun1(X0,sK0)
        | sK3 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(X0) )
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f250,f106])).

fof(f250,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(X0,sK3)
        | ~ v1_partfun1(X0,sK0)
        | sK3 = X0
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(X0) )
    | ~ spl6_2
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f246,f212])).

fof(f212,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl6_13
  <=> v1_partfun1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f246,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(X0,sK3)
        | ~ v1_partfun1(sK3,sK0)
        | ~ v1_partfun1(X0,sK0)
        | sK3 = X0
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(X0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f70,f96])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_partfun1(X2,X3)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | X2 = X3
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f514,plain,
    ( ~ spl6_7
    | ~ spl6_33 ),
    inference(avatar_contradiction_clause,[],[f513])).

fof(f513,plain,
    ( $false
    | ~ spl6_7
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f511,f121])).

fof(f121,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl6_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f511,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl6_33 ),
    inference(resolution,[],[f496,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f496,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f494])).

fof(f494,plain,
    ( spl6_33
  <=> r2_hidden(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f503,plain,
    ( spl6_34
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f498,f284,f114,f109,f104,f94,f500])).

fof(f500,plain,
    ( spl6_34
  <=> r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f284,plain,
    ( spl6_19
  <=> ! [X0] :
        ( ~ r1_partfun1(X0,sK3)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f498,plain,
    ( r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f489,f116])).

fof(f489,plain,
    ( ~ v1_funct_1(sK2)
    | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_19 ),
    inference(resolution,[],[f487,f111])).

fof(f487,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(X0)
        | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X0)) )
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f285,f239])).

fof(f285,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(X0,sK3)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X0)) )
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f284])).

fof(f394,plain,
    ( spl6_11
    | ~ spl6_5
    | ~ spl6_6
    | spl6_10 ),
    inference(avatar_split_clause,[],[f393,f183,f114,f109,f187])).

fof(f393,plain,
    ( ! [X0] :
        ( v1_funct_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0))
        | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) )
    | ~ spl6_5
    | ~ spl6_6
    | spl6_10 ),
    inference(subsumption_resolution,[],[f391,f184])).

fof(f391,plain,
    ( ! [X0] :
        ( v1_funct_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0))
        | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
        | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) )
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(resolution,[],[f171,f58])).

fof(f171,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2))
        | v1_funct_1(X1) )
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f167,f116])).

fof(f167,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2))
        | v1_funct_1(X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl6_5 ),
    inference(resolution,[],[f64,f111])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | v1_funct_1(X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f361,plain,
    ( spl6_19
    | spl6_14
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f360,f104,f99,f94,f214,f284])).

fof(f99,plain,
    ( spl6_3
  <=> v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f360,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k1_tarski(sK1)
        | ~ r1_partfun1(X1,sK3)
        | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(X1) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f359,f106])).

fof(f359,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k1_tarski(sK1)
        | ~ r1_partfun1(X1,sK3)
        | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X1))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(X1) )
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f352,f101])).

fof(f101,plain,
    ( v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f352,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k1_tarski(sK1)
        | ~ r1_partfun1(X1,sK3)
        | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X1))
        | ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_1(X1) )
    | ~ spl6_2 ),
    inference(resolution,[],[f96,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_partfun1(X2,X3)
      | r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_2)).

fof(f350,plain,
    ( ~ spl6_7
    | ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f349])).

fof(f349,plain,
    ( $false
    | ~ spl6_7
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f348,f121])).

fof(f348,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f306,f83])).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f306,plain,
    ( ! [X8,X9] : ~ v1_xboole_0(k2_zfmisc_1(k2_tarski(X8,X9),k1_xboole_0))
    | ~ spl6_14 ),
    inference(superposition,[],[f154,f216])).

fof(f216,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f214])).

fof(f154,plain,(
    ! [X12,X10,X11] : ~ v1_xboole_0(k2_zfmisc_1(k2_tarski(X10,X12),k1_tarski(X11))) ),
    inference(superposition,[],[f123,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f123,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(resolution,[],[f78,f73])).

fof(f78,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f217,plain,
    ( spl6_13
    | spl6_14
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f208,f104,f99,f94,f214,f210])).

fof(f208,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | v1_partfun1(sK3,sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f207,f106])).

fof(f207,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | v1_partfun1(sK3,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f203,f101])).

fof(f203,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | v1_partfun1(sK3,sK0)
    | ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ v1_funct_1(sK3)
    | ~ spl6_2 ),
    inference(resolution,[],[f86,f96])).

fof(f122,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f75,f119])).

fof(f75,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f117,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f44,f114])).

fof(f44,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK3,sK0,k1_tarski(sK1))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f33,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(sK0,k1_tarski(sK1),sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
          & v1_funct_2(X3,sK0,k1_tarski(sK1))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X3] :
        ( k1_tarski(X3) != k5_partfun1(sK0,k1_tarski(sK1),sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        & v1_funct_2(X3,sK0,k1_tarski(sK1))
        & v1_funct_1(X3) )
   => ( k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      & v1_funct_2(sK3,sK0,k1_tarski(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
              & v1_funct_2(X3,X0,k1_tarski(X1))
              & v1_funct_1(X3) )
           => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_2)).

fof(f112,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f45,f109])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f107,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f46,f104])).

fof(f46,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f102,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f47,f99])).

fof(f47,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f97,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f48,f94])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f92,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f49,f89])).

fof(f49,plain,(
    k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:38:10 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.56  % (16404)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.57  % (16411)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.57  % (16414)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.57  % (16423)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.57  % (16406)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.57  % (16431)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.58  % (16407)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.58  % (16431)Refutation not found, incomplete strategy% (16431)------------------------------
% 0.20/0.58  % (16431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (16431)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (16431)Memory used [KB]: 1663
% 0.20/0.58  % (16431)Time elapsed: 0.003 s
% 0.20/0.58  % (16431)------------------------------
% 0.20/0.58  % (16431)------------------------------
% 1.56/0.58  % (16402)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.56/0.59  % (16413)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.56/0.59  % (16421)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.56/0.59  % (16403)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.56/0.60  % (16417)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.56/0.60  % (16405)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.56/0.60  % (16408)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.56/0.60  % (16425)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.56/0.60  % (16427)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.90/0.61  % (16428)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.90/0.61  % (16419)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.90/0.61  % (16422)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.90/0.61  % (16409)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.90/0.62  % (16415)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.90/0.62  % (16420)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.90/0.62  % (16412)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.90/0.62  % (16416)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.90/0.62  % (16424)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.90/0.62  % (16430)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.90/0.63  % (16429)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.90/0.63  % (16429)Refutation not found, incomplete strategy% (16429)------------------------------
% 1.90/0.63  % (16429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.63  % (16429)Termination reason: Refutation not found, incomplete strategy
% 1.90/0.63  
% 1.90/0.63  % (16429)Memory used [KB]: 6268
% 1.90/0.63  % (16429)Time elapsed: 0.197 s
% 1.90/0.63  % (16429)------------------------------
% 1.90/0.63  % (16429)------------------------------
% 1.90/0.63  % (16418)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.90/0.64  % (16410)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.90/0.65  % (16426)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 2.18/0.65  % (16418)Refutation not found, incomplete strategy% (16418)------------------------------
% 2.18/0.65  % (16418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.65  % (16418)Termination reason: Refutation not found, incomplete strategy
% 2.18/0.65  
% 2.18/0.65  % (16418)Memory used [KB]: 10746
% 2.18/0.65  % (16418)Time elapsed: 0.229 s
% 2.18/0.65  % (16418)------------------------------
% 2.18/0.65  % (16418)------------------------------
% 2.18/0.66  % (16423)Refutation found. Thanks to Tanya!
% 2.18/0.66  % SZS status Theorem for theBenchmark
% 2.18/0.66  % SZS output start Proof for theBenchmark
% 2.18/0.66  fof(f1068,plain,(
% 2.18/0.66    $false),
% 2.18/0.66    inference(avatar_sat_refutation,[],[f92,f97,f102,f107,f112,f117,f122,f217,f350,f361,f394,f503,f514,f1066,f1067])).
% 2.18/0.66  fof(f1067,plain,(
% 2.18/0.66    k1_xboole_0 != k5_partfun1(sK0,k1_tarski(sK1),sK2) | r2_hidden(sK3,k1_xboole_0) | ~r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2))),
% 2.18/0.66    introduced(theory_tautology_sat_conflict,[])).
% 2.18/0.66  fof(f1066,plain,(
% 2.18/0.66    spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_10 | ~spl6_11 | ~spl6_13 | spl6_14),
% 2.18/0.66    inference(avatar_contradiction_clause,[],[f1065])).
% 2.18/0.66  fof(f1065,plain,(
% 2.18/0.66    $false | (spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_10 | ~spl6_11 | ~spl6_13 | spl6_14)),
% 2.18/0.66    inference(subsumption_resolution,[],[f1064,f91])).
% 2.18/0.66  fof(f91,plain,(
% 2.18/0.66    k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3) | spl6_1),
% 2.18/0.66    inference(avatar_component_clause,[],[f89])).
% 2.18/0.66  fof(f89,plain,(
% 2.18/0.66    spl6_1 <=> k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(sK3)),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.18/0.66  fof(f1064,plain,(
% 2.18/0.66    k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(sK3) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_10 | ~spl6_11 | ~spl6_13 | spl6_14)),
% 2.18/0.66    inference(equality_resolution,[],[f1061])).
% 2.18/0.66  fof(f1061,plain,(
% 2.18/0.66    ( ! [X10] : (sK3 != X10 | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X10)) ) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_10 | ~spl6_11 | ~spl6_13 | spl6_14)),
% 2.18/0.66    inference(subsumption_resolution,[],[f1051,f184])).
% 2.18/0.66  fof(f184,plain,(
% 2.18/0.66    k1_xboole_0 != k5_partfun1(sK0,k1_tarski(sK1),sK2) | spl6_10),
% 2.18/0.66    inference(avatar_component_clause,[],[f183])).
% 2.18/0.66  fof(f183,plain,(
% 2.18/0.66    spl6_10 <=> k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 2.18/0.66  fof(f1051,plain,(
% 2.18/0.66    ( ! [X10] : (sK3 != X10 | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X10)) ) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_10 | ~spl6_11 | ~spl6_13 | spl6_14)),
% 2.18/0.66    inference(duplicate_literal_removal,[],[f1048])).
% 2.18/0.66  fof(f1048,plain,(
% 2.18/0.66    ( ! [X10] : (sK3 != X10 | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X10) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X10)) ) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_10 | ~spl6_11 | ~spl6_13 | spl6_14)),
% 2.18/0.66    inference(superposition,[],[f59,f1038])).
% 2.18/0.66  fof(f1038,plain,(
% 2.18/0.66    ( ! [X1] : (sK3 = sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X1) | k1_tarski(X1) = k5_partfun1(sK0,k1_tarski(sK1),sK2)) ) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_10 | ~spl6_11 | ~spl6_13 | spl6_14)),
% 2.18/0.66    inference(subsumption_resolution,[],[f852,f863])).
% 2.18/0.66  fof(f863,plain,(
% 2.18/0.66    ( ! [X12] : (v1_partfun1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12),sK0) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X12)) ) | (~spl6_5 | ~spl6_6 | spl6_10 | ~spl6_11 | spl6_14)),
% 2.18/0.66    inference(subsumption_resolution,[],[f862,f413])).
% 2.18/0.66  fof(f413,plain,(
% 2.18/0.66    ( ! [X0] : (v1_funct_2(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),sK0,k1_tarski(sK1)) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)) ) | (~spl6_5 | ~spl6_6 | spl6_10)),
% 2.18/0.66    inference(subsumption_resolution,[],[f411,f184])).
% 2.18/0.66  fof(f411,plain,(
% 2.18/0.66    ( ! [X0] : (v1_funct_2(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),sK0,k1_tarski(sK1)) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)) ) | (~spl6_5 | ~spl6_6)),
% 2.18/0.66    inference(resolution,[],[f195,f58])).
% 2.18/0.66  fof(f58,plain,(
% 2.18/0.66    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 2.18/0.66    inference(cnf_transformation,[],[f41])).
% 2.18/0.66  fof(f41,plain,(
% 2.18/0.66    ! [X0,X1] : ((sK5(X0,X1) != X1 & r2_hidden(sK5(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 2.18/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f40])).
% 2.18/0.66  fof(f40,plain,(
% 2.18/0.66    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK5(X0,X1) != X1 & r2_hidden(sK5(X0,X1),X0)))),
% 2.18/0.66    introduced(choice_axiom,[])).
% 2.18/0.66  fof(f22,plain,(
% 2.18/0.66    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 2.18/0.66    inference(ennf_transformation,[],[f7])).
% 2.18/0.66  fof(f7,axiom,(
% 2.18/0.66    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 2.18/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).
% 2.18/0.66  fof(f195,plain,(
% 2.18/0.66    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | v1_funct_2(X1,sK0,k1_tarski(sK1))) ) | (~spl6_5 | ~spl6_6)),
% 2.18/0.66    inference(subsumption_resolution,[],[f191,f116])).
% 2.18/0.66  fof(f116,plain,(
% 2.18/0.66    v1_funct_1(sK2) | ~spl6_6),
% 2.18/0.66    inference(avatar_component_clause,[],[f114])).
% 2.18/0.66  fof(f114,plain,(
% 2.18/0.66    spl6_6 <=> v1_funct_1(sK2)),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 2.18/0.66  fof(f191,plain,(
% 2.18/0.66    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | v1_funct_2(X1,sK0,k1_tarski(sK1)) | ~v1_funct_1(sK2)) ) | ~spl6_5),
% 2.18/0.66    inference(resolution,[],[f65,f111])).
% 2.18/0.66  fof(f111,plain,(
% 2.18/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~spl6_5),
% 2.18/0.66    inference(avatar_component_clause,[],[f109])).
% 2.18/0.66  fof(f109,plain,(
% 2.18/0.66    spl6_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 2.18/0.66  fof(f65,plain,(
% 2.18/0.66    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | v1_funct_2(X3,X0,X1) | ~v1_funct_1(X2)) )),
% 2.18/0.66    inference(cnf_transformation,[],[f24])).
% 2.18/0.66  fof(f24,plain,(
% 2.18/0.66    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.18/0.66    inference(flattening,[],[f23])).
% 2.18/0.66  fof(f23,plain,(
% 2.18/0.66    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.18/0.66    inference(ennf_transformation,[],[f14])).
% 2.18/0.66  fof(f14,axiom,(
% 2.18/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))))),
% 2.18/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).
% 2.18/0.66  fof(f862,plain,(
% 2.18/0.66    ( ! [X12] : (k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X12) | v1_partfun1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12),sK0) | ~v1_funct_2(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12),sK0,k1_tarski(sK1))) ) | (~spl6_5 | ~spl6_6 | spl6_10 | ~spl6_11 | spl6_14)),
% 2.18/0.66    inference(subsumption_resolution,[],[f861,f188])).
% 2.18/0.66  fof(f188,plain,(
% 2.18/0.66    ( ! [X0] : (v1_funct_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0)) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)) ) | ~spl6_11),
% 2.18/0.66    inference(avatar_component_clause,[],[f187])).
% 2.18/0.66  fof(f187,plain,(
% 2.18/0.66    spl6_11 <=> ! [X0] : (v1_funct_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0)) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 2.18/0.66  fof(f861,plain,(
% 2.18/0.66    ( ! [X12] : (k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X12) | v1_partfun1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12),sK0) | ~v1_funct_2(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12),sK0,k1_tarski(sK1)) | ~v1_funct_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12))) ) | (~spl6_5 | ~spl6_6 | spl6_10 | spl6_14)),
% 2.18/0.66    inference(subsumption_resolution,[],[f848,f215])).
% 2.18/0.66  fof(f215,plain,(
% 2.18/0.66    k1_xboole_0 != k1_tarski(sK1) | spl6_14),
% 2.18/0.66    inference(avatar_component_clause,[],[f214])).
% 2.18/0.66  fof(f214,plain,(
% 2.18/0.66    spl6_14 <=> k1_xboole_0 = k1_tarski(sK1)),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 2.18/0.66  fof(f848,plain,(
% 2.18/0.66    ( ! [X12] : (k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X12) | k1_xboole_0 = k1_tarski(sK1) | v1_partfun1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12),sK0) | ~v1_funct_2(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12),sK0,k1_tarski(sK1)) | ~v1_funct_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X12))) ) | (~spl6_5 | ~spl6_6 | spl6_10)),
% 2.18/0.66    inference(resolution,[],[f470,f86])).
% 2.18/0.66  fof(f86,plain,(
% 2.18/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.18/0.66    inference(duplicate_literal_removal,[],[f67])).
% 2.18/0.66  fof(f67,plain,(
% 2.18/0.66    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.18/0.66    inference(cnf_transformation,[],[f26])).
% 2.18/0.66  fof(f26,plain,(
% 2.18/0.66    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.18/0.66    inference(flattening,[],[f25])).
% 2.18/0.66  fof(f25,plain,(
% 2.18/0.66    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.18/0.66    inference(ennf_transformation,[],[f10])).
% 2.18/0.66  fof(f10,axiom,(
% 2.18/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.18/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).
% 2.18/0.66  fof(f470,plain,(
% 2.18/0.66    ( ! [X0] : (m1_subset_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)) ) | (~spl6_5 | ~spl6_6 | spl6_10)),
% 2.18/0.66    inference(subsumption_resolution,[],[f468,f184])).
% 2.18/0.66  fof(f468,plain,(
% 2.18/0.66    ( ! [X0] : (m1_subset_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)) ) | (~spl6_5 | ~spl6_6)),
% 2.18/0.66    inference(resolution,[],[f233,f58])).
% 2.18/0.66  fof(f233,plain,(
% 2.18/0.66    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))) ) | (~spl6_5 | ~spl6_6)),
% 2.18/0.66    inference(subsumption_resolution,[],[f229,f116])).
% 2.18/0.66  fof(f229,plain,(
% 2.18/0.66    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(sK2)) ) | ~spl6_5),
% 2.18/0.66    inference(resolution,[],[f66,f111])).
% 2.18/0.66  fof(f66,plain,(
% 2.18/0.66    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.18/0.66    inference(cnf_transformation,[],[f24])).
% 2.18/0.66  fof(f852,plain,(
% 2.18/0.66    ( ! [X1] : (k1_tarski(X1) = k5_partfun1(sK0,k1_tarski(sK1),sK2) | sK3 = sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X1) | ~v1_partfun1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X1),sK0)) ) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_10 | ~spl6_11 | ~spl6_13)),
% 2.18/0.66    inference(subsumption_resolution,[],[f841,f188])).
% 2.18/0.66  fof(f841,plain,(
% 2.18/0.66    ( ! [X1] : (k1_tarski(X1) = k5_partfun1(sK0,k1_tarski(sK1),sK2) | sK3 = sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X1) | ~v1_partfun1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X1),sK0) | ~v1_funct_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X1))) ) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_10 | ~spl6_13)),
% 2.18/0.66    inference(resolution,[],[f470,f476])).
% 2.18/0.66  fof(f476,plain,(
% 2.18/0.66    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | sK3 = X0 | ~v1_partfun1(X0,sK0) | ~v1_funct_1(X0)) ) | (~spl6_2 | ~spl6_4 | ~spl6_13)),
% 2.18/0.66    inference(subsumption_resolution,[],[f251,f239])).
% 2.18/0.66  fof(f239,plain,(
% 2.18/0.66    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | r1_partfun1(X0,sK3) | ~v1_funct_1(X0)) ) | (~spl6_2 | ~spl6_4)),
% 2.18/0.66    inference(subsumption_resolution,[],[f236,f106])).
% 2.18/0.66  fof(f106,plain,(
% 2.18/0.66    v1_funct_1(sK3) | ~spl6_4),
% 2.18/0.66    inference(avatar_component_clause,[],[f104])).
% 2.18/0.66  fof(f104,plain,(
% 2.18/0.66    spl6_4 <=> v1_funct_1(sK3)),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.18/0.66  fof(f236,plain,(
% 2.18/0.66    ( ! [X0] : (r1_partfun1(X0,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X0)) ) | ~spl6_2),
% 2.18/0.66    inference(resolution,[],[f69,f96])).
% 2.18/0.66  fof(f96,plain,(
% 2.18/0.66    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~spl6_2),
% 2.18/0.66    inference(avatar_component_clause,[],[f94])).
% 2.18/0.66  fof(f94,plain,(
% 2.18/0.66    spl6_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.18/0.66  fof(f69,plain,(
% 2.18/0.66    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | r1_partfun1(X2,X3) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)) )),
% 2.18/0.66    inference(cnf_transformation,[],[f28])).
% 2.18/0.66  fof(f28,plain,(
% 2.18/0.66    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2))),
% 2.18/0.66    inference(flattening,[],[f27])).
% 2.18/0.66  fof(f27,plain,(
% 2.18/0.66    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)))),
% 2.18/0.66    inference(ennf_transformation,[],[f11])).
% 2.18/0.66  fof(f11,axiom,(
% 2.18/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X3)) => r1_partfun1(X2,X3)))),
% 2.18/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_partfun1)).
% 2.18/0.66  fof(f251,plain,(
% 2.18/0.66    ( ! [X0] : (~r1_partfun1(X0,sK3) | ~v1_partfun1(X0,sK0) | sK3 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X0)) ) | (~spl6_2 | ~spl6_4 | ~spl6_13)),
% 2.18/0.66    inference(subsumption_resolution,[],[f250,f106])).
% 2.18/0.66  fof(f250,plain,(
% 2.18/0.66    ( ! [X0] : (~r1_partfun1(X0,sK3) | ~v1_partfun1(X0,sK0) | sK3 = X0 | ~v1_funct_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X0)) ) | (~spl6_2 | ~spl6_13)),
% 2.18/0.66    inference(subsumption_resolution,[],[f246,f212])).
% 2.18/0.66  fof(f212,plain,(
% 2.18/0.66    v1_partfun1(sK3,sK0) | ~spl6_13),
% 2.18/0.66    inference(avatar_component_clause,[],[f210])).
% 2.18/0.66  fof(f210,plain,(
% 2.18/0.66    spl6_13 <=> v1_partfun1(sK3,sK0)),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 2.18/0.66  fof(f246,plain,(
% 2.18/0.66    ( ! [X0] : (~r1_partfun1(X0,sK3) | ~v1_partfun1(sK3,sK0) | ~v1_partfun1(X0,sK0) | sK3 = X0 | ~v1_funct_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X0)) ) | ~spl6_2),
% 2.18/0.66    inference(resolution,[],[f70,f96])).
% 2.18/0.66  fof(f70,plain,(
% 2.18/0.66    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | X2 = X3 | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.18/0.66    inference(cnf_transformation,[],[f30])).
% 2.18/0.66  fof(f30,plain,(
% 2.18/0.66    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.18/0.66    inference(flattening,[],[f29])).
% 2.18/0.66  fof(f29,plain,(
% 2.18/0.66    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.18/0.66    inference(ennf_transformation,[],[f12])).
% 2.18/0.66  fof(f12,axiom,(
% 2.18/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 2.18/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).
% 2.18/0.66  fof(f59,plain,(
% 2.18/0.66    ( ! [X0,X1] : (sK5(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 2.18/0.66    inference(cnf_transformation,[],[f41])).
% 2.18/0.66  fof(f514,plain,(
% 2.18/0.66    ~spl6_7 | ~spl6_33),
% 2.18/0.66    inference(avatar_contradiction_clause,[],[f513])).
% 2.18/0.66  fof(f513,plain,(
% 2.18/0.66    $false | (~spl6_7 | ~spl6_33)),
% 2.18/0.66    inference(subsumption_resolution,[],[f511,f121])).
% 2.18/0.66  fof(f121,plain,(
% 2.18/0.66    v1_xboole_0(k1_xboole_0) | ~spl6_7),
% 2.18/0.66    inference(avatar_component_clause,[],[f119])).
% 2.18/0.66  fof(f119,plain,(
% 2.18/0.66    spl6_7 <=> v1_xboole_0(k1_xboole_0)),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 2.18/0.66  fof(f511,plain,(
% 2.18/0.66    ~v1_xboole_0(k1_xboole_0) | ~spl6_33),
% 2.18/0.66    inference(resolution,[],[f496,f73])).
% 2.18/0.66  fof(f73,plain,(
% 2.18/0.66    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.18/0.66    inference(cnf_transformation,[],[f31])).
% 2.18/0.66  fof(f31,plain,(
% 2.18/0.66    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 2.18/0.66    inference(ennf_transformation,[],[f17])).
% 2.18/0.66  fof(f17,plain,(
% 2.18/0.66    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 2.18/0.66    inference(unused_predicate_definition_removal,[],[f1])).
% 2.18/0.66  fof(f1,axiom,(
% 2.18/0.66    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.18/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.18/0.66  fof(f496,plain,(
% 2.18/0.66    r2_hidden(sK3,k1_xboole_0) | ~spl6_33),
% 2.18/0.66    inference(avatar_component_clause,[],[f494])).
% 2.18/0.66  fof(f494,plain,(
% 2.18/0.66    spl6_33 <=> r2_hidden(sK3,k1_xboole_0)),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 2.18/0.66  fof(f503,plain,(
% 2.18/0.66    spl6_34 | ~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_19),
% 2.18/0.66    inference(avatar_split_clause,[],[f498,f284,f114,f109,f104,f94,f500])).
% 2.18/0.66  fof(f500,plain,(
% 2.18/0.66    spl6_34 <=> r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 2.18/0.66  fof(f284,plain,(
% 2.18/0.66    spl6_19 <=> ! [X0] : (~r1_partfun1(X0,sK3) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X0)))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 2.18/0.66  fof(f498,plain,(
% 2.18/0.66    r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_19)),
% 2.18/0.66    inference(subsumption_resolution,[],[f489,f116])).
% 2.18/0.66  fof(f489,plain,(
% 2.18/0.66    ~v1_funct_1(sK2) | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_19)),
% 2.18/0.66    inference(resolution,[],[f487,f111])).
% 2.18/0.66  fof(f487,plain,(
% 2.18/0.66    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X0) | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X0))) ) | (~spl6_2 | ~spl6_4 | ~spl6_19)),
% 2.18/0.66    inference(subsumption_resolution,[],[f285,f239])).
% 2.18/0.66  fof(f285,plain,(
% 2.18/0.66    ( ! [X0] : (~r1_partfun1(X0,sK3) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X0))) ) | ~spl6_19),
% 2.18/0.66    inference(avatar_component_clause,[],[f284])).
% 2.18/0.66  fof(f394,plain,(
% 2.18/0.66    spl6_11 | ~spl6_5 | ~spl6_6 | spl6_10),
% 2.18/0.66    inference(avatar_split_clause,[],[f393,f183,f114,f109,f187])).
% 2.18/0.66  fof(f393,plain,(
% 2.18/0.66    ( ! [X0] : (v1_funct_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0)) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)) ) | (~spl6_5 | ~spl6_6 | spl6_10)),
% 2.18/0.66    inference(subsumption_resolution,[],[f391,f184])).
% 2.18/0.66  fof(f391,plain,(
% 2.18/0.66    ( ! [X0] : (v1_funct_1(sK5(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0)) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)) ) | (~spl6_5 | ~spl6_6)),
% 2.18/0.66    inference(resolution,[],[f171,f58])).
% 2.18/0.66  fof(f171,plain,(
% 2.18/0.66    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | v1_funct_1(X1)) ) | (~spl6_5 | ~spl6_6)),
% 2.18/0.66    inference(subsumption_resolution,[],[f167,f116])).
% 2.18/0.66  fof(f167,plain,(
% 2.18/0.66    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | v1_funct_1(X1) | ~v1_funct_1(sK2)) ) | ~spl6_5),
% 2.18/0.66    inference(resolution,[],[f64,f111])).
% 2.18/0.66  fof(f64,plain,(
% 2.18/0.66    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | v1_funct_1(X3) | ~v1_funct_1(X2)) )),
% 2.18/0.66    inference(cnf_transformation,[],[f24])).
% 2.18/0.66  fof(f361,plain,(
% 2.18/0.66    spl6_19 | spl6_14 | ~spl6_2 | ~spl6_3 | ~spl6_4),
% 2.18/0.66    inference(avatar_split_clause,[],[f360,f104,f99,f94,f214,f284])).
% 2.18/0.66  fof(f99,plain,(
% 2.18/0.66    spl6_3 <=> v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.18/0.66  fof(f360,plain,(
% 2.18/0.66    ( ! [X1] : (k1_xboole_0 = k1_tarski(sK1) | ~r1_partfun1(X1,sK3) | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X1)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4)),
% 2.18/0.66    inference(subsumption_resolution,[],[f359,f106])).
% 2.18/0.66  fof(f359,plain,(
% 2.18/0.66    ( ! [X1] : (k1_xboole_0 = k1_tarski(sK1) | ~r1_partfun1(X1,sK3) | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X1)) | ~v1_funct_1(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X1)) ) | (~spl6_2 | ~spl6_3)),
% 2.18/0.66    inference(subsumption_resolution,[],[f352,f101])).
% 2.18/0.66  fof(f101,plain,(
% 2.18/0.66    v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~spl6_3),
% 2.18/0.66    inference(avatar_component_clause,[],[f99])).
% 2.18/0.66  fof(f352,plain,(
% 2.18/0.66    ( ! [X1] : (k1_xboole_0 = k1_tarski(sK1) | ~r1_partfun1(X1,sK3) | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X1)) | ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~v1_funct_1(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X1)) ) | ~spl6_2),
% 2.18/0.66    inference(resolution,[],[f96,f56])).
% 2.18/0.66  fof(f56,plain,(
% 2.18/0.66    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r1_partfun1(X2,X3) | r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.18/0.66    inference(cnf_transformation,[],[f21])).
% 2.18/0.66  fof(f21,plain,(
% 2.18/0.66    ! [X0,X1,X2] : (! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.18/0.66    inference(flattening,[],[f20])).
% 2.18/0.66  fof(f20,plain,(
% 2.18/0.66    ! [X0,X1,X2] : (! [X3] : (((r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_partfun1(X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.18/0.66    inference(ennf_transformation,[],[f13])).
% 2.18/0.66  fof(f13,axiom,(
% 2.18/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 2.18/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_2)).
% 2.18/0.66  fof(f350,plain,(
% 2.18/0.66    ~spl6_7 | ~spl6_14),
% 2.18/0.66    inference(avatar_contradiction_clause,[],[f349])).
% 2.18/0.66  fof(f349,plain,(
% 2.18/0.66    $false | (~spl6_7 | ~spl6_14)),
% 2.18/0.66    inference(subsumption_resolution,[],[f348,f121])).
% 2.18/0.66  fof(f348,plain,(
% 2.18/0.66    ~v1_xboole_0(k1_xboole_0) | ~spl6_14),
% 2.18/0.66    inference(forward_demodulation,[],[f306,f83])).
% 2.18/0.66  fof(f83,plain,(
% 2.18/0.66    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.18/0.66    inference(equality_resolution,[],[f62])).
% 2.18/0.66  fof(f62,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.18/0.66    inference(cnf_transformation,[],[f43])).
% 2.18/0.66  fof(f43,plain,(
% 2.18/0.66    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.18/0.66    inference(flattening,[],[f42])).
% 2.18/0.66  fof(f42,plain,(
% 2.18/0.66    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.18/0.66    inference(nnf_transformation,[],[f8])).
% 2.18/0.66  fof(f8,axiom,(
% 2.18/0.66    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.18/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.18/0.66  fof(f306,plain,(
% 2.18/0.66    ( ! [X8,X9] : (~v1_xboole_0(k2_zfmisc_1(k2_tarski(X8,X9),k1_xboole_0))) ) | ~spl6_14),
% 2.18/0.66    inference(superposition,[],[f154,f216])).
% 2.18/0.66  fof(f216,plain,(
% 2.18/0.66    k1_xboole_0 = k1_tarski(sK1) | ~spl6_14),
% 2.18/0.66    inference(avatar_component_clause,[],[f214])).
% 2.18/0.66  fof(f154,plain,(
% 2.18/0.66    ( ! [X12,X10,X11] : (~v1_xboole_0(k2_zfmisc_1(k2_tarski(X10,X12),k1_tarski(X11)))) )),
% 2.18/0.66    inference(superposition,[],[f123,f72])).
% 2.18/0.66  fof(f72,plain,(
% 2.18/0.66    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 2.18/0.66    inference(cnf_transformation,[],[f9])).
% 2.18/0.66  fof(f9,axiom,(
% 2.18/0.66    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 2.18/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 2.18/0.66  fof(f123,plain,(
% 2.18/0.66    ( ! [X0,X1] : (~v1_xboole_0(k2_tarski(X0,X1))) )),
% 2.18/0.66    inference(resolution,[],[f78,f73])).
% 2.18/0.66  fof(f78,plain,(
% 2.18/0.66    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 2.18/0.66    inference(equality_resolution,[],[f77])).
% 2.18/0.66  fof(f77,plain,(
% 2.18/0.66    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 2.18/0.66    inference(equality_resolution,[],[f52])).
% 2.18/0.66  fof(f52,plain,(
% 2.18/0.66    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.18/0.66    inference(cnf_transformation,[],[f39])).
% 2.18/0.66  fof(f39,plain,(
% 2.18/0.66    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.18/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).
% 2.18/0.66  fof(f38,plain,(
% 2.18/0.66    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.18/0.66    introduced(choice_axiom,[])).
% 2.18/0.66  fof(f37,plain,(
% 2.18/0.66    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.18/0.66    inference(rectify,[],[f36])).
% 2.18/0.66  fof(f36,plain,(
% 2.18/0.66    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.18/0.66    inference(flattening,[],[f35])).
% 2.18/0.66  fof(f35,plain,(
% 2.18/0.66    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.18/0.66    inference(nnf_transformation,[],[f3])).
% 2.18/0.66  fof(f3,axiom,(
% 2.18/0.66    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.18/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 2.18/0.66  fof(f217,plain,(
% 2.18/0.66    spl6_13 | spl6_14 | ~spl6_2 | ~spl6_3 | ~spl6_4),
% 2.18/0.66    inference(avatar_split_clause,[],[f208,f104,f99,f94,f214,f210])).
% 2.18/0.66  fof(f208,plain,(
% 2.18/0.66    k1_xboole_0 = k1_tarski(sK1) | v1_partfun1(sK3,sK0) | (~spl6_2 | ~spl6_3 | ~spl6_4)),
% 2.18/0.66    inference(subsumption_resolution,[],[f207,f106])).
% 2.18/0.66  fof(f207,plain,(
% 2.18/0.66    k1_xboole_0 = k1_tarski(sK1) | v1_partfun1(sK3,sK0) | ~v1_funct_1(sK3) | (~spl6_2 | ~spl6_3)),
% 2.18/0.66    inference(subsumption_resolution,[],[f203,f101])).
% 2.18/0.66  fof(f203,plain,(
% 2.18/0.66    k1_xboole_0 = k1_tarski(sK1) | v1_partfun1(sK3,sK0) | ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~v1_funct_1(sK3) | ~spl6_2),
% 2.18/0.66    inference(resolution,[],[f86,f96])).
% 2.18/0.66  fof(f122,plain,(
% 2.18/0.66    spl6_7),
% 2.18/0.66    inference(avatar_split_clause,[],[f75,f119])).
% 2.18/0.66  fof(f75,plain,(
% 2.18/0.66    v1_xboole_0(k1_xboole_0)),
% 2.18/0.66    inference(cnf_transformation,[],[f2])).
% 2.18/0.66  fof(f2,axiom,(
% 2.18/0.66    v1_xboole_0(k1_xboole_0)),
% 2.18/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.18/0.66  fof(f117,plain,(
% 2.18/0.66    spl6_6),
% 2.18/0.66    inference(avatar_split_clause,[],[f44,f114])).
% 2.18/0.66  fof(f44,plain,(
% 2.18/0.66    v1_funct_1(sK2)),
% 2.18/0.66    inference(cnf_transformation,[],[f34])).
% 2.18/0.66  fof(f34,plain,(
% 2.18/0.66    (k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_1(sK2)),
% 2.18/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f33,f32])).
% 2.18/0.66  fof(f32,plain,(
% 2.18/0.66    ? [X0,X1,X2] : (? [X3] : (k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => (? [X3] : (k1_tarski(X3) != k5_partfun1(sK0,k1_tarski(sK1),sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(X3,sK0,k1_tarski(sK1)) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_1(sK2))),
% 2.18/0.66    introduced(choice_axiom,[])).
% 2.18/0.66  fof(f33,plain,(
% 2.18/0.66    ? [X3] : (k1_tarski(X3) != k5_partfun1(sK0,k1_tarski(sK1),sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(X3,sK0,k1_tarski(sK1)) & v1_funct_1(X3)) => (k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3))),
% 2.18/0.66    introduced(choice_axiom,[])).
% 2.18/0.66  fof(f19,plain,(
% 2.18/0.66    ? [X0,X1,X2] : (? [X3] : (k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2))),
% 2.18/0.66    inference(flattening,[],[f18])).
% 2.18/0.66  fof(f18,plain,(
% 2.18/0.66    ? [X0,X1,X2] : (? [X3] : (k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)))),
% 2.18/0.66    inference(ennf_transformation,[],[f16])).
% 2.18/0.66  fof(f16,negated_conjecture,(
% 2.18/0.66    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3)))),
% 2.18/0.66    inference(negated_conjecture,[],[f15])).
% 2.18/0.66  fof(f15,conjecture,(
% 2.18/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3)))),
% 2.18/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_2)).
% 2.18/0.66  fof(f112,plain,(
% 2.18/0.66    spl6_5),
% 2.18/0.66    inference(avatar_split_clause,[],[f45,f109])).
% 2.18/0.66  fof(f45,plain,(
% 2.18/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 2.18/0.66    inference(cnf_transformation,[],[f34])).
% 2.18/0.66  fof(f107,plain,(
% 2.18/0.66    spl6_4),
% 2.18/0.66    inference(avatar_split_clause,[],[f46,f104])).
% 2.18/0.66  fof(f46,plain,(
% 2.18/0.66    v1_funct_1(sK3)),
% 2.18/0.66    inference(cnf_transformation,[],[f34])).
% 2.18/0.66  fof(f102,plain,(
% 2.18/0.66    spl6_3),
% 2.18/0.66    inference(avatar_split_clause,[],[f47,f99])).
% 2.18/0.66  fof(f47,plain,(
% 2.18/0.66    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 2.18/0.66    inference(cnf_transformation,[],[f34])).
% 2.18/0.66  fof(f97,plain,(
% 2.18/0.66    spl6_2),
% 2.18/0.66    inference(avatar_split_clause,[],[f48,f94])).
% 2.18/0.66  fof(f48,plain,(
% 2.18/0.66    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 2.18/0.66    inference(cnf_transformation,[],[f34])).
% 2.18/0.66  fof(f92,plain,(
% 2.18/0.66    ~spl6_1),
% 2.18/0.66    inference(avatar_split_clause,[],[f49,f89])).
% 2.18/0.66  fof(f49,plain,(
% 2.18/0.66    k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3)),
% 2.18/0.66    inference(cnf_transformation,[],[f34])).
% 2.18/0.66  % SZS output end Proof for theBenchmark
% 2.18/0.66  % (16423)------------------------------
% 2.18/0.66  % (16423)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.66  % (16423)Termination reason: Refutation
% 2.18/0.66  
% 2.18/0.66  % (16423)Memory used [KB]: 6908
% 2.18/0.66  % (16423)Time elapsed: 0.218 s
% 2.18/0.66  % (16423)------------------------------
% 2.18/0.66  % (16423)------------------------------
% 2.18/0.67  % (16401)Success in time 0.303 s
%------------------------------------------------------------------------------
