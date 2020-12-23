%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 347 expanded)
%              Number of leaves         :   35 ( 144 expanded)
%              Depth                    :   14
%              Number of atoms          :  572 (1303 expanded)
%              Number of equality atoms :  139 ( 371 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f650,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f86,f91,f108,f120,f131,f164,f204,f282,f294,f336,f364,f405,f469,f474,f477,f500,f507,f572,f583,f646,f649])).

fof(f649,plain,
    ( ~ spl6_50
    | ~ spl6_58 ),
    inference(avatar_contradiction_clause,[],[f648])).

fof(f648,plain,
    ( $false
    | ~ spl6_50
    | ~ spl6_58 ),
    inference(subsumption_resolution,[],[f647,f92])).

fof(f92,plain,(
    ! [X0] : ~ r2_hidden(X0,X0) ),
    inference(unit_resulting_resolution,[],[f65,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f65,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f647,plain,
    ( r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ spl6_50
    | ~ spl6_58 ),
    inference(forward_demodulation,[],[f645,f580])).

fof(f580,plain,
    ( k1_xboole_0 = sK5(k1_xboole_0,k1_xboole_0)
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f578])).

fof(f578,plain,
    ( spl6_50
  <=> k1_xboole_0 = sK5(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f645,plain,
    ( r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f643])).

fof(f643,plain,
    ( spl6_58
  <=> r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f646,plain,
    ( spl6_58
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f555,f357,f161,f117,f643])).

fof(f117,plain,
    ( spl6_6
  <=> r2_hidden(sK5(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f161,plain,
    ( spl6_11
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f357,plain,
    ( spl6_32
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f555,plain,
    ( r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_32 ),
    inference(forward_demodulation,[],[f525,f163])).

fof(f163,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f161])).

fof(f525,plain,
    ( r2_hidden(sK5(sK1,k1_xboole_0),sK1)
    | ~ spl6_6
    | ~ spl6_32 ),
    inference(superposition,[],[f119,f359])).

fof(f359,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f357])).

fof(f119,plain,
    ( r2_hidden(sK5(sK1,sK2),sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f117])).

fof(f583,plain,
    ( spl6_50
    | ~ spl6_11
    | ~ spl6_32
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f582,f569,f357,f161,f578])).

fof(f569,plain,
    ( spl6_48
  <=> k1_xboole_0 = sK5(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f582,plain,
    ( k1_xboole_0 = sK5(k1_xboole_0,k1_xboole_0)
    | ~ spl6_11
    | ~ spl6_32
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f581,f163])).

fof(f581,plain,
    ( k1_xboole_0 = sK5(sK1,k1_xboole_0)
    | ~ spl6_32
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f571,f359])).

fof(f571,plain,
    ( k1_xboole_0 = sK5(sK1,sK2)
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f569])).

fof(f572,plain,
    ( spl6_48
    | ~ spl6_1
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f393,f333,f105,f88,f83,f73,f569])).

fof(f73,plain,
    ( spl6_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f83,plain,
    ( spl6_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f88,plain,
    ( spl6_4
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f105,plain,
    ( spl6_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f333,plain,
    ( spl6_28
  <=> sK5(sK1,sK2) = k1_funct_1(sK2,sK3(sK5(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f393,plain,
    ( k1_xboole_0 = sK5(sK1,sK2)
    | ~ spl6_1
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f392,f114])).

fof(f114,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK5(sK1,sK2)),sK2)
    | ~ spl6_3
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f85,f90,f60])).

fof(f60,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X6,sK5(X1,X2)),X2)
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(sK4(X2,X3),X3),X2)
              | ~ r2_hidden(X3,X1) )
          | k2_relset_1(X0,X1,X2) != X1 )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(X6,sK5(X1,X2)),X2)
            & r2_hidden(sK5(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f31,f33,f32])).

fof(f32,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
     => r2_hidden(k4_tarski(sK4(X2,X3),X3),X2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(X6,sK5(X1,X2)),X2)
        & r2_hidden(sK5(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
              | ~ r2_hidden(X3,X1) )
          | k2_relset_1(X0,X1,X2) != X1 )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ? [X5] :
              ( ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X2)
              & r2_hidden(X5,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
              | ~ r2_hidden(X3,X1) )
          | k2_relset_1(X0,X1,X2) != X1 )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).

fof(f90,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f85,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f392,plain,
    ( r2_hidden(k4_tarski(sK3(sK5(sK1,sK2)),sK5(sK1,sK2)),sK2)
    | k1_xboole_0 = sK5(sK1,sK2)
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_28 ),
    inference(superposition,[],[f155,f335])).

fof(f335,plain,
    ( sK5(sK1,sK2) = k1_funct_1(sK2,sK3(sK5(sK1,sK2)))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f333])).

fof(f155,plain,
    ( ! [X2] :
        ( r2_hidden(k4_tarski(X2,k1_funct_1(sK2,X2)),sK2)
        | k1_xboole_0 = k1_funct_1(sK2,X2) )
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f154,f107])).

fof(f107,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f105])).

fof(f154,plain,
    ( ! [X2] :
        ( k1_xboole_0 = k1_funct_1(sK2,X2)
        | r2_hidden(k4_tarski(X2,k1_funct_1(sK2,X2)),sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f148,f75])).

fof(f75,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f148,plain,
    ( ! [X2] :
        ( k1_xboole_0 = k1_funct_1(sK2,X2)
        | r2_hidden(k4_tarski(X2,k1_funct_1(sK2,X2)),sK2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(resolution,[],[f103,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f103,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_relat_1(sK2))
        | k1_xboole_0 = k1_funct_1(sK2,X0) )
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f102,f94])).

fof(f94,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f46,f85,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f102,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_relat_1(sK2))
        | k1_xboole_0 = k1_funct_1(sK2,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl6_1 ),
    inference(resolution,[],[f62,f75])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | k1_funct_1(X0,X1) = k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f507,plain,
    ( spl6_15
    | ~ spl6_2
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f424,f161,f78,f190])).

fof(f190,plain,
    ( spl6_15
  <=> v1_funct_2(sK2,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f78,plain,
    ( spl6_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f424,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_11 ),
    inference(superposition,[],[f80,f163])).

fof(f80,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f500,plain,
    ( ~ spl6_17
    | spl6_10
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f421,f161,f157,f215])).

fof(f215,plain,
    ( spl6_17
  <=> sK0 = k1_relset_1(sK0,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f157,plain,
    ( spl6_10
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f421,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK2)
    | spl6_10
    | ~ spl6_11 ),
    inference(forward_demodulation,[],[f158,f163])).

fof(f158,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK2)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f157])).

fof(f477,plain,
    ( ~ spl6_3
    | ~ spl6_11
    | ~ spl6_33
    | spl6_38
    | ~ spl6_39 ),
    inference(avatar_contradiction_clause,[],[f476])).

fof(f476,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_11
    | ~ spl6_33
    | spl6_38
    | ~ spl6_39 ),
    inference(subsumption_resolution,[],[f475,f453])).

fof(f453,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_3
    | ~ spl6_11
    | ~ spl6_33 ),
    inference(forward_demodulation,[],[f438,f163])).

fof(f438,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl6_3
    | ~ spl6_33 ),
    inference(superposition,[],[f85,f363])).

fof(f363,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f361])).

fof(f361,plain,
    ( spl6_33
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f475,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl6_38
    | ~ spl6_39 ),
    inference(unit_resulting_resolution,[],[f468,f473,f71])).

fof(f71,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f21])).

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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f473,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f471])).

fof(f471,plain,
    ( spl6_39
  <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f468,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | spl6_38 ),
    inference(avatar_component_clause,[],[f466])).

fof(f466,plain,
    ( spl6_38
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f474,plain,
    ( spl6_39
    | ~ spl6_15
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f420,f361,f190,f471])).

fof(f420,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl6_15
    | ~ spl6_33 ),
    inference(forward_demodulation,[],[f192,f363])).

fof(f192,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f190])).

% (5839)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f469,plain,
    ( ~ spl6_38
    | spl6_17
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f418,f361,f215,f466])).

fof(f418,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | spl6_17
    | ~ spl6_33 ),
    inference(forward_demodulation,[],[f217,f363])).

fof(f217,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK2)
    | spl6_17 ),
    inference(avatar_component_clause,[],[f215])).

fof(f405,plain,
    ( ~ spl6_1
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_16
    | ~ spl6_22
    | ~ spl6_28 ),
    inference(avatar_contradiction_clause,[],[f404])).

fof(f404,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_16
    | ~ spl6_22
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f403,f114])).

fof(f403,plain,
    ( r2_hidden(k4_tarski(sK3(sK5(sK1,sK2)),sK5(sK1,sK2)),sK2)
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_16
    | ~ spl6_22
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f399,f335])).

fof(f399,plain,
    ( r2_hidden(k4_tarski(sK3(sK5(sK1,sK2)),k1_funct_1(sK2,sK3(sK5(sK1,sK2)))),sK2)
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_16
    | ~ spl6_22 ),
    inference(resolution,[],[f384,f281])).

fof(f281,plain,
    ( r2_hidden(sK3(sK5(sK1,sK2)),sK0)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f279])).

fof(f279,plain,
    ( spl6_22
  <=> r2_hidden(sK3(sK5(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f384,plain,
    ( ! [X7] :
        ( ~ r2_hidden(X7,sK0)
        | r2_hidden(k4_tarski(X7,k1_funct_1(sK2,X7)),sK2) )
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f383,f107])).

fof(f383,plain,
    ( ! [X7] :
        ( ~ r2_hidden(X7,sK0)
        | r2_hidden(k4_tarski(X7,k1_funct_1(sK2,X7)),sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl6_1
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f380,f75])).

fof(f380,plain,
    ( ! [X7] :
        ( ~ r2_hidden(X7,sK0)
        | r2_hidden(k4_tarski(X7,k1_funct_1(sK2,X7)),sK2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl6_16 ),
    inference(superposition,[],[f64,f197])).

fof(f197,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl6_16
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f364,plain,
    ( spl6_32
    | spl6_33
    | ~ spl6_15
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f321,f291,f190,f361,f357])).

fof(f291,plain,
    ( spl6_24
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f321,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl6_15
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f315,f192])).

fof(f315,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl6_24 ),
    inference(resolution,[],[f293,f69])).

fof(f69,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f293,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f291])).

fof(f336,plain,
    ( spl6_28
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f121,f117,f333])).

fof(f121,plain,
    ( sK5(sK1,sK2) = k1_funct_1(sK2,sK3(sK5(sK1,sK2)))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f119,f39])).

fof(f39,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | k1_funct_1(sK2,sK3(X3)) = X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    & ! [X3] :
        ( ( k1_funct_1(sK2,sK3(X3)) = X3
          & r2_hidden(sK3(X3),sK0) )
        | ~ r2_hidden(X3,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f24,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(X0,X1,X2) != X1
        & ! [X3] :
            ( ? [X4] :
                ( k1_funct_1(X2,X4) = X3
                & r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( sK1 != k2_relset_1(sK0,sK1,sK2)
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK2,X4) = X3
              & r2_hidden(X4,sK0) )
          | ~ r2_hidden(X3,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X3] :
      ( ? [X4] :
          ( k1_funct_1(sK2,X4) = X3
          & r2_hidden(X4,sK0) )
     => ( k1_funct_1(sK2,sK3(X3)) = X3
        & r2_hidden(sK3(X3),sK0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

fof(f294,plain,
    ( spl6_24
    | ~ spl6_3
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f261,f161,f83,f291])).

fof(f261,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_3
    | ~ spl6_11 ),
    inference(superposition,[],[f85,f163])).

fof(f282,plain,
    ( spl6_22
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f122,f117,f279])).

fof(f122,plain,
    ( r2_hidden(sK3(sK5(sK1,sK2)),sK0)
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f119,f38])).

fof(f38,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f204,plain,
    ( spl6_16
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f200,f157,f128,f195])).

fof(f128,plain,
    ( spl6_7
  <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f200,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(superposition,[],[f159,f130])).

fof(f130,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f128])).

fof(f159,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f157])).

fof(f164,plain,
    ( spl6_10
    | spl6_11
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f112,f83,f78,f161,f157])).

fof(f112,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f111,f80])).

fof(f111,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl6_3 ),
    inference(resolution,[],[f53,f85])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f131,plain,
    ( spl6_7
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f98,f83,f128])).

fof(f98,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f85,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f120,plain,
    ( spl6_6
    | ~ spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f109,f88,f83,f117])).

fof(f109,plain,
    ( r2_hidden(sK5(sK1,sK2),sK1)
    | ~ spl6_3
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f90,f85,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK5(X1,X2),X1)
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f108,plain,
    ( spl6_5
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f94,f83,f105])).

fof(f91,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f40,f88])).

fof(f40,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f86,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f37,f83])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f81,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f36,f78])).

fof(f36,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f35,f73])).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:47:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.46  % (5862)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.46  % (5846)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.46  % (5846)Refutation not found, incomplete strategy% (5846)------------------------------
% 0.21/0.46  % (5846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (5846)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (5846)Memory used [KB]: 1663
% 0.21/0.46  % (5846)Time elapsed: 0.044 s
% 0.21/0.46  % (5846)------------------------------
% 0.21/0.46  % (5846)------------------------------
% 0.21/0.48  % (5862)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f650,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f76,f81,f86,f91,f108,f120,f131,f164,f204,f282,f294,f336,f364,f405,f469,f474,f477,f500,f507,f572,f583,f646,f649])).
% 0.21/0.48  fof(f649,plain,(
% 0.21/0.48    ~spl6_50 | ~spl6_58),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f648])).
% 0.21/0.48  fof(f648,plain,(
% 0.21/0.48    $false | (~spl6_50 | ~spl6_58)),
% 0.21/0.48    inference(subsumption_resolution,[],[f647,f92])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,X0)) )),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f65,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.48    inference(flattening,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.48  fof(f647,plain,(
% 0.21/0.48    r2_hidden(k1_xboole_0,k1_xboole_0) | (~spl6_50 | ~spl6_58)),
% 0.21/0.48    inference(forward_demodulation,[],[f645,f580])).
% 0.21/0.48  fof(f580,plain,(
% 0.21/0.48    k1_xboole_0 = sK5(k1_xboole_0,k1_xboole_0) | ~spl6_50),
% 0.21/0.48    inference(avatar_component_clause,[],[f578])).
% 0.21/0.48  fof(f578,plain,(
% 0.21/0.48    spl6_50 <=> k1_xboole_0 = sK5(k1_xboole_0,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).
% 0.21/0.48  fof(f645,plain,(
% 0.21/0.48    r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~spl6_58),
% 0.21/0.48    inference(avatar_component_clause,[],[f643])).
% 0.21/0.48  fof(f643,plain,(
% 0.21/0.48    spl6_58 <=> r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).
% 0.21/0.48  fof(f646,plain,(
% 0.21/0.48    spl6_58 | ~spl6_6 | ~spl6_11 | ~spl6_32),
% 0.21/0.48    inference(avatar_split_clause,[],[f555,f357,f161,f117,f643])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    spl6_6 <=> r2_hidden(sK5(sK1,sK2),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    spl6_11 <=> k1_xboole_0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.48  fof(f357,plain,(
% 0.21/0.48    spl6_32 <=> k1_xboole_0 = sK2),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.21/0.48  fof(f555,plain,(
% 0.21/0.48    r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0) | (~spl6_6 | ~spl6_11 | ~spl6_32)),
% 0.21/0.48    inference(forward_demodulation,[],[f525,f163])).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | ~spl6_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f161])).
% 0.21/0.48  fof(f525,plain,(
% 0.21/0.48    r2_hidden(sK5(sK1,k1_xboole_0),sK1) | (~spl6_6 | ~spl6_32)),
% 0.21/0.48    inference(superposition,[],[f119,f359])).
% 0.21/0.48  fof(f359,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | ~spl6_32),
% 0.21/0.48    inference(avatar_component_clause,[],[f357])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    r2_hidden(sK5(sK1,sK2),sK1) | ~spl6_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f117])).
% 0.21/0.48  fof(f583,plain,(
% 0.21/0.48    spl6_50 | ~spl6_11 | ~spl6_32 | ~spl6_48),
% 0.21/0.48    inference(avatar_split_clause,[],[f582,f569,f357,f161,f578])).
% 0.21/0.48  fof(f569,plain,(
% 0.21/0.48    spl6_48 <=> k1_xboole_0 = sK5(sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 0.21/0.48  fof(f582,plain,(
% 0.21/0.48    k1_xboole_0 = sK5(k1_xboole_0,k1_xboole_0) | (~spl6_11 | ~spl6_32 | ~spl6_48)),
% 0.21/0.48    inference(forward_demodulation,[],[f581,f163])).
% 0.21/0.48  fof(f581,plain,(
% 0.21/0.48    k1_xboole_0 = sK5(sK1,k1_xboole_0) | (~spl6_32 | ~spl6_48)),
% 0.21/0.48    inference(forward_demodulation,[],[f571,f359])).
% 0.21/0.48  fof(f571,plain,(
% 0.21/0.48    k1_xboole_0 = sK5(sK1,sK2) | ~spl6_48),
% 0.21/0.48    inference(avatar_component_clause,[],[f569])).
% 0.21/0.48  fof(f572,plain,(
% 0.21/0.48    spl6_48 | ~spl6_1 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_28),
% 0.21/0.48    inference(avatar_split_clause,[],[f393,f333,f105,f88,f83,f73,f569])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    spl6_1 <=> v1_funct_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    spl6_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    spl6_4 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    spl6_5 <=> v1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.48  fof(f333,plain,(
% 0.21/0.48    spl6_28 <=> sK5(sK1,sK2) = k1_funct_1(sK2,sK3(sK5(sK1,sK2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.21/0.48  fof(f393,plain,(
% 0.21/0.48    k1_xboole_0 = sK5(sK1,sK2) | (~spl6_1 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_28)),
% 0.21/0.48    inference(subsumption_resolution,[],[f392,f114])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK5(sK1,sK2)),sK2)) ) | (~spl6_3 | spl6_4)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f85,f90,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X6,X2,X0,X1] : (~r2_hidden(k4_tarski(X6,sK5(X1,X2)),X2) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(sK4(X2,X3),X3),X2) | ~r2_hidden(X3,X1)) | k2_relset_1(X0,X1,X2) != X1) & (k2_relset_1(X0,X1,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(X6,sK5(X1,X2)),X2) & r2_hidden(sK5(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f31,f33,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) => r2_hidden(k4_tarski(sK4(X2,X3),X3),X2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X6,X5),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(X6,sK5(X1,X2)),X2) & r2_hidden(sK5(X1,X2),X1)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) | k2_relset_1(X0,X1,X2) != X1) & (k2_relset_1(X0,X1,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X6,X5),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(rectify,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) | k2_relset_1(X0,X1,X2) != X1) & (k2_relset_1(X0,X1,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(nnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    sK1 != k2_relset_1(sK0,sK1,sK2) | spl6_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f88])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f83])).
% 0.21/0.48  fof(f392,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(sK3(sK5(sK1,sK2)),sK5(sK1,sK2)),sK2) | k1_xboole_0 = sK5(sK1,sK2) | (~spl6_1 | ~spl6_3 | ~spl6_5 | ~spl6_28)),
% 0.21/0.48    inference(superposition,[],[f155,f335])).
% 0.21/0.48  fof(f335,plain,(
% 0.21/0.48    sK5(sK1,sK2) = k1_funct_1(sK2,sK3(sK5(sK1,sK2))) | ~spl6_28),
% 0.21/0.48    inference(avatar_component_clause,[],[f333])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    ( ! [X2] : (r2_hidden(k4_tarski(X2,k1_funct_1(sK2,X2)),sK2) | k1_xboole_0 = k1_funct_1(sK2,X2)) ) | (~spl6_1 | ~spl6_3 | ~spl6_5)),
% 0.21/0.48    inference(subsumption_resolution,[],[f154,f107])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    v1_relat_1(sK2) | ~spl6_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f105])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    ( ! [X2] : (k1_xboole_0 = k1_funct_1(sK2,X2) | r2_hidden(k4_tarski(X2,k1_funct_1(sK2,X2)),sK2) | ~v1_relat_1(sK2)) ) | (~spl6_1 | ~spl6_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f148,f75])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    v1_funct_1(sK2) | ~spl6_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f73])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    ( ! [X2] : (k1_xboole_0 = k1_funct_1(sK2,X2) | r2_hidden(k4_tarski(X2,k1_funct_1(sK2,X2)),sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | (~spl6_1 | ~spl6_3)),
% 0.21/0.48    inference(resolution,[],[f103,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(X0)) | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2 | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(X0,k1_relat_1(sK2)) | k1_xboole_0 = k1_funct_1(sK2,X0)) ) | (~spl6_1 | ~spl6_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f102,f94])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    v1_relat_1(sK2) | ~spl6_3),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f46,f85,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(X0,k1_relat_1(sK2)) | k1_xboole_0 = k1_funct_1(sK2,X0) | ~v1_relat_1(sK2)) ) | ~spl6_1),
% 0.21/0.48    inference(resolution,[],[f62,f75])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_funct_1(X0) | r2_hidden(X1,k1_relat_1(X0)) | k1_funct_1(X0,X1) = k1_xboole_0 | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f507,plain,(
% 0.21/0.48    spl6_15 | ~spl6_2 | ~spl6_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f424,f161,f78,f190])).
% 0.21/0.48  fof(f190,plain,(
% 0.21/0.48    spl6_15 <=> v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    spl6_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.48  fof(f424,plain,(
% 0.21/0.48    v1_funct_2(sK2,sK0,k1_xboole_0) | (~spl6_2 | ~spl6_11)),
% 0.21/0.48    inference(superposition,[],[f80,f163])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    v1_funct_2(sK2,sK0,sK1) | ~spl6_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f78])).
% 0.21/0.48  fof(f500,plain,(
% 0.21/0.48    ~spl6_17 | spl6_10 | ~spl6_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f421,f161,f157,f215])).
% 0.21/0.48  fof(f215,plain,(
% 0.21/0.48    spl6_17 <=> sK0 = k1_relset_1(sK0,k1_xboole_0,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    spl6_10 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.48  fof(f421,plain,(
% 0.21/0.48    sK0 != k1_relset_1(sK0,k1_xboole_0,sK2) | (spl6_10 | ~spl6_11)),
% 0.21/0.48    inference(forward_demodulation,[],[f158,f163])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    sK0 != k1_relset_1(sK0,sK1,sK2) | spl6_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f157])).
% 0.21/0.48  fof(f477,plain,(
% 0.21/0.48    ~spl6_3 | ~spl6_11 | ~spl6_33 | spl6_38 | ~spl6_39),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f476])).
% 0.21/0.48  fof(f476,plain,(
% 0.21/0.48    $false | (~spl6_3 | ~spl6_11 | ~spl6_33 | spl6_38 | ~spl6_39)),
% 0.21/0.48    inference(subsumption_resolution,[],[f475,f453])).
% 0.21/0.48  fof(f453,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl6_3 | ~spl6_11 | ~spl6_33)),
% 0.21/0.48    inference(forward_demodulation,[],[f438,f163])).
% 0.21/0.48  fof(f438,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl6_3 | ~spl6_33)),
% 0.21/0.48    inference(superposition,[],[f85,f363])).
% 0.21/0.48  fof(f363,plain,(
% 0.21/0.48    k1_xboole_0 = sK0 | ~spl6_33),
% 0.21/0.48    inference(avatar_component_clause,[],[f361])).
% 0.21/0.48  fof(f361,plain,(
% 0.21/0.48    spl6_33 <=> k1_xboole_0 = sK0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.21/0.48  fof(f475,plain,(
% 0.21/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (spl6_38 | ~spl6_39)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f468,f473,f71])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.21/0.48    inference(equality_resolution,[],[f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(nnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.48  fof(f473,plain,(
% 0.21/0.48    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~spl6_39),
% 0.21/0.48    inference(avatar_component_clause,[],[f471])).
% 0.21/0.48  fof(f471,plain,(
% 0.21/0.48    spl6_39 <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 0.21/0.48  fof(f468,plain,(
% 0.21/0.48    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | spl6_38),
% 0.21/0.48    inference(avatar_component_clause,[],[f466])).
% 0.21/0.48  fof(f466,plain,(
% 0.21/0.48    spl6_38 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 0.21/0.48  fof(f474,plain,(
% 0.21/0.48    spl6_39 | ~spl6_15 | ~spl6_33),
% 0.21/0.48    inference(avatar_split_clause,[],[f420,f361,f190,f471])).
% 0.21/0.48  fof(f420,plain,(
% 0.21/0.48    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl6_15 | ~spl6_33)),
% 0.21/0.48    inference(forward_demodulation,[],[f192,f363])).
% 0.21/0.48  fof(f192,plain,(
% 0.21/0.48    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl6_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f190])).
% 0.21/0.48  % (5839)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.48  fof(f469,plain,(
% 0.21/0.48    ~spl6_38 | spl6_17 | ~spl6_33),
% 0.21/0.48    inference(avatar_split_clause,[],[f418,f361,f215,f466])).
% 0.21/0.48  fof(f418,plain,(
% 0.21/0.48    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (spl6_17 | ~spl6_33)),
% 0.21/0.48    inference(forward_demodulation,[],[f217,f363])).
% 0.21/0.48  fof(f217,plain,(
% 0.21/0.48    sK0 != k1_relset_1(sK0,k1_xboole_0,sK2) | spl6_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f215])).
% 0.21/0.48  fof(f405,plain,(
% 0.21/0.48    ~spl6_1 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_16 | ~spl6_22 | ~spl6_28),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f404])).
% 0.21/0.48  fof(f404,plain,(
% 0.21/0.48    $false | (~spl6_1 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_16 | ~spl6_22 | ~spl6_28)),
% 0.21/0.48    inference(subsumption_resolution,[],[f403,f114])).
% 0.21/0.48  fof(f403,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(sK3(sK5(sK1,sK2)),sK5(sK1,sK2)),sK2) | (~spl6_1 | ~spl6_5 | ~spl6_16 | ~spl6_22 | ~spl6_28)),
% 0.21/0.48    inference(forward_demodulation,[],[f399,f335])).
% 0.21/0.48  fof(f399,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(sK3(sK5(sK1,sK2)),k1_funct_1(sK2,sK3(sK5(sK1,sK2)))),sK2) | (~spl6_1 | ~spl6_5 | ~spl6_16 | ~spl6_22)),
% 0.21/0.48    inference(resolution,[],[f384,f281])).
% 0.21/0.48  fof(f281,plain,(
% 0.21/0.48    r2_hidden(sK3(sK5(sK1,sK2)),sK0) | ~spl6_22),
% 0.21/0.48    inference(avatar_component_clause,[],[f279])).
% 0.21/0.48  fof(f279,plain,(
% 0.21/0.48    spl6_22 <=> r2_hidden(sK3(sK5(sK1,sK2)),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.21/0.48  fof(f384,plain,(
% 0.21/0.48    ( ! [X7] : (~r2_hidden(X7,sK0) | r2_hidden(k4_tarski(X7,k1_funct_1(sK2,X7)),sK2)) ) | (~spl6_1 | ~spl6_5 | ~spl6_16)),
% 0.21/0.48    inference(subsumption_resolution,[],[f383,f107])).
% 0.21/0.48  fof(f383,plain,(
% 0.21/0.48    ( ! [X7] : (~r2_hidden(X7,sK0) | r2_hidden(k4_tarski(X7,k1_funct_1(sK2,X7)),sK2) | ~v1_relat_1(sK2)) ) | (~spl6_1 | ~spl6_16)),
% 0.21/0.48    inference(subsumption_resolution,[],[f380,f75])).
% 0.21/0.48  fof(f380,plain,(
% 0.21/0.48    ( ! [X7] : (~r2_hidden(X7,sK0) | r2_hidden(k4_tarski(X7,k1_funct_1(sK2,X7)),sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl6_16),
% 0.21/0.48    inference(superposition,[],[f64,f197])).
% 0.21/0.48  fof(f197,plain,(
% 0.21/0.48    sK0 = k1_relat_1(sK2) | ~spl6_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f195])).
% 0.21/0.48  fof(f195,plain,(
% 0.21/0.48    spl6_16 <=> sK0 = k1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.48  fof(f364,plain,(
% 0.21/0.48    spl6_32 | spl6_33 | ~spl6_15 | ~spl6_24),
% 0.21/0.48    inference(avatar_split_clause,[],[f321,f291,f190,f361,f357])).
% 0.21/0.48  fof(f291,plain,(
% 0.21/0.48    spl6_24 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.21/0.48  fof(f321,plain,(
% 0.21/0.48    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | (~spl6_15 | ~spl6_24)),
% 0.21/0.48    inference(subsumption_resolution,[],[f315,f192])).
% 0.21/0.48  fof(f315,plain,(
% 0.21/0.48    ~v1_funct_2(sK2,sK0,k1_xboole_0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl6_24),
% 0.21/0.48    inference(resolution,[],[f293,f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 0.21/0.48    inference(equality_resolution,[],[f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f293,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl6_24),
% 0.21/0.48    inference(avatar_component_clause,[],[f291])).
% 0.21/0.48  fof(f336,plain,(
% 0.21/0.48    spl6_28 | ~spl6_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f121,f117,f333])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    sK5(sK1,sK2) = k1_funct_1(sK2,sK3(sK5(sK1,sK2))) | ~spl6_6),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f119,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X3] : (~r2_hidden(X3,sK1) | k1_funct_1(sK2,sK3(X3)) = X3) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    sK1 != k2_relset_1(sK0,sK1,sK2) & ! [X3] : ((k1_funct_1(sK2,sK3(X3)) = X3 & r2_hidden(sK3(X3),sK0)) | ~r2_hidden(X3,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f24,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (sK1 != k2_relset_1(sK0,sK1,sK2) & ! [X3] : (? [X4] : (k1_funct_1(sK2,X4) = X3 & r2_hidden(X4,sK0)) | ~r2_hidden(X3,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X3] : (? [X4] : (k1_funct_1(sK2,X4) = X3 & r2_hidden(X4,sK0)) => (k1_funct_1(sK2,sK3(X3)) = X3 & r2_hidden(sK3(X3),sK0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.48    inference(negated_conjecture,[],[f10])).
% 0.21/0.48  fof(f10,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).
% 0.21/0.48  fof(f294,plain,(
% 0.21/0.48    spl6_24 | ~spl6_3 | ~spl6_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f261,f161,f83,f291])).
% 0.21/0.48  fof(f261,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl6_3 | ~spl6_11)),
% 0.21/0.48    inference(superposition,[],[f85,f163])).
% 0.21/0.48  fof(f282,plain,(
% 0.21/0.48    spl6_22 | ~spl6_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f122,f117,f279])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    r2_hidden(sK3(sK5(sK1,sK2)),sK0) | ~spl6_6),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f119,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f204,plain,(
% 0.21/0.48    spl6_16 | ~spl6_7 | ~spl6_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f200,f157,f128,f195])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    spl6_7 <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.48  fof(f200,plain,(
% 0.21/0.48    sK0 = k1_relat_1(sK2) | (~spl6_7 | ~spl6_10)),
% 0.21/0.48    inference(superposition,[],[f159,f130])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl6_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f128])).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl6_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f157])).
% 0.21/0.48  fof(f164,plain,(
% 0.21/0.48    spl6_10 | spl6_11 | ~spl6_2 | ~spl6_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f112,f83,f78,f161,f157])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl6_2 | ~spl6_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f111,f80])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl6_3),
% 0.21/0.48    inference(resolution,[],[f53,f85])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    spl6_7 | ~spl6_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f98,f83,f128])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl6_3),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f85,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    spl6_6 | ~spl6_3 | spl6_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f109,f88,f83,f117])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    r2_hidden(sK5(sK1,sK2),sK1) | (~spl6_3 | spl6_4)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f90,f85,f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK5(X1,X2),X1) | k2_relset_1(X0,X1,X2) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    spl6_5 | ~spl6_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f94,f83,f105])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ~spl6_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f40,f88])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    spl6_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f37,f83])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    spl6_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f36,f78])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    spl6_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f35,f73])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    v1_funct_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (5862)------------------------------
% 0.21/0.48  % (5862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (5862)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (5862)Memory used [KB]: 11001
% 0.21/0.48  % (5862)Time elapsed: 0.072 s
% 0.21/0.48  % (5862)------------------------------
% 0.21/0.48  % (5862)------------------------------
% 0.21/0.48  % (5839)Refutation not found, incomplete strategy% (5839)------------------------------
% 0.21/0.48  % (5839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (5838)Success in time 0.127 s
%------------------------------------------------------------------------------
