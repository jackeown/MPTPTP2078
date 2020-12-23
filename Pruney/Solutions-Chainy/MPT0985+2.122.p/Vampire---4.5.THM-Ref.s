%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:18 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 598 expanded)
%              Number of leaves         :   31 ( 176 expanded)
%              Depth                    :   20
%              Number of atoms          :  584 (2766 expanded)
%              Number of equality atoms :  106 ( 567 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f673,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f146,f149,f350,f435,f540,f542,f590,f605,f628,f641,f652,f668,f672])).

fof(f672,plain,
    ( ~ spl7_7
    | ~ spl7_25
    | ~ spl7_6
    | spl7_31 ),
    inference(avatar_split_clause,[],[f671,f665,f132,f594,f136])).

fof(f136,plain,
    ( spl7_7
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f594,plain,
    ( spl7_25
  <=> v2_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f132,plain,
    ( spl7_6
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f665,plain,
    ( spl7_31
  <=> k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f671,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl7_6
    | spl7_31 ),
    inference(subsumption_resolution,[],[f670,f133])).

fof(f133,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f132])).

fof(f670,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl7_31 ),
    inference(subsumption_resolution,[],[f669,f58])).

fof(f58,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f669,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl7_31 ),
    inference(superposition,[],[f667,f67])).

fof(f67,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f667,plain,
    ( k1_xboole_0 != k1_relat_1(k2_funct_1(k1_xboole_0))
    | spl7_31 ),
    inference(avatar_component_clause,[],[f665])).

fof(f668,plain,
    ( ~ spl7_31
    | ~ spl7_27
    | spl7_2
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f663,f385,f102,f602,f665])).

fof(f602,plain,
    ( spl7_27
  <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f102,plain,
    ( spl7_2
  <=> v1_funct_2(k2_funct_1(sK6),sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f385,plain,
    ( spl7_22
  <=> sP1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f663,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k1_relat_1(k2_funct_1(k1_xboole_0))
    | spl7_2
    | ~ spl7_22 ),
    inference(resolution,[],[f658,f471])).

fof(f471,plain,(
    ! [X2,X3] :
      ( v1_funct_2(X3,k1_xboole_0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != k1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f468,f96])).

fof(f96,plain,(
    ! [X1] : ~ sP1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f468,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X3,k1_xboole_0,X2)
      | sP1(k1_xboole_0,X2)
      | k1_xboole_0 != k1_relat_1(X3) ) ),
    inference(superposition,[],[f325,f92])).

fof(f92,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f325,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | v1_funct_2(X5,X3,X4)
      | sP1(X3,X4)
      | k1_relat_1(X5) != X3 ) ),
    inference(subsumption_resolution,[],[f323,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X2,X1,X0)
        & sP2(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f29,f36,f35,f34])).

fof(f35,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP3(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f323,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) != X3
      | v1_funct_2(X5,X3,X4)
      | sP1(X3,X4)
      | ~ sP2(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f83,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) != X0
      | v1_funct_2(X1,X0,X2)
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f658,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK4)
    | spl7_2
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f657,f572])).

fof(f572,plain,
    ( k1_xboole_0 = sK6
    | ~ spl7_22 ),
    inference(resolution,[],[f561,f154])).

fof(f154,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f71,f59])).

fof(f59,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f561,plain,
    ( r1_tarski(sK6,k1_xboole_0)
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f549,f91])).

fof(f91,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f549,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK4,k1_xboole_0))
    | ~ spl7_22 ),
    inference(backward_demodulation,[],[f113,f543])).

fof(f543,plain,
    ( k1_xboole_0 = sK5
    | ~ spl7_22 ),
    inference(resolution,[],[f387,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f387,plain,
    ( sP1(sK4,sK5)
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f385])).

fof(f113,plain,(
    r1_tarski(sK6,k2_zfmisc_1(sK4,sK5)) ),
    inference(resolution,[],[f72,f53])).

fof(f53,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
      | ~ v1_funct_2(k2_funct_1(sK6),sK5,sK4)
      | ~ v1_funct_1(k2_funct_1(sK6)) )
    & sK5 = k2_relset_1(sK4,sK5,sK6)
    & v2_funct_1(sK6)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK6,sK4,sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f18,f38])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
        | ~ v1_funct_2(k2_funct_1(sK6),sK5,sK4)
        | ~ v1_funct_1(k2_funct_1(sK6)) )
      & sK5 = k2_relset_1(sK4,sK5,sK6)
      & v2_funct_1(sK6)
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK6,sK4,sK5)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
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

fof(f657,plain,
    ( ~ v1_funct_2(k2_funct_1(sK6),k1_xboole_0,sK4)
    | spl7_2
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f104,f543])).

fof(f104,plain,
    ( ~ v1_funct_2(k2_funct_1(sK6),sK5,sK4)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f652,plain,
    ( ~ spl7_27
    | spl7_3
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f651,f385,f106,f602])).

fof(f106,plain,
    ( spl7_3
  <=> m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f651,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl7_3
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f560,f572])).

fof(f560,plain,
    ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k1_xboole_0))
    | spl7_3
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f548,f92])).

fof(f548,plain,
    ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4)))
    | spl7_3
    | ~ spl7_22 ),
    inference(backward_demodulation,[],[f108,f543])).

fof(f108,plain,
    ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f641,plain,
    ( spl7_26
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f582,f385,f337,f598])).

fof(f598,plain,
    ( spl7_26
  <=> sP0(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f337,plain,
    ( spl7_19
  <=> sP0(k2_funct_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f582,plain,
    ( sP0(k2_funct_1(k1_xboole_0))
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(backward_demodulation,[],[f338,f572])).

fof(f338,plain,
    ( sP0(k2_funct_1(sK6))
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f337])).

fof(f628,plain,
    ( spl7_25
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f578,f385,f594])).

fof(f578,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ spl7_22 ),
    inference(backward_demodulation,[],[f54,f572])).

fof(f54,plain,(
    v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f39])).

fof(f605,plain,
    ( ~ spl7_7
    | ~ spl7_25
    | ~ spl7_26
    | spl7_27
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f592,f132,f602,f598,f594,f136])).

fof(f592,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ sP0(k2_funct_1(k1_xboole_0))
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f591,f92])).

fof(f591,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0)))))
    | ~ sP0(k2_funct_1(k1_xboole_0))
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f506,f133])).

fof(f506,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0)))))
    | ~ sP0(k2_funct_1(k1_xboole_0))
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f226,f58])).

% (18213)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% (18211)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% (18199)Refutation not found, incomplete strategy% (18199)------------------------------
% (18199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (18199)Termination reason: Refutation not found, incomplete strategy

% (18199)Memory used [KB]: 6396
% (18199)Time elapsed: 0.127 s
% (18199)------------------------------
% (18199)------------------------------
% (18194)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% (18202)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% (18214)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% (18200)Termination reason: Refutation not found, incomplete strategy
% (18203)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% (18195)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% (18205)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% (18195)Refutation not found, incomplete strategy% (18195)------------------------------
% (18195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f226,plain,(
    ! [X3] :
      ( m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X3),k2_relat_1(k2_funct_1(X3)))))
      | ~ sP0(k2_funct_1(X3))
      | ~ v2_funct_1(X3)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f63,f67])).

fof(f63,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f590,plain,
    ( spl7_7
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f577,f385,f136])).

fof(f577,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl7_22 ),
    inference(backward_demodulation,[],[f51,f572])).

fof(f51,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f39])).

fof(f542,plain,
    ( spl7_21
    | spl7_22 ),
    inference(avatar_split_clause,[],[f541,f385,f381])).

fof(f381,plain,
    ( spl7_21
  <=> sK4 = k1_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f541,plain,
    ( sP1(sK4,sK5)
    | sK4 = k1_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f450,f52])).

fof(f52,plain,(
    v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f450,plain,
    ( sP1(sK4,sK5)
    | sK4 = k1_relat_1(sK6)
    | ~ v1_funct_2(sK6,sK4,sK5) ),
    inference(resolution,[],[f376,f113])).

fof(f376,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X3,k2_zfmisc_1(X4,X5))
      | sP1(X4,X5)
      | k1_relat_1(X3) = X4
      | ~ v1_funct_2(X3,X4,X5) ) ),
    inference(resolution,[],[f307,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f307,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP1(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f305,f86])).

fof(f305,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP1(X3,X4)
      | ~ sP2(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f82,f78])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f540,plain,
    ( spl7_3
    | ~ spl7_19
    | ~ spl7_21 ),
    inference(avatar_contradiction_clause,[],[f539])).

fof(f539,plain,
    ( $false
    | spl7_3
    | ~ spl7_19
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f538,f108])).

fof(f538,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ spl7_19
    | ~ spl7_21 ),
    inference(forward_demodulation,[],[f537,f383])).

fof(f383,plain,
    ( sK4 = k1_relat_1(sK6)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f381])).

fof(f537,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,k1_relat_1(sK6))))
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f536,f140])).

fof(f140,plain,(
    v1_relat_1(sK6) ),
    inference(resolution,[],[f77,f53])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f536,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,k1_relat_1(sK6))))
    | ~ v1_relat_1(sK6)
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f535,f51])).

fof(f535,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,k1_relat_1(sK6))))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f524,f54])).

fof(f524,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,k1_relat_1(sK6))))
    | ~ v2_funct_1(sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ spl7_19 ),
    inference(superposition,[],[f516,f68])).

fof(f68,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f516,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,k2_relat_1(k2_funct_1(sK6)))))
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f515,f140])).

fof(f515,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,k2_relat_1(k2_funct_1(sK6)))))
    | ~ v1_relat_1(sK6)
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f514,f51])).

fof(f514,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,k2_relat_1(k2_funct_1(sK6)))))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f513,f54])).

fof(f513,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,k2_relat_1(k2_funct_1(sK6)))))
    | ~ v2_funct_1(sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f508,f338])).

fof(f508,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,k2_relat_1(k2_funct_1(sK6)))))
    | ~ sP0(k2_funct_1(sK6))
    | ~ v2_funct_1(sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6) ),
    inference(superposition,[],[f226,f239])).

fof(f239,plain,(
    sK5 = k2_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f237,f53])).

fof(f237,plain,
    ( sK5 = k2_relat_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(superposition,[],[f79,f55])).

fof(f55,plain,(
    sK5 = k2_relset_1(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f39])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f435,plain,
    ( spl7_2
    | ~ spl7_19
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f432,f381,f337,f102])).

fof(f432,plain,
    ( v1_funct_2(k2_funct_1(sK6),sK5,sK4)
    | ~ spl7_19
    | ~ spl7_21 ),
    inference(forward_demodulation,[],[f431,f239])).

fof(f431,plain,
    ( v1_funct_2(k2_funct_1(sK6),k2_relat_1(sK6),sK4)
    | ~ spl7_19
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f430,f140])).

fof(f430,plain,
    ( v1_funct_2(k2_funct_1(sK6),k2_relat_1(sK6),sK4)
    | ~ v1_relat_1(sK6)
    | ~ spl7_19
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f429,f51])).

fof(f429,plain,
    ( v1_funct_2(k2_funct_1(sK6),k2_relat_1(sK6),sK4)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ spl7_19
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f428,f54])).

fof(f428,plain,
    ( v1_funct_2(k2_funct_1(sK6),k2_relat_1(sK6),sK4)
    | ~ v2_funct_1(sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ spl7_19
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f407,f338])).

fof(f407,plain,
    ( v1_funct_2(k2_funct_1(sK6),k2_relat_1(sK6),sK4)
    | ~ sP0(k2_funct_1(sK6))
    | ~ v2_funct_1(sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ spl7_21 ),
    inference(superposition,[],[f330,f383])).

fof(f330,plain,(
    ! [X0] :
      ( v1_funct_2(k2_funct_1(X0),k2_relat_1(X0),k1_relat_1(X0))
      | ~ sP0(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f329])).

fof(f329,plain,(
    ! [X0] :
      ( v1_funct_2(k2_funct_1(X0),k2_relat_1(X0),k1_relat_1(X0))
      | ~ sP0(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f227,f68])).

fof(f227,plain,(
    ! [X4] :
      ( v1_funct_2(k2_funct_1(X4),k2_relat_1(X4),k2_relat_1(k2_funct_1(X4)))
      | ~ sP0(k2_funct_1(X4))
      | ~ v2_funct_1(X4)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f62,f67])).

fof(f62,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f350,plain,
    ( ~ spl7_1
    | spl7_19 ),
    inference(avatar_contradiction_clause,[],[f349])).

fof(f349,plain,
    ( $false
    | ~ spl7_1
    | spl7_19 ),
    inference(subsumption_resolution,[],[f348,f140])).

fof(f348,plain,
    ( ~ v1_relat_1(sK6)
    | ~ spl7_1
    | spl7_19 ),
    inference(subsumption_resolution,[],[f347,f51])).

fof(f347,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ spl7_1
    | spl7_19 ),
    inference(resolution,[],[f346,f65])).

fof(f65,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f346,plain,
    ( ~ v1_relat_1(k2_funct_1(sK6))
    | ~ spl7_1
    | spl7_19 ),
    inference(subsumption_resolution,[],[f345,f99])).

fof(f99,plain,
    ( v1_funct_1(k2_funct_1(sK6))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl7_1
  <=> v1_funct_1(k2_funct_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f345,plain,
    ( ~ v1_funct_1(k2_funct_1(sK6))
    | ~ v1_relat_1(k2_funct_1(sK6))
    | spl7_19 ),
    inference(resolution,[],[f339,f64])).

fof(f64,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f20,f32])).

fof(f20,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f339,plain,
    ( ~ sP0(k2_funct_1(sK6))
    | spl7_19 ),
    inference(avatar_component_clause,[],[f337])).

fof(f149,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f141,f132])).

fof(f141,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f77,f60])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f146,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | spl7_1 ),
    inference(subsumption_resolution,[],[f140,f112])).

fof(f112,plain,
    ( ~ v1_relat_1(sK6)
    | spl7_1 ),
    inference(subsumption_resolution,[],[f111,f51])).

fof(f111,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl7_1 ),
    inference(resolution,[],[f66,f100])).

fof(f100,plain,
    ( ~ v1_funct_1(k2_funct_1(sK6))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f98])).

fof(f66,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f109,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f56,f106,f102,f98])).

fof(f56,plain,
    ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(k2_funct_1(sK6),sK5,sK4)
    | ~ v1_funct_1(k2_funct_1(sK6)) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:50:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (18217)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.52  % (18209)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.53  % (18198)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.53  % (18201)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.54  % (18204)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.54  % (18215)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.39/0.54  % (18197)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.39/0.54  % (18200)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.39/0.54  % (18219)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.39/0.54  % (18206)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.39/0.54  % (18212)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.39/0.54  % (18196)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.39/0.55  % (18208)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.39/0.55  % (18210)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.39/0.55  % (18200)Refutation not found, incomplete strategy% (18200)------------------------------
% 1.39/0.55  % (18200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (18199)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.39/0.55  % (18207)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.39/0.55  % (18216)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.39/0.55  % (18198)Refutation found. Thanks to Tanya!
% 1.39/0.55  % SZS status Theorem for theBenchmark
% 1.39/0.55  % SZS output start Proof for theBenchmark
% 1.39/0.55  fof(f673,plain,(
% 1.39/0.55    $false),
% 1.39/0.55    inference(avatar_sat_refutation,[],[f109,f146,f149,f350,f435,f540,f542,f590,f605,f628,f641,f652,f668,f672])).
% 1.39/0.55  fof(f672,plain,(
% 1.39/0.55    ~spl7_7 | ~spl7_25 | ~spl7_6 | spl7_31),
% 1.39/0.55    inference(avatar_split_clause,[],[f671,f665,f132,f594,f136])).
% 1.39/0.55  fof(f136,plain,(
% 1.39/0.55    spl7_7 <=> v1_funct_1(k1_xboole_0)),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.39/0.55  fof(f594,plain,(
% 1.39/0.55    spl7_25 <=> v2_funct_1(k1_xboole_0)),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 1.39/0.55  fof(f132,plain,(
% 1.39/0.55    spl7_6 <=> v1_relat_1(k1_xboole_0)),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.39/0.55  fof(f665,plain,(
% 1.39/0.55    spl7_31 <=> k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 1.39/0.55  fof(f671,plain,(
% 1.39/0.55    ~v2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | (~spl7_6 | spl7_31)),
% 1.39/0.55    inference(subsumption_resolution,[],[f670,f133])).
% 1.39/0.55  fof(f133,plain,(
% 1.39/0.55    v1_relat_1(k1_xboole_0) | ~spl7_6),
% 1.39/0.55    inference(avatar_component_clause,[],[f132])).
% 1.39/0.55  fof(f670,plain,(
% 1.39/0.55    ~v2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | spl7_31),
% 1.39/0.55    inference(subsumption_resolution,[],[f669,f58])).
% 1.39/0.55  fof(f58,plain,(
% 1.39/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.39/0.55    inference(cnf_transformation,[],[f7])).
% 1.39/0.55  fof(f7,axiom,(
% 1.39/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.39/0.55  fof(f669,plain,(
% 1.39/0.55    k1_xboole_0 != k2_relat_1(k1_xboole_0) | ~v2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | spl7_31),
% 1.39/0.55    inference(superposition,[],[f667,f67])).
% 1.39/0.55  fof(f67,plain,(
% 1.39/0.55    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f24])).
% 1.39/0.55  fof(f24,plain,(
% 1.39/0.55    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.39/0.55    inference(flattening,[],[f23])).
% 1.39/0.55  fof(f23,plain,(
% 1.39/0.55    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.39/0.55    inference(ennf_transformation,[],[f9])).
% 1.39/0.55  fof(f9,axiom,(
% 1.39/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.39/0.55  fof(f667,plain,(
% 1.39/0.55    k1_xboole_0 != k1_relat_1(k2_funct_1(k1_xboole_0)) | spl7_31),
% 1.39/0.55    inference(avatar_component_clause,[],[f665])).
% 1.39/0.55  fof(f668,plain,(
% 1.39/0.55    ~spl7_31 | ~spl7_27 | spl7_2 | ~spl7_22),
% 1.39/0.55    inference(avatar_split_clause,[],[f663,f385,f102,f602,f665])).
% 1.39/0.55  fof(f602,plain,(
% 1.39/0.55    spl7_27 <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 1.39/0.55  fof(f102,plain,(
% 1.39/0.55    spl7_2 <=> v1_funct_2(k2_funct_1(sK6),sK5,sK4)),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.39/0.55  fof(f385,plain,(
% 1.39/0.55    spl7_22 <=> sP1(sK4,sK5)),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 1.39/0.55  fof(f663,plain,(
% 1.39/0.55    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relat_1(k2_funct_1(k1_xboole_0)) | (spl7_2 | ~spl7_22)),
% 1.39/0.55    inference(resolution,[],[f658,f471])).
% 1.39/0.55  fof(f471,plain,(
% 1.39/0.55    ( ! [X2,X3] : (v1_funct_2(X3,k1_xboole_0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relat_1(X3)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f468,f96])).
% 1.39/0.55  fof(f96,plain,(
% 1.39/0.55    ( ! [X1] : (~sP1(k1_xboole_0,X1)) )),
% 1.39/0.55    inference(equality_resolution,[],[f85])).
% 1.39/0.55  fof(f85,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~sP1(X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f50])).
% 1.39/0.55  fof(f50,plain,(
% 1.39/0.55    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 1.39/0.55    inference(nnf_transformation,[],[f34])).
% 1.39/0.55  fof(f34,plain,(
% 1.39/0.55    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 1.39/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.39/0.55  fof(f468,plain,(
% 1.39/0.55    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X3,k1_xboole_0,X2) | sP1(k1_xboole_0,X2) | k1_xboole_0 != k1_relat_1(X3)) )),
% 1.39/0.55    inference(superposition,[],[f325,f92])).
% 1.39/0.55  fof(f92,plain,(
% 1.39/0.55    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.39/0.55    inference(equality_resolution,[],[f75])).
% 1.39/0.55  fof(f75,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.39/0.55    inference(cnf_transformation,[],[f45])).
% 1.39/0.55  fof(f45,plain,(
% 1.39/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.39/0.55    inference(flattening,[],[f44])).
% 1.39/0.55  fof(f44,plain,(
% 1.39/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.39/0.55    inference(nnf_transformation,[],[f3])).
% 1.39/0.55  fof(f3,axiom,(
% 1.39/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.39/0.55  fof(f325,plain,(
% 1.39/0.55    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | v1_funct_2(X5,X3,X4) | sP1(X3,X4) | k1_relat_1(X5) != X3) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f323,f86])).
% 1.39/0.55  fof(f86,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X0,X2,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f37])).
% 1.39/0.55  fof(f37,plain,(
% 1.39/0.55    ! [X0,X1,X2] : ((sP3(X2,X1,X0) & sP2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.55    inference(definition_folding,[],[f29,f36,f35,f34])).
% 1.39/0.55  fof(f35,plain,(
% 1.39/0.55    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 1.39/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.39/0.55  fof(f36,plain,(
% 1.39/0.55    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP3(X2,X1,X0))),
% 1.39/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.39/0.55  fof(f29,plain,(
% 1.39/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.55    inference(flattening,[],[f28])).
% 1.39/0.55  fof(f28,plain,(
% 1.39/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.55    inference(ennf_transformation,[],[f13])).
% 1.39/0.55  fof(f13,axiom,(
% 1.39/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.39/0.55  fof(f323,plain,(
% 1.39/0.55    ( ! [X4,X5,X3] : (k1_relat_1(X5) != X3 | v1_funct_2(X5,X3,X4) | sP1(X3,X4) | ~sP2(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 1.39/0.55    inference(superposition,[],[f83,f78])).
% 1.39/0.55  fof(f78,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.39/0.55    inference(cnf_transformation,[],[f26])).
% 1.39/0.55  fof(f26,plain,(
% 1.39/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.55    inference(ennf_transformation,[],[f11])).
% 1.39/0.55  fof(f11,axiom,(
% 1.39/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.39/0.55  fof(f83,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) != X0 | v1_funct_2(X1,X0,X2) | sP1(X0,X2) | ~sP2(X0,X1,X2)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f49])).
% 1.39/0.55  fof(f49,plain,(
% 1.39/0.55    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP1(X0,X2) | ~sP2(X0,X1,X2))),
% 1.39/0.55    inference(rectify,[],[f48])).
% 1.39/0.55  fof(f48,plain,(
% 1.39/0.55    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 1.39/0.55    inference(nnf_transformation,[],[f35])).
% 1.39/0.55  fof(f658,plain,(
% 1.39/0.55    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK4) | (spl7_2 | ~spl7_22)),
% 1.39/0.55    inference(forward_demodulation,[],[f657,f572])).
% 1.39/0.55  fof(f572,plain,(
% 1.39/0.55    k1_xboole_0 = sK6 | ~spl7_22),
% 1.39/0.55    inference(resolution,[],[f561,f154])).
% 1.39/0.55  fof(f154,plain,(
% 1.39/0.55    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.39/0.55    inference(resolution,[],[f71,f59])).
% 1.39/0.55  fof(f59,plain,(
% 1.39/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f2])).
% 1.39/0.55  fof(f2,axiom,(
% 1.39/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.39/0.55  fof(f71,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f42])).
% 1.39/0.55  fof(f42,plain,(
% 1.39/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.39/0.55    inference(flattening,[],[f41])).
% 1.39/0.55  fof(f41,plain,(
% 1.39/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.39/0.55    inference(nnf_transformation,[],[f1])).
% 1.39/0.55  fof(f1,axiom,(
% 1.39/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.39/0.55  fof(f561,plain,(
% 1.39/0.55    r1_tarski(sK6,k1_xboole_0) | ~spl7_22),
% 1.39/0.55    inference(forward_demodulation,[],[f549,f91])).
% 1.39/0.55  fof(f91,plain,(
% 1.39/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.39/0.55    inference(equality_resolution,[],[f76])).
% 1.39/0.55  fof(f76,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.39/0.55    inference(cnf_transformation,[],[f45])).
% 1.39/0.55  fof(f549,plain,(
% 1.39/0.55    r1_tarski(sK6,k2_zfmisc_1(sK4,k1_xboole_0)) | ~spl7_22),
% 1.39/0.55    inference(backward_demodulation,[],[f113,f543])).
% 1.39/0.55  fof(f543,plain,(
% 1.39/0.55    k1_xboole_0 = sK5 | ~spl7_22),
% 1.39/0.55    inference(resolution,[],[f387,f84])).
% 1.39/0.55  fof(f84,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~sP1(X0,X1) | k1_xboole_0 = X1) )),
% 1.39/0.55    inference(cnf_transformation,[],[f50])).
% 1.39/0.55  fof(f387,plain,(
% 1.39/0.55    sP1(sK4,sK5) | ~spl7_22),
% 1.39/0.55    inference(avatar_component_clause,[],[f385])).
% 1.39/0.55  fof(f113,plain,(
% 1.39/0.55    r1_tarski(sK6,k2_zfmisc_1(sK4,sK5))),
% 1.39/0.55    inference(resolution,[],[f72,f53])).
% 1.39/0.55  fof(f53,plain,(
% 1.39/0.55    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 1.39/0.55    inference(cnf_transformation,[],[f39])).
% 1.39/0.55  fof(f39,plain,(
% 1.39/0.55    (~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(k2_funct_1(sK6),sK5,sK4) | ~v1_funct_1(k2_funct_1(sK6))) & sK5 = k2_relset_1(sK4,sK5,sK6) & v2_funct_1(sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6)),
% 1.39/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f18,f38])).
% 1.39/0.55  fof(f38,plain,(
% 1.39/0.55    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(k2_funct_1(sK6),sK5,sK4) | ~v1_funct_1(k2_funct_1(sK6))) & sK5 = k2_relset_1(sK4,sK5,sK6) & v2_funct_1(sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6))),
% 1.39/0.55    introduced(choice_axiom,[])).
% 1.39/0.55  fof(f18,plain,(
% 1.39/0.55    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.39/0.55    inference(flattening,[],[f17])).
% 1.39/0.55  fof(f17,plain,(
% 1.39/0.55    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.39/0.55    inference(ennf_transformation,[],[f16])).
% 1.39/0.55  fof(f16,negated_conjecture,(
% 1.39/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.39/0.55    inference(negated_conjecture,[],[f15])).
% 1.39/0.55  fof(f15,conjecture,(
% 1.39/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 1.39/0.55  fof(f72,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f43])).
% 1.39/0.55  fof(f43,plain,(
% 1.39/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.39/0.55    inference(nnf_transformation,[],[f5])).
% 1.39/0.55  fof(f5,axiom,(
% 1.39/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.39/0.55  fof(f657,plain,(
% 1.39/0.55    ~v1_funct_2(k2_funct_1(sK6),k1_xboole_0,sK4) | (spl7_2 | ~spl7_22)),
% 1.39/0.55    inference(forward_demodulation,[],[f104,f543])).
% 1.39/0.55  fof(f104,plain,(
% 1.39/0.55    ~v1_funct_2(k2_funct_1(sK6),sK5,sK4) | spl7_2),
% 1.39/0.55    inference(avatar_component_clause,[],[f102])).
% 1.39/0.55  fof(f652,plain,(
% 1.39/0.55    ~spl7_27 | spl7_3 | ~spl7_22),
% 1.39/0.55    inference(avatar_split_clause,[],[f651,f385,f106,f602])).
% 1.39/0.55  fof(f106,plain,(
% 1.39/0.55    spl7_3 <=> m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.39/0.55  fof(f651,plain,(
% 1.39/0.55    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl7_3 | ~spl7_22)),
% 1.39/0.55    inference(forward_demodulation,[],[f560,f572])).
% 1.39/0.55  fof(f560,plain,(
% 1.39/0.55    ~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k1_xboole_0)) | (spl7_3 | ~spl7_22)),
% 1.39/0.55    inference(forward_demodulation,[],[f548,f92])).
% 1.39/0.55  fof(f548,plain,(
% 1.39/0.55    ~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) | (spl7_3 | ~spl7_22)),
% 1.39/0.55    inference(backward_demodulation,[],[f108,f543])).
% 1.39/0.55  fof(f108,plain,(
% 1.39/0.55    ~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | spl7_3),
% 1.39/0.55    inference(avatar_component_clause,[],[f106])).
% 1.39/0.55  fof(f641,plain,(
% 1.39/0.55    spl7_26 | ~spl7_19 | ~spl7_22),
% 1.39/0.55    inference(avatar_split_clause,[],[f582,f385,f337,f598])).
% 1.39/0.55  fof(f598,plain,(
% 1.39/0.55    spl7_26 <=> sP0(k2_funct_1(k1_xboole_0))),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 1.39/0.55  fof(f337,plain,(
% 1.39/0.55    spl7_19 <=> sP0(k2_funct_1(sK6))),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 1.39/0.55  fof(f582,plain,(
% 1.39/0.55    sP0(k2_funct_1(k1_xboole_0)) | (~spl7_19 | ~spl7_22)),
% 1.39/0.55    inference(backward_demodulation,[],[f338,f572])).
% 1.39/0.55  fof(f338,plain,(
% 1.39/0.55    sP0(k2_funct_1(sK6)) | ~spl7_19),
% 1.39/0.55    inference(avatar_component_clause,[],[f337])).
% 1.39/0.55  fof(f628,plain,(
% 1.39/0.55    spl7_25 | ~spl7_22),
% 1.39/0.55    inference(avatar_split_clause,[],[f578,f385,f594])).
% 1.39/0.55  fof(f578,plain,(
% 1.39/0.55    v2_funct_1(k1_xboole_0) | ~spl7_22),
% 1.39/0.55    inference(backward_demodulation,[],[f54,f572])).
% 1.39/0.55  fof(f54,plain,(
% 1.39/0.55    v2_funct_1(sK6)),
% 1.39/0.55    inference(cnf_transformation,[],[f39])).
% 1.39/0.55  fof(f605,plain,(
% 1.39/0.55    ~spl7_7 | ~spl7_25 | ~spl7_26 | spl7_27 | ~spl7_6),
% 1.39/0.55    inference(avatar_split_clause,[],[f592,f132,f602,f598,f594,f136])).
% 1.39/0.55  fof(f592,plain,(
% 1.39/0.55    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~sP0(k2_funct_1(k1_xboole_0)) | ~v2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~spl7_6),
% 1.39/0.55    inference(forward_demodulation,[],[f591,f92])).
% 1.39/0.55  fof(f591,plain,(
% 1.39/0.55    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0))))) | ~sP0(k2_funct_1(k1_xboole_0)) | ~v2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~spl7_6),
% 1.39/0.55    inference(subsumption_resolution,[],[f506,f133])).
% 1.39/0.55  fof(f506,plain,(
% 1.39/0.55    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0))))) | ~sP0(k2_funct_1(k1_xboole_0)) | ~v2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.39/0.55    inference(superposition,[],[f226,f58])).
% 1.55/0.56  % (18213)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.55/0.56  % (18211)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.55/0.56  % (18199)Refutation not found, incomplete strategy% (18199)------------------------------
% 1.55/0.56  % (18199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.56  % (18199)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.56  
% 1.55/0.56  % (18199)Memory used [KB]: 6396
% 1.55/0.56  % (18199)Time elapsed: 0.127 s
% 1.55/0.56  % (18199)------------------------------
% 1.55/0.56  % (18199)------------------------------
% 1.55/0.56  % (18194)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.55/0.56  % (18202)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.55/0.56  % (18214)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.55/0.56  % (18200)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.56  % (18203)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.55/0.57  % (18195)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.55/0.57  % (18205)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.55/0.57  % (18195)Refutation not found, incomplete strategy% (18195)------------------------------
% 1.55/0.57  % (18195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  fof(f226,plain,(
% 1.55/0.57    ( ! [X3] : (m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X3),k2_relat_1(k2_funct_1(X3))))) | ~sP0(k2_funct_1(X3)) | ~v2_funct_1(X3) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 1.55/0.57    inference(superposition,[],[f63,f67])).
% 1.55/0.57  fof(f63,plain,(
% 1.55/0.57    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~sP0(X0)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f40])).
% 1.55/0.57  fof(f40,plain,(
% 1.55/0.57    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~sP0(X0))),
% 1.55/0.57    inference(nnf_transformation,[],[f32])).
% 1.55/0.57  fof(f32,plain,(
% 1.55/0.57    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~sP0(X0))),
% 1.55/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.55/0.57  fof(f590,plain,(
% 1.55/0.57    spl7_7 | ~spl7_22),
% 1.55/0.57    inference(avatar_split_clause,[],[f577,f385,f136])).
% 1.55/0.57  fof(f577,plain,(
% 1.55/0.57    v1_funct_1(k1_xboole_0) | ~spl7_22),
% 1.55/0.57    inference(backward_demodulation,[],[f51,f572])).
% 1.55/0.57  fof(f51,plain,(
% 1.55/0.57    v1_funct_1(sK6)),
% 1.55/0.57    inference(cnf_transformation,[],[f39])).
% 1.55/0.57  fof(f542,plain,(
% 1.55/0.57    spl7_21 | spl7_22),
% 1.55/0.57    inference(avatar_split_clause,[],[f541,f385,f381])).
% 1.55/0.57  fof(f381,plain,(
% 1.55/0.57    spl7_21 <=> sK4 = k1_relat_1(sK6)),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 1.55/0.57  fof(f541,plain,(
% 1.55/0.57    sP1(sK4,sK5) | sK4 = k1_relat_1(sK6)),
% 1.55/0.57    inference(subsumption_resolution,[],[f450,f52])).
% 1.55/0.57  fof(f52,plain,(
% 1.55/0.57    v1_funct_2(sK6,sK4,sK5)),
% 1.55/0.57    inference(cnf_transformation,[],[f39])).
% 1.55/0.57  fof(f450,plain,(
% 1.55/0.57    sP1(sK4,sK5) | sK4 = k1_relat_1(sK6) | ~v1_funct_2(sK6,sK4,sK5)),
% 1.55/0.57    inference(resolution,[],[f376,f113])).
% 1.55/0.57  fof(f376,plain,(
% 1.55/0.57    ( ! [X4,X5,X3] : (~r1_tarski(X3,k2_zfmisc_1(X4,X5)) | sP1(X4,X5) | k1_relat_1(X3) = X4 | ~v1_funct_2(X3,X4,X5)) )),
% 1.55/0.57    inference(resolution,[],[f307,f73])).
% 1.55/0.57  fof(f73,plain,(
% 1.55/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f43])).
% 1.55/0.57  fof(f307,plain,(
% 1.55/0.57    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP1(X3,X4) | k1_relat_1(X5) = X3) )),
% 1.55/0.57    inference(subsumption_resolution,[],[f305,f86])).
% 1.55/0.57  fof(f305,plain,(
% 1.55/0.57    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP1(X3,X4) | ~sP2(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 1.55/0.57    inference(superposition,[],[f82,f78])).
% 1.55/0.57  fof(f82,plain,(
% 1.55/0.57    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP1(X0,X2) | ~sP2(X0,X1,X2)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f49])).
% 1.55/0.57  fof(f540,plain,(
% 1.55/0.57    spl7_3 | ~spl7_19 | ~spl7_21),
% 1.55/0.57    inference(avatar_contradiction_clause,[],[f539])).
% 1.55/0.57  fof(f539,plain,(
% 1.55/0.57    $false | (spl7_3 | ~spl7_19 | ~spl7_21)),
% 1.55/0.57    inference(subsumption_resolution,[],[f538,f108])).
% 1.55/0.57  fof(f538,plain,(
% 1.55/0.57    m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | (~spl7_19 | ~spl7_21)),
% 1.55/0.57    inference(forward_demodulation,[],[f537,f383])).
% 1.55/0.57  fof(f383,plain,(
% 1.55/0.57    sK4 = k1_relat_1(sK6) | ~spl7_21),
% 1.55/0.57    inference(avatar_component_clause,[],[f381])).
% 1.55/0.57  fof(f537,plain,(
% 1.55/0.57    m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,k1_relat_1(sK6)))) | ~spl7_19),
% 1.55/0.57    inference(subsumption_resolution,[],[f536,f140])).
% 1.55/0.57  fof(f140,plain,(
% 1.55/0.57    v1_relat_1(sK6)),
% 1.55/0.57    inference(resolution,[],[f77,f53])).
% 1.55/0.57  fof(f77,plain,(
% 1.55/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f25])).
% 1.55/0.57  fof(f25,plain,(
% 1.55/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.55/0.57    inference(ennf_transformation,[],[f10])).
% 1.55/0.57  fof(f10,axiom,(
% 1.55/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.55/0.57  fof(f536,plain,(
% 1.55/0.57    m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,k1_relat_1(sK6)))) | ~v1_relat_1(sK6) | ~spl7_19),
% 1.55/0.57    inference(subsumption_resolution,[],[f535,f51])).
% 1.55/0.57  fof(f535,plain,(
% 1.55/0.57    m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,k1_relat_1(sK6)))) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~spl7_19),
% 1.55/0.57    inference(subsumption_resolution,[],[f524,f54])).
% 1.55/0.57  fof(f524,plain,(
% 1.55/0.57    m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,k1_relat_1(sK6)))) | ~v2_funct_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~spl7_19),
% 1.55/0.57    inference(superposition,[],[f516,f68])).
% 1.55/0.57  fof(f68,plain,(
% 1.55/0.57    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f24])).
% 1.55/0.57  fof(f516,plain,(
% 1.55/0.57    m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,k2_relat_1(k2_funct_1(sK6))))) | ~spl7_19),
% 1.55/0.57    inference(subsumption_resolution,[],[f515,f140])).
% 1.55/0.57  fof(f515,plain,(
% 1.55/0.57    m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,k2_relat_1(k2_funct_1(sK6))))) | ~v1_relat_1(sK6) | ~spl7_19),
% 1.55/0.57    inference(subsumption_resolution,[],[f514,f51])).
% 1.55/0.57  fof(f514,plain,(
% 1.55/0.57    m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,k2_relat_1(k2_funct_1(sK6))))) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~spl7_19),
% 1.55/0.57    inference(subsumption_resolution,[],[f513,f54])).
% 1.55/0.57  fof(f513,plain,(
% 1.55/0.57    m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,k2_relat_1(k2_funct_1(sK6))))) | ~v2_funct_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~spl7_19),
% 1.55/0.57    inference(subsumption_resolution,[],[f508,f338])).
% 1.55/0.57  fof(f508,plain,(
% 1.55/0.57    m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,k2_relat_1(k2_funct_1(sK6))))) | ~sP0(k2_funct_1(sK6)) | ~v2_funct_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)),
% 1.55/0.57    inference(superposition,[],[f226,f239])).
% 1.55/0.57  fof(f239,plain,(
% 1.55/0.57    sK5 = k2_relat_1(sK6)),
% 1.55/0.57    inference(subsumption_resolution,[],[f237,f53])).
% 1.55/0.57  fof(f237,plain,(
% 1.55/0.57    sK5 = k2_relat_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 1.55/0.57    inference(superposition,[],[f79,f55])).
% 1.55/0.57  fof(f55,plain,(
% 1.55/0.57    sK5 = k2_relset_1(sK4,sK5,sK6)),
% 1.55/0.57    inference(cnf_transformation,[],[f39])).
% 1.55/0.57  fof(f79,plain,(
% 1.55/0.57    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.55/0.57    inference(cnf_transformation,[],[f27])).
% 1.55/0.57  fof(f27,plain,(
% 1.55/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.55/0.57    inference(ennf_transformation,[],[f12])).
% 1.55/0.57  fof(f12,axiom,(
% 1.55/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.55/0.57  fof(f435,plain,(
% 1.55/0.57    spl7_2 | ~spl7_19 | ~spl7_21),
% 1.55/0.57    inference(avatar_split_clause,[],[f432,f381,f337,f102])).
% 1.55/0.57  fof(f432,plain,(
% 1.55/0.57    v1_funct_2(k2_funct_1(sK6),sK5,sK4) | (~spl7_19 | ~spl7_21)),
% 1.55/0.57    inference(forward_demodulation,[],[f431,f239])).
% 1.55/0.57  fof(f431,plain,(
% 1.55/0.57    v1_funct_2(k2_funct_1(sK6),k2_relat_1(sK6),sK4) | (~spl7_19 | ~spl7_21)),
% 1.55/0.57    inference(subsumption_resolution,[],[f430,f140])).
% 1.55/0.57  fof(f430,plain,(
% 1.55/0.57    v1_funct_2(k2_funct_1(sK6),k2_relat_1(sK6),sK4) | ~v1_relat_1(sK6) | (~spl7_19 | ~spl7_21)),
% 1.55/0.57    inference(subsumption_resolution,[],[f429,f51])).
% 1.55/0.57  fof(f429,plain,(
% 1.55/0.57    v1_funct_2(k2_funct_1(sK6),k2_relat_1(sK6),sK4) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | (~spl7_19 | ~spl7_21)),
% 1.55/0.57    inference(subsumption_resolution,[],[f428,f54])).
% 1.55/0.57  fof(f428,plain,(
% 1.55/0.57    v1_funct_2(k2_funct_1(sK6),k2_relat_1(sK6),sK4) | ~v2_funct_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | (~spl7_19 | ~spl7_21)),
% 1.55/0.57    inference(subsumption_resolution,[],[f407,f338])).
% 1.55/0.57  fof(f407,plain,(
% 1.55/0.57    v1_funct_2(k2_funct_1(sK6),k2_relat_1(sK6),sK4) | ~sP0(k2_funct_1(sK6)) | ~v2_funct_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~spl7_21),
% 1.55/0.57    inference(superposition,[],[f330,f383])).
% 1.55/0.57  fof(f330,plain,(
% 1.55/0.57    ( ! [X0] : (v1_funct_2(k2_funct_1(X0),k2_relat_1(X0),k1_relat_1(X0)) | ~sP0(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.55/0.57    inference(duplicate_literal_removal,[],[f329])).
% 1.55/0.57  fof(f329,plain,(
% 1.55/0.57    ( ! [X0] : (v1_funct_2(k2_funct_1(X0),k2_relat_1(X0),k1_relat_1(X0)) | ~sP0(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.55/0.57    inference(superposition,[],[f227,f68])).
% 1.55/0.57  fof(f227,plain,(
% 1.55/0.57    ( ! [X4] : (v1_funct_2(k2_funct_1(X4),k2_relat_1(X4),k2_relat_1(k2_funct_1(X4))) | ~sP0(k2_funct_1(X4)) | ~v2_funct_1(X4) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) )),
% 1.55/0.57    inference(superposition,[],[f62,f67])).
% 1.55/0.57  fof(f62,plain,(
% 1.55/0.57    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~sP0(X0)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f40])).
% 1.55/0.57  fof(f350,plain,(
% 1.55/0.57    ~spl7_1 | spl7_19),
% 1.55/0.57    inference(avatar_contradiction_clause,[],[f349])).
% 1.55/0.57  fof(f349,plain,(
% 1.55/0.57    $false | (~spl7_1 | spl7_19)),
% 1.55/0.57    inference(subsumption_resolution,[],[f348,f140])).
% 1.55/0.57  fof(f348,plain,(
% 1.55/0.57    ~v1_relat_1(sK6) | (~spl7_1 | spl7_19)),
% 1.55/0.57    inference(subsumption_resolution,[],[f347,f51])).
% 1.55/0.57  fof(f347,plain,(
% 1.55/0.57    ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | (~spl7_1 | spl7_19)),
% 1.55/0.57    inference(resolution,[],[f346,f65])).
% 1.55/0.57  fof(f65,plain,(
% 1.55/0.57    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f22])).
% 1.55/0.57  fof(f22,plain,(
% 1.55/0.57    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.55/0.57    inference(flattening,[],[f21])).
% 1.55/0.57  fof(f21,plain,(
% 1.55/0.57    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.55/0.57    inference(ennf_transformation,[],[f8])).
% 1.55/0.57  fof(f8,axiom,(
% 1.55/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.55/0.57  fof(f346,plain,(
% 1.55/0.57    ~v1_relat_1(k2_funct_1(sK6)) | (~spl7_1 | spl7_19)),
% 1.55/0.57    inference(subsumption_resolution,[],[f345,f99])).
% 1.55/0.57  fof(f99,plain,(
% 1.55/0.57    v1_funct_1(k2_funct_1(sK6)) | ~spl7_1),
% 1.55/0.57    inference(avatar_component_clause,[],[f98])).
% 1.55/0.57  fof(f98,plain,(
% 1.55/0.57    spl7_1 <=> v1_funct_1(k2_funct_1(sK6))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.55/0.57  fof(f345,plain,(
% 1.55/0.57    ~v1_funct_1(k2_funct_1(sK6)) | ~v1_relat_1(k2_funct_1(sK6)) | spl7_19),
% 1.55/0.57    inference(resolution,[],[f339,f64])).
% 1.55/0.57  fof(f64,plain,(
% 1.55/0.57    ( ! [X0] : (sP0(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f33])).
% 1.55/0.57  fof(f33,plain,(
% 1.55/0.57    ! [X0] : (sP0(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.55/0.57    inference(definition_folding,[],[f20,f32])).
% 1.55/0.57  fof(f20,plain,(
% 1.55/0.57    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.55/0.57    inference(flattening,[],[f19])).
% 1.55/0.57  fof(f19,plain,(
% 1.55/0.57    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.55/0.57    inference(ennf_transformation,[],[f14])).
% 1.55/0.57  fof(f14,axiom,(
% 1.55/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 1.55/0.57  fof(f339,plain,(
% 1.55/0.57    ~sP0(k2_funct_1(sK6)) | spl7_19),
% 1.55/0.57    inference(avatar_component_clause,[],[f337])).
% 1.55/0.57  fof(f149,plain,(
% 1.55/0.57    spl7_6),
% 1.55/0.57    inference(avatar_split_clause,[],[f141,f132])).
% 1.55/0.57  fof(f141,plain,(
% 1.55/0.57    v1_relat_1(k1_xboole_0)),
% 1.55/0.57    inference(resolution,[],[f77,f60])).
% 1.55/0.57  fof(f60,plain,(
% 1.55/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.55/0.57    inference(cnf_transformation,[],[f4])).
% 1.55/0.57  fof(f4,axiom,(
% 1.55/0.57    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.55/0.57  fof(f146,plain,(
% 1.55/0.57    spl7_1),
% 1.55/0.57    inference(avatar_contradiction_clause,[],[f145])).
% 1.55/0.57  fof(f145,plain,(
% 1.55/0.57    $false | spl7_1),
% 1.55/0.57    inference(subsumption_resolution,[],[f140,f112])).
% 1.55/0.57  fof(f112,plain,(
% 1.55/0.57    ~v1_relat_1(sK6) | spl7_1),
% 1.55/0.57    inference(subsumption_resolution,[],[f111,f51])).
% 1.55/0.57  fof(f111,plain,(
% 1.55/0.57    ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl7_1),
% 1.55/0.57    inference(resolution,[],[f66,f100])).
% 1.55/0.57  fof(f100,plain,(
% 1.55/0.57    ~v1_funct_1(k2_funct_1(sK6)) | spl7_1),
% 1.55/0.57    inference(avatar_component_clause,[],[f98])).
% 1.55/0.57  fof(f66,plain,(
% 1.55/0.57    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f22])).
% 1.55/0.57  fof(f109,plain,(
% 1.55/0.57    ~spl7_1 | ~spl7_2 | ~spl7_3),
% 1.55/0.57    inference(avatar_split_clause,[],[f56,f106,f102,f98])).
% 1.55/0.57  fof(f56,plain,(
% 1.55/0.57    ~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(k2_funct_1(sK6),sK5,sK4) | ~v1_funct_1(k2_funct_1(sK6))),
% 1.55/0.57    inference(cnf_transformation,[],[f39])).
% 1.55/0.57  % SZS output end Proof for theBenchmark
% 1.55/0.57  % (18198)------------------------------
% 1.55/0.57  % (18198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (18198)Termination reason: Refutation
% 1.55/0.57  
% 1.55/0.57  % (18198)Memory used [KB]: 6396
% 1.55/0.57  % (18198)Time elapsed: 0.130 s
% 1.55/0.57  % (18198)------------------------------
% 1.55/0.57  % (18198)------------------------------
% 1.55/0.57  
% 1.55/0.57  % (18200)Memory used [KB]: 10618
% 1.55/0.57  % (18200)Time elapsed: 0.124 s
% 1.55/0.57  % (18200)------------------------------
% 1.55/0.57  % (18200)------------------------------
% 1.55/0.57  % (18193)Success in time 0.211 s
%------------------------------------------------------------------------------
