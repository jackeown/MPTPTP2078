%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 200 expanded)
%              Number of leaves         :   31 (  85 expanded)
%              Depth                    :    9
%              Number of atoms          :  326 ( 707 expanded)
%              Number of equality atoms :   46 ( 134 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f494,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f91,f96,f101,f106,f184,f216,f222,f234,f244,f254,f255,f340,f345,f383,f388,f486,f493])).

fof(f493,plain,
    ( k1_xboole_0 != sK3
    | v1_xboole_0(sK3)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f486,plain,
    ( ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_23
    | spl9_27
    | ~ spl9_33
    | ~ spl9_36
    | ~ spl9_37 ),
    inference(avatar_contradiction_clause,[],[f485])).

fof(f485,plain,
    ( $false
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_23
    | spl9_27
    | ~ spl9_33
    | ~ spl9_36
    | ~ spl9_37 ),
    inference(subsumption_resolution,[],[f484,f253])).

fof(f253,plain,
    ( ~ r2_hidden(sK8(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
    | spl9_23 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl9_23
  <=> r2_hidden(sK8(k2_relat_1(sK4),sK3),k2_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f484,plain,
    ( r2_hidden(sK8(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_27
    | ~ spl9_33
    | ~ spl9_36
    | ~ spl9_37 ),
    inference(forward_demodulation,[],[f483,f387])).

fof(f387,plain,
    ( sK8(k2_relat_1(sK4),sK3) = k1_funct_1(sK4,sK5(sK8(k2_relat_1(sK4),sK3)))
    | ~ spl9_37 ),
    inference(avatar_component_clause,[],[f385])).

fof(f385,plain,
    ( spl9_37
  <=> sK8(k2_relat_1(sK4),sK3) = k1_funct_1(sK4,sK5(sK8(k2_relat_1(sK4),sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).

fof(f483,plain,
    ( r2_hidden(k1_funct_1(sK4,sK5(sK8(k2_relat_1(sK4),sK3))),k2_relat_1(sK4))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_27
    | ~ spl9_33
    | ~ spl9_36 ),
    inference(forward_demodulation,[],[f476,f344])).

fof(f344,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4)
    | ~ spl9_33 ),
    inference(avatar_component_clause,[],[f342])).

fof(f342,plain,
    ( spl9_33
  <=> k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).

fof(f476,plain,
    ( r2_hidden(k1_funct_1(sK4,sK5(sK8(k2_relat_1(sK4),sK3))),k2_relset_1(sK2,sK3,sK4))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_27
    | ~ spl9_36 ),
    inference(unit_resulting_resolution,[],[f100,f382,f286,f95,f90,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

fof(f90,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl9_2
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f95,plain,
    ( v1_funct_2(sK4,sK2,sK3)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl9_3
  <=> v1_funct_2(sK4,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f286,plain,
    ( k1_xboole_0 != sK3
    | spl9_27 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl9_27
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f382,plain,
    ( r2_hidden(sK5(sK8(k2_relat_1(sK4),sK3)),sK2)
    | ~ spl9_36 ),
    inference(avatar_component_clause,[],[f380])).

fof(f380,plain,
    ( spl9_36
  <=> r2_hidden(sK5(sK8(k2_relat_1(sK4),sK3)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f100,plain,
    ( v1_funct_1(sK4)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl9_4
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f388,plain,
    ( spl9_37
    | ~ spl9_21 ),
    inference(avatar_split_clause,[],[f375,f241,f385])).

fof(f241,plain,
    ( spl9_21
  <=> r2_hidden(sK8(k2_relat_1(sK4),sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f375,plain,
    ( sK8(k2_relat_1(sK4),sK3) = k1_funct_1(sK4,sK5(sK8(k2_relat_1(sK4),sK3)))
    | ~ spl9_21 ),
    inference(unit_resulting_resolution,[],[f243,f52])).

fof(f52,plain,(
    ! [X3] :
      ( k1_funct_1(sK4,sK5(X3)) = X3
      | ~ r2_hidden(X3,sK3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( sK3 != k2_relset_1(sK2,sK3,sK4)
    & ! [X3] :
        ( ( k1_funct_1(sK4,sK5(X3)) = X3
          & r2_hidden(sK5(X3),sK2) )
        | ~ r2_hidden(X3,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f16,f34,f33])).

fof(f33,plain,
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
   => ( sK3 != k2_relset_1(sK2,sK3,sK4)
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK4,X4) = X3
              & r2_hidden(X4,sK2) )
          | ~ r2_hidden(X3,sK3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X3] :
      ( ? [X4] :
          ( k1_funct_1(sK4,X4) = X3
          & r2_hidden(X4,sK2) )
     => ( k1_funct_1(sK4,sK5(X3)) = X3
        & r2_hidden(sK5(X3),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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

fof(f243,plain,
    ( r2_hidden(sK8(k2_relat_1(sK4),sK3),sK3)
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f241])).

fof(f383,plain,
    ( spl9_36
    | ~ spl9_21 ),
    inference(avatar_split_clause,[],[f376,f241,f380])).

fof(f376,plain,
    ( r2_hidden(sK5(sK8(k2_relat_1(sK4),sK3)),sK2)
    | ~ spl9_21 ),
    inference(unit_resulting_resolution,[],[f243,f51])).

fof(f51,plain,(
    ! [X3] :
      ( r2_hidden(sK5(X3),sK2)
      | ~ r2_hidden(X3,sK3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f345,plain,
    ( spl9_33
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f331,f88,f342])).

fof(f331,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4)
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f90,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f340,plain,
    ( ~ spl9_20
    | spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f339,f88,f83,f231])).

fof(f231,plain,
    ( spl9_20
  <=> sK3 = k2_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f83,plain,
    ( spl9_1
  <=> sK3 = k2_relset_1(sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f339,plain,
    ( sK3 != k2_relat_1(sK4)
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f332,f90])).

fof(f332,plain,
    ( sK3 != k2_relat_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | spl9_1 ),
    inference(superposition,[],[f85,f77])).

fof(f85,plain,
    ( sK3 != k2_relset_1(sK2,sK3,sK4)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f255,plain,
    ( ~ spl9_22
    | ~ spl9_19 ),
    inference(avatar_split_clause,[],[f239,f227,f246])).

fof(f246,plain,
    ( spl9_22
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f227,plain,
    ( spl9_19
  <=> r2_xboole_0(k2_relat_1(sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f239,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl9_19 ),
    inference(resolution,[],[f229,f163])).

fof(f163,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f73,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK8(X0,X1),X0)
        & r2_hidden(sK8(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f23,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK8(X0,X1),X0)
        & r2_hidden(sK8(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f229,plain,
    ( r2_xboole_0(k2_relat_1(sK4),sK3)
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f227])).

fof(f254,plain,
    ( ~ spl9_23
    | ~ spl9_19 ),
    inference(avatar_split_clause,[],[f235,f227,f251])).

fof(f235,plain,
    ( ~ r2_hidden(sK8(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
    | ~ spl9_19 ),
    inference(unit_resulting_resolution,[],[f229,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f244,plain,
    ( spl9_21
    | ~ spl9_19 ),
    inference(avatar_split_clause,[],[f237,f227,f241])).

fof(f237,plain,
    ( r2_hidden(sK8(k2_relat_1(sK4),sK3),sK3)
    | ~ spl9_19 ),
    inference(unit_resulting_resolution,[],[f229,f73])).

fof(f234,plain,
    ( spl9_19
    | spl9_20
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f225,f219,f231,f227])).

fof(f219,plain,
    ( spl9_18
  <=> r1_tarski(k2_relat_1(sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f225,plain,
    ( sK3 = k2_relat_1(sK4)
    | r2_xboole_0(k2_relat_1(sK4),sK3)
    | ~ spl9_18 ),
    inference(resolution,[],[f221,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f221,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3)
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f219])).

fof(f222,plain,
    ( spl9_18
    | ~ spl9_14
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f217,f212,f180,f219])).

fof(f180,plain,
    ( spl9_14
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f212,plain,
    ( spl9_17
  <=> v5_relat_1(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f217,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3)
    | ~ spl9_14
    | ~ spl9_17 ),
    inference(unit_resulting_resolution,[],[f182,f214,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f214,plain,
    ( v5_relat_1(sK4,sK3)
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f212])).

fof(f182,plain,
    ( v1_relat_1(sK4)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f180])).

fof(f216,plain,
    ( spl9_17
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f210,f88,f212])).

fof(f210,plain,
    ( v5_relat_1(sK4,sK3)
    | ~ spl9_2 ),
    inference(resolution,[],[f79,f90])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f184,plain,
    ( spl9_14
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f178,f88,f180])).

fof(f178,plain,
    ( v1_relat_1(sK4)
    | ~ spl9_2 ),
    inference(resolution,[],[f76,f90])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f106,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f54,f103])).

fof(f103,plain,
    ( spl9_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f101,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f48,f98])).

fof(f48,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f96,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f49,f93])).

fof(f49,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f91,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f50,f88])).

fof(f50,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f35])).

fof(f86,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f53,f83])).

fof(f53,plain,(
    sK3 != k2_relset_1(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:12:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (13472)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.44  % (13472)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f494,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f86,f91,f96,f101,f106,f184,f216,f222,f234,f244,f254,f255,f340,f345,f383,f388,f486,f493])).
% 0.21/0.44  fof(f493,plain,(
% 0.21/0.44    k1_xboole_0 != sK3 | v1_xboole_0(sK3) | ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.44    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.44  fof(f486,plain,(
% 0.21/0.44    ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_23 | spl9_27 | ~spl9_33 | ~spl9_36 | ~spl9_37),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f485])).
% 0.21/0.44  fof(f485,plain,(
% 0.21/0.44    $false | (~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_23 | spl9_27 | ~spl9_33 | ~spl9_36 | ~spl9_37)),
% 0.21/0.44    inference(subsumption_resolution,[],[f484,f253])).
% 0.21/0.44  fof(f253,plain,(
% 0.21/0.44    ~r2_hidden(sK8(k2_relat_1(sK4),sK3),k2_relat_1(sK4)) | spl9_23),
% 0.21/0.44    inference(avatar_component_clause,[],[f251])).
% 0.21/0.44  fof(f251,plain,(
% 0.21/0.44    spl9_23 <=> r2_hidden(sK8(k2_relat_1(sK4),sK3),k2_relat_1(sK4))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 0.21/0.44  fof(f484,plain,(
% 0.21/0.44    r2_hidden(sK8(k2_relat_1(sK4),sK3),k2_relat_1(sK4)) | (~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_27 | ~spl9_33 | ~spl9_36 | ~spl9_37)),
% 0.21/0.44    inference(forward_demodulation,[],[f483,f387])).
% 0.21/0.44  fof(f387,plain,(
% 0.21/0.44    sK8(k2_relat_1(sK4),sK3) = k1_funct_1(sK4,sK5(sK8(k2_relat_1(sK4),sK3))) | ~spl9_37),
% 0.21/0.44    inference(avatar_component_clause,[],[f385])).
% 0.21/0.44  fof(f385,plain,(
% 0.21/0.44    spl9_37 <=> sK8(k2_relat_1(sK4),sK3) = k1_funct_1(sK4,sK5(sK8(k2_relat_1(sK4),sK3)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).
% 0.21/0.44  fof(f483,plain,(
% 0.21/0.44    r2_hidden(k1_funct_1(sK4,sK5(sK8(k2_relat_1(sK4),sK3))),k2_relat_1(sK4)) | (~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_27 | ~spl9_33 | ~spl9_36)),
% 0.21/0.44    inference(forward_demodulation,[],[f476,f344])).
% 0.21/0.44  fof(f344,plain,(
% 0.21/0.44    k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) | ~spl9_33),
% 0.21/0.44    inference(avatar_component_clause,[],[f342])).
% 0.21/0.44  fof(f342,plain,(
% 0.21/0.44    spl9_33 <=> k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).
% 0.21/0.44  fof(f476,plain,(
% 0.21/0.44    r2_hidden(k1_funct_1(sK4,sK5(sK8(k2_relat_1(sK4),sK3))),k2_relset_1(sK2,sK3,sK4)) | (~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_27 | ~spl9_36)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f100,f382,f286,f95,f90,f80])).
% 0.21/0.44  fof(f80,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f29])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.44    inference(flattening,[],[f28])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.44    inference(ennf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).
% 0.21/0.44  fof(f90,plain,(
% 0.21/0.44    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~spl9_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f88])).
% 0.21/0.44  fof(f88,plain,(
% 0.21/0.44    spl9_2 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.44  fof(f95,plain,(
% 0.21/0.44    v1_funct_2(sK4,sK2,sK3) | ~spl9_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f93])).
% 0.21/0.44  fof(f93,plain,(
% 0.21/0.44    spl9_3 <=> v1_funct_2(sK4,sK2,sK3)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.44  fof(f286,plain,(
% 0.21/0.44    k1_xboole_0 != sK3 | spl9_27),
% 0.21/0.44    inference(avatar_component_clause,[],[f284])).
% 0.21/0.44  fof(f284,plain,(
% 0.21/0.44    spl9_27 <=> k1_xboole_0 = sK3),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).
% 0.21/0.44  fof(f382,plain,(
% 0.21/0.44    r2_hidden(sK5(sK8(k2_relat_1(sK4),sK3)),sK2) | ~spl9_36),
% 0.21/0.44    inference(avatar_component_clause,[],[f380])).
% 0.21/0.44  fof(f380,plain,(
% 0.21/0.44    spl9_36 <=> r2_hidden(sK5(sK8(k2_relat_1(sK4),sK3)),sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).
% 0.21/0.44  fof(f100,plain,(
% 0.21/0.44    v1_funct_1(sK4) | ~spl9_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f98])).
% 0.21/0.44  fof(f98,plain,(
% 0.21/0.44    spl9_4 <=> v1_funct_1(sK4)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.44  fof(f388,plain,(
% 0.21/0.44    spl9_37 | ~spl9_21),
% 0.21/0.44    inference(avatar_split_clause,[],[f375,f241,f385])).
% 0.21/0.44  fof(f241,plain,(
% 0.21/0.44    spl9_21 <=> r2_hidden(sK8(k2_relat_1(sK4),sK3),sK3)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 0.21/0.44  fof(f375,plain,(
% 0.21/0.44    sK8(k2_relat_1(sK4),sK3) = k1_funct_1(sK4,sK5(sK8(k2_relat_1(sK4),sK3))) | ~spl9_21),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f243,f52])).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    ( ! [X3] : (k1_funct_1(sK4,sK5(X3)) = X3 | ~r2_hidden(X3,sK3)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f35])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    sK3 != k2_relset_1(sK2,sK3,sK4) & ! [X3] : ((k1_funct_1(sK4,sK5(X3)) = X3 & r2_hidden(sK5(X3),sK2)) | ~r2_hidden(X3,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f16,f34,f33])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (sK3 != k2_relset_1(sK2,sK3,sK4) & ! [X3] : (? [X4] : (k1_funct_1(sK4,X4) = X3 & r2_hidden(X4,sK2)) | ~r2_hidden(X3,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ! [X3] : (? [X4] : (k1_funct_1(sK4,X4) = X3 & r2_hidden(X4,sK2)) => (k1_funct_1(sK4,sK5(X3)) = X3 & r2_hidden(sK5(X3),sK2)))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.44    inference(flattening,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.44    inference(ennf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.44    inference(negated_conjecture,[],[f13])).
% 0.21/0.44  fof(f13,conjecture,(
% 0.21/0.44    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).
% 0.21/0.44  fof(f243,plain,(
% 0.21/0.44    r2_hidden(sK8(k2_relat_1(sK4),sK3),sK3) | ~spl9_21),
% 0.21/0.44    inference(avatar_component_clause,[],[f241])).
% 0.21/0.44  fof(f383,plain,(
% 0.21/0.44    spl9_36 | ~spl9_21),
% 0.21/0.44    inference(avatar_split_clause,[],[f376,f241,f380])).
% 0.21/0.44  fof(f376,plain,(
% 0.21/0.44    r2_hidden(sK5(sK8(k2_relat_1(sK4),sK3)),sK2) | ~spl9_21),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f243,f51])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    ( ! [X3] : (r2_hidden(sK5(X3),sK2) | ~r2_hidden(X3,sK3)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f35])).
% 0.21/0.44  fof(f345,plain,(
% 0.21/0.44    spl9_33 | ~spl9_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f331,f88,f342])).
% 0.21/0.44  fof(f331,plain,(
% 0.21/0.44    k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) | ~spl9_2),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f90,f77])).
% 0.21/0.44  fof(f77,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.44    inference(ennf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.44  fof(f340,plain,(
% 0.21/0.44    ~spl9_20 | spl9_1 | ~spl9_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f339,f88,f83,f231])).
% 0.21/0.44  fof(f231,plain,(
% 0.21/0.44    spl9_20 <=> sK3 = k2_relat_1(sK4)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 0.21/0.44  fof(f83,plain,(
% 0.21/0.44    spl9_1 <=> sK3 = k2_relset_1(sK2,sK3,sK4)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.44  fof(f339,plain,(
% 0.21/0.44    sK3 != k2_relat_1(sK4) | (spl9_1 | ~spl9_2)),
% 0.21/0.44    inference(subsumption_resolution,[],[f332,f90])).
% 0.21/0.44  fof(f332,plain,(
% 0.21/0.44    sK3 != k2_relat_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | spl9_1),
% 0.21/0.44    inference(superposition,[],[f85,f77])).
% 0.21/0.44  fof(f85,plain,(
% 0.21/0.44    sK3 != k2_relset_1(sK2,sK3,sK4) | spl9_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f83])).
% 0.21/0.44  fof(f255,plain,(
% 0.21/0.44    ~spl9_22 | ~spl9_19),
% 0.21/0.44    inference(avatar_split_clause,[],[f239,f227,f246])).
% 0.21/0.44  fof(f246,plain,(
% 0.21/0.44    spl9_22 <=> v1_xboole_0(sK3)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 0.21/0.44  fof(f227,plain,(
% 0.21/0.44    spl9_19 <=> r2_xboole_0(k2_relat_1(sK4),sK3)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 0.21/0.44  fof(f239,plain,(
% 0.21/0.44    ~v1_xboole_0(sK3) | ~spl9_19),
% 0.21/0.44    inference(resolution,[],[f229,f163])).
% 0.21/0.44  fof(f163,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | ~v1_xboole_0(X1)) )),
% 0.21/0.44    inference(resolution,[],[f73,f75])).
% 0.21/0.44  fof(f75,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_xboole_0(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f47])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    ! [X0,X1] : ((~r2_hidden(sK8(X0,X1),X0) & r2_hidden(sK8(X0,X1),X1)) | ~r2_xboole_0(X0,X1))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f23,f46])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (~r2_hidden(sK8(X0,X1),X0) & r2_hidden(sK8(X0,X1),X1)))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).
% 0.21/0.44  fof(f229,plain,(
% 0.21/0.44    r2_xboole_0(k2_relat_1(sK4),sK3) | ~spl9_19),
% 0.21/0.44    inference(avatar_component_clause,[],[f227])).
% 0.21/0.44  fof(f254,plain,(
% 0.21/0.44    ~spl9_23 | ~spl9_19),
% 0.21/0.44    inference(avatar_split_clause,[],[f235,f227,f251])).
% 0.21/0.44  fof(f235,plain,(
% 0.21/0.44    ~r2_hidden(sK8(k2_relat_1(sK4),sK3),k2_relat_1(sK4)) | ~spl9_19),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f229,f74])).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r2_hidden(sK8(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f47])).
% 0.21/0.44  fof(f244,plain,(
% 0.21/0.44    spl9_21 | ~spl9_19),
% 0.21/0.44    inference(avatar_split_clause,[],[f237,f227,f241])).
% 0.21/0.44  fof(f237,plain,(
% 0.21/0.44    r2_hidden(sK8(k2_relat_1(sK4),sK3),sK3) | ~spl9_19),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f229,f73])).
% 0.21/0.44  fof(f234,plain,(
% 0.21/0.44    spl9_19 | spl9_20 | ~spl9_18),
% 0.21/0.44    inference(avatar_split_clause,[],[f225,f219,f231,f227])).
% 0.21/0.44  fof(f219,plain,(
% 0.21/0.44    spl9_18 <=> r1_tarski(k2_relat_1(sK4),sK3)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 0.21/0.44  fof(f225,plain,(
% 0.21/0.44    sK3 = k2_relat_1(sK4) | r2_xboole_0(k2_relat_1(sK4),sK3) | ~spl9_18),
% 0.21/0.44    inference(resolution,[],[f221,f72])).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f45])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.44    inference(flattening,[],[f44])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.44    inference(nnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.44  fof(f221,plain,(
% 0.21/0.44    r1_tarski(k2_relat_1(sK4),sK3) | ~spl9_18),
% 0.21/0.44    inference(avatar_component_clause,[],[f219])).
% 0.21/0.44  fof(f222,plain,(
% 0.21/0.44    spl9_18 | ~spl9_14 | ~spl9_17),
% 0.21/0.44    inference(avatar_split_clause,[],[f217,f212,f180,f219])).
% 0.21/0.44  fof(f180,plain,(
% 0.21/0.44    spl9_14 <=> v1_relat_1(sK4)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.21/0.44  fof(f212,plain,(
% 0.21/0.44    spl9_17 <=> v5_relat_1(sK4,sK3)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 0.21/0.44  fof(f217,plain,(
% 0.21/0.44    r1_tarski(k2_relat_1(sK4),sK3) | (~spl9_14 | ~spl9_17)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f182,f214,f58])).
% 0.21/0.44  fof(f58,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f36])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(nnf_transformation,[],[f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.44  fof(f214,plain,(
% 0.21/0.44    v5_relat_1(sK4,sK3) | ~spl9_17),
% 0.21/0.44    inference(avatar_component_clause,[],[f212])).
% 0.21/0.44  fof(f182,plain,(
% 0.21/0.44    v1_relat_1(sK4) | ~spl9_14),
% 0.21/0.44    inference(avatar_component_clause,[],[f180])).
% 0.21/0.44  fof(f216,plain,(
% 0.21/0.44    spl9_17 | ~spl9_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f210,f88,f212])).
% 0.21/0.44  fof(f210,plain,(
% 0.21/0.44    v5_relat_1(sK4,sK3) | ~spl9_2),
% 0.21/0.44    inference(resolution,[],[f79,f90])).
% 0.21/0.44  fof(f79,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f27])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.44    inference(ennf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.44  fof(f184,plain,(
% 0.21/0.44    spl9_14 | ~spl9_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f178,f88,f180])).
% 0.21/0.44  fof(f178,plain,(
% 0.21/0.44    v1_relat_1(sK4) | ~spl9_2),
% 0.21/0.44    inference(resolution,[],[f76,f90])).
% 0.21/0.44  fof(f76,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.44    inference(ennf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.44  fof(f106,plain,(
% 0.21/0.44    spl9_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f54,f103])).
% 0.21/0.44  fof(f103,plain,(
% 0.21/0.44    spl9_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    v1_xboole_0(k1_xboole_0)),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    v1_xboole_0(k1_xboole_0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.44  fof(f101,plain,(
% 0.21/0.44    spl9_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f48,f98])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    v1_funct_1(sK4)),
% 0.21/0.44    inference(cnf_transformation,[],[f35])).
% 0.21/0.44  fof(f96,plain,(
% 0.21/0.44    spl9_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f49,f93])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    v1_funct_2(sK4,sK2,sK3)),
% 0.21/0.44    inference(cnf_transformation,[],[f35])).
% 0.21/0.44  fof(f91,plain,(
% 0.21/0.44    spl9_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f50,f88])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 0.21/0.44    inference(cnf_transformation,[],[f35])).
% 0.21/0.44  fof(f86,plain,(
% 0.21/0.44    ~spl9_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f53,f83])).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    sK3 != k2_relset_1(sK2,sK3,sK4)),
% 0.21/0.44    inference(cnf_transformation,[],[f35])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (13472)------------------------------
% 0.21/0.44  % (13472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (13472)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (13472)Memory used [KB]: 11001
% 0.21/0.44  % (13472)Time elapsed: 0.037 s
% 0.21/0.44  % (13472)------------------------------
% 0.21/0.44  % (13472)------------------------------
% 0.21/0.45  % (13454)Success in time 0.08 s
%------------------------------------------------------------------------------
