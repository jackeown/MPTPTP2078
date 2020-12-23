%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:33 EST 2020

% Result     : Theorem 1.94s
% Output     : Refutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :  270 ( 615 expanded)
%              Number of leaves         :   55 ( 223 expanded)
%              Depth                    :   14
%              Number of atoms          :  788 (1898 expanded)
%              Number of equality atoms :   98 ( 298 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f727,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f104,f113,f119,f126,f137,f146,f159,f182,f195,f220,f226,f260,f317,f369,f397,f401,f412,f416,f425,f446,f459,f465,f466,f481,f498,f509,f537,f563,f660,f671,f695,f706,f714,f726])).

fof(f726,plain,
    ( spl6_53
    | ~ spl6_55
    | ~ spl6_56 ),
    inference(avatar_contradiction_clause,[],[f725])).

fof(f725,plain,
    ( $false
    | spl6_53
    | ~ spl6_55
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f724,f694])).

fof(f694,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl6_53 ),
    inference(avatar_component_clause,[],[f692])).

fof(f692,plain,
    ( spl6_53
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f724,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_55
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f723,f705])).

fof(f705,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_55 ),
    inference(avatar_component_clause,[],[f703])).

fof(f703,plain,
    ( spl6_55
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f723,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_56 ),
    inference(trivial_inequality_removal,[],[f721])).

fof(f721,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_56 ),
    inference(superposition,[],[f91,f713])).

fof(f713,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_56 ),
    inference(avatar_component_clause,[],[f711])).

fof(f711,plain,
    ( spl6_56
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f91,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f714,plain,
    ( spl6_56
    | ~ spl6_18
    | ~ spl6_42
    | ~ spl6_46
    | spl6_49
    | ~ spl6_51 ),
    inference(avatar_split_clause,[],[f682,f668,f657,f560,f534,f223,f711])).

fof(f223,plain,
    ( spl6_18
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f534,plain,
    ( spl6_42
  <=> m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f560,plain,
    ( spl6_46
  <=> sK1 = k1_relset_1(sK1,k1_xboole_0,k7_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f657,plain,
    ( spl6_49
  <=> v1_funct_2(k1_xboole_0,sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f668,plain,
    ( spl6_51
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f682,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_18
    | ~ spl6_42
    | ~ spl6_46
    | spl6_49
    | ~ spl6_51 ),
    inference(backward_demodulation,[],[f643,f675])).

fof(f675,plain,
    ( k1_xboole_0 = sK1
    | spl6_49
    | ~ spl6_51 ),
    inference(subsumption_resolution,[],[f672,f659])).

fof(f659,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK1,k1_xboole_0)
    | spl6_49 ),
    inference(avatar_component_clause,[],[f657])).

fof(f672,plain,
    ( k1_xboole_0 = sK1
    | v1_funct_2(k1_xboole_0,sK1,k1_xboole_0)
    | ~ spl6_51 ),
    inference(resolution,[],[f670,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 != X2
      | v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != X2
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f670,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f668])).

fof(f643,plain,
    ( sK1 = k1_relset_1(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl6_18
    | ~ spl6_42
    | ~ spl6_46 ),
    inference(backward_demodulation,[],[f562,f632])).

fof(f632,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK1)
    | ~ spl6_18
    | ~ spl6_42 ),
    inference(resolution,[],[f616,f56])).

fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f616,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k7_relat_1(sK4,sK1))
        | k7_relat_1(sK4,sK1) = X0 )
    | ~ spl6_18
    | ~ spl6_42 ),
    inference(resolution,[],[f607,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f607,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK4,sK1),X0)
    | ~ spl6_18
    | ~ spl6_42 ),
    inference(resolution,[],[f603,f89])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f603,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k7_relat_1(sK4,sK1))
        | r1_tarski(X0,X1) )
    | ~ spl6_18
    | ~ spl6_42 ),
    inference(resolution,[],[f601,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f601,plain,
    ( ! [X8,X9] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(k7_relat_1(sK4,sK1)))
        | r1_tarski(X8,X9) )
    | ~ spl6_18
    | ~ spl6_42 ),
    inference(resolution,[],[f382,f536])).

fof(f536,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f534])).

fof(f382,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_xboole_0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X3) )
    | ~ spl6_18 ),
    inference(resolution,[],[f320,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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

fof(f320,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(X3,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) )
    | ~ spl6_18 ),
    inference(resolution,[],[f235,f225])).

fof(f225,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f223])).

fof(f235,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ r2_hidden(X4,X3) ) ),
    inference(resolution,[],[f59,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f562,plain,
    ( sK1 = k1_relset_1(sK1,k1_xboole_0,k7_relat_1(sK4,sK1))
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f560])).

fof(f706,plain,
    ( spl6_55
    | spl6_49
    | ~ spl6_51 ),
    inference(avatar_split_clause,[],[f685,f668,f657,f703])).

fof(f685,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl6_49
    | ~ spl6_51 ),
    inference(backward_demodulation,[],[f670,f675])).

fof(f695,plain,
    ( ~ spl6_53
    | spl6_49
    | ~ spl6_51 ),
    inference(avatar_split_clause,[],[f684,f668,f657,f692])).

fof(f684,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl6_49
    | ~ spl6_51 ),
    inference(backward_demodulation,[],[f659,f675])).

fof(f671,plain,
    ( spl6_51
    | ~ spl6_18
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f640,f534,f223,f668])).

fof(f640,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl6_18
    | ~ spl6_42 ),
    inference(backward_demodulation,[],[f536,f632])).

fof(f660,plain,
    ( ~ spl6_49
    | ~ spl6_18
    | spl6_40
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f639,f534,f495,f223,f657])).

fof(f495,plain,
    ( spl6_40
  <=> v1_funct_2(k7_relat_1(sK4,sK1),sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f639,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK1,k1_xboole_0)
    | ~ spl6_18
    | spl6_40
    | ~ spl6_42 ),
    inference(backward_demodulation,[],[f497,f632])).

fof(f497,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,k1_xboole_0)
    | spl6_40 ),
    inference(avatar_component_clause,[],[f495])).

fof(f563,plain,
    ( spl6_46
    | ~ spl6_19
    | ~ spl6_36
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f518,f443,f439,f253,f560])).

fof(f253,plain,
    ( spl6_19
  <=> sK2 = k7_relset_1(sK0,sK3,sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f439,plain,
    ( spl6_36
  <=> sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f443,plain,
    ( spl6_37
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f518,plain,
    ( sK1 = k1_relset_1(sK1,k1_xboole_0,k7_relat_1(sK4,sK1))
    | ~ spl6_19
    | ~ spl6_36
    | ~ spl6_37 ),
    inference(backward_demodulation,[],[f440,f512])).

fof(f512,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_19
    | ~ spl6_37 ),
    inference(backward_demodulation,[],[f255,f492])).

fof(f492,plain,
    ( k1_xboole_0 = k7_relset_1(sK0,sK3,sK4,sK1)
    | ~ spl6_19
    | ~ spl6_37 ),
    inference(forward_demodulation,[],[f255,f445])).

fof(f445,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f443])).

fof(f255,plain,
    ( sK2 = k7_relset_1(sK0,sK3,sK4,sK1)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f253])).

fof(f440,plain,
    ( sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f439])).

fof(f537,plain,
    ( spl6_42
    | ~ spl6_19
    | ~ spl6_22
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f513,f443,f291,f253,f534])).

fof(f291,plain,
    ( spl6_22
  <=> m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f513,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl6_19
    | ~ spl6_22
    | ~ spl6_37 ),
    inference(backward_demodulation,[],[f292,f512])).

fof(f292,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f291])).

fof(f509,plain,
    ( ~ spl6_1
    | ~ spl6_5
    | spl6_11 ),
    inference(avatar_contradiction_clause,[],[f508])).

fof(f508,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_5
    | spl6_11 ),
    inference(subsumption_resolution,[],[f507,f277])).

fof(f277,plain,
    ( ! [X0] : v1_funct_1(k7_relat_1(sK4,X0))
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f248,f271])).

fof(f271,plain,
    ( ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK0,sK3,sK4,X0)
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(resolution,[],[f107,f125])).

fof(f125,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl6_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f107,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | k2_partfun1(X6,X7,sK4,X8) = k7_relat_1(sK4,X8) )
    | ~ spl6_1 ),
    inference(resolution,[],[f98,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f98,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl6_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f248,plain,
    ( ! [X0] : v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0))
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(resolution,[],[f105,f125])).

fof(f105,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_funct_1(k2_partfun1(X0,X1,sK4,X2)) )
    | ~ spl6_1 ),
    inference(resolution,[],[f98,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f507,plain,
    ( ~ v1_funct_1(k7_relat_1(sK4,sK1))
    | ~ spl6_1
    | ~ spl6_5
    | spl6_11 ),
    inference(forward_demodulation,[],[f158,f271])).

fof(f158,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl6_11
  <=> v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f498,plain,
    ( ~ spl6_40
    | spl6_35
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f477,f443,f422,f495])).

fof(f422,plain,
    ( spl6_35
  <=> v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f477,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,k1_xboole_0)
    | spl6_35
    | ~ spl6_37 ),
    inference(backward_demodulation,[],[f424,f445])).

fof(f424,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | spl6_35 ),
    inference(avatar_component_clause,[],[f422])).

fof(f481,plain,
    ( spl6_20
    | ~ spl6_37 ),
    inference(avatar_contradiction_clause,[],[f480])).

fof(f480,plain,
    ( $false
    | spl6_20
    | ~ spl6_37 ),
    inference(subsumption_resolution,[],[f472,f56])).

fof(f472,plain,
    ( ~ r1_tarski(k1_xboole_0,k7_relset_1(sK0,sK3,sK4,sK1))
    | spl6_20
    | ~ spl6_37 ),
    inference(backward_demodulation,[],[f259,f445])).

fof(f259,plain,
    ( ~ r1_tarski(sK2,k7_relset_1(sK0,sK3,sK4,sK1))
    | spl6_20 ),
    inference(avatar_component_clause,[],[f257])).

fof(f257,plain,
    ( spl6_20
  <=> r1_tarski(sK2,k7_relset_1(sK0,sK3,sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f466,plain,
    ( sK1 != k1_relat_1(k7_relat_1(sK4,sK1))
    | r1_tarski(sK1,k1_relat_1(k7_relat_1(sK4,sK1)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f465,plain,
    ( ~ spl6_3
    | ~ spl6_17
    | ~ spl6_33
    | spl6_38 ),
    inference(avatar_contradiction_clause,[],[f464])).

fof(f464,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_17
    | ~ spl6_33
    | spl6_38 ),
    inference(subsumption_resolution,[],[f463,f112])).

fof(f112,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl6_3
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f463,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl6_17
    | ~ spl6_33
    | spl6_38 ),
    inference(forward_demodulation,[],[f462,f194])).

fof(f194,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl6_17
  <=> sK0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f462,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK4))
    | ~ spl6_33
    | spl6_38 ),
    inference(subsumption_resolution,[],[f461,f360])).

fof(f360,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f359])).

fof(f359,plain,
    ( spl6_33
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f461,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | spl6_38 ),
    inference(trivial_inequality_removal,[],[f460])).

fof(f460,plain,
    ( sK1 != sK1
    | ~ r1_tarski(sK1,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | spl6_38 ),
    inference(superposition,[],[f453,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f453,plain,
    ( sK1 != k1_relat_1(k7_relat_1(sK4,sK1))
    | spl6_38 ),
    inference(avatar_component_clause,[],[f451])).

fof(f451,plain,
    ( spl6_38
  <=> sK1 = k1_relat_1(k7_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f459,plain,
    ( ~ spl6_39
    | ~ spl6_22
    | ~ spl6_25
    | spl6_36 ),
    inference(avatar_split_clause,[],[f449,f439,f310,f291,f456])).

fof(f456,plain,
    ( spl6_39
  <=> r1_tarski(sK1,k1_relat_1(k7_relat_1(sK4,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f310,plain,
    ( spl6_25
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f449,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(k7_relat_1(sK4,sK1)))
    | ~ spl6_22
    | ~ spl6_25
    | spl6_36 ),
    inference(subsumption_resolution,[],[f407,f448])).

fof(f448,plain,
    ( sK1 != k1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl6_22
    | spl6_36 ),
    inference(subsumption_resolution,[],[f447,f292])).

fof(f447,plain,
    ( sK1 != k1_relat_1(k7_relat_1(sK4,sK1))
    | ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl6_36 ),
    inference(superposition,[],[f441,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f441,plain,
    ( sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | spl6_36 ),
    inference(avatar_component_clause,[],[f439])).

fof(f407,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(k7_relat_1(sK4,sK1)))
    | sK1 = k1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl6_25 ),
    inference(resolution,[],[f311,f66])).

fof(f311,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f310])).

fof(f446,plain,
    ( ~ spl6_36
    | spl6_37
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_9
    | spl6_35 ),
    inference(avatar_split_clause,[],[f427,f422,f148,f123,f96,f443,f439])).

fof(f148,plain,
    ( spl6_9
  <=> m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f427,plain,
    ( k1_xboole_0 = sK2
    | sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_9
    | spl6_35 ),
    inference(subsumption_resolution,[],[f426,f418])).

fof(f418,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f149,f271])).

fof(f149,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f148])).

fof(f426,plain,
    ( k1_xboole_0 = sK2
    | sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl6_35 ),
    inference(resolution,[],[f424,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f425,plain,
    ( ~ spl6_35
    | ~ spl6_1
    | ~ spl6_5
    | spl6_10 ),
    inference(avatar_split_clause,[],[f417,f152,f123,f96,f422])).

fof(f152,plain,
    ( spl6_10
  <=> v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f417,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | ~ spl6_1
    | ~ spl6_5
    | spl6_10 ),
    inference(forward_demodulation,[],[f154,f271])).

fof(f154,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f152])).

fof(f416,plain,
    ( spl6_22
    | ~ spl6_24
    | ~ spl6_25
    | ~ spl6_26 ),
    inference(avatar_contradiction_clause,[],[f415])).

fof(f415,plain,
    ( $false
    | spl6_22
    | ~ spl6_24
    | ~ spl6_25
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f315,f414])).

fof(f414,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)
    | spl6_22
    | ~ spl6_24
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f413,f307])).

fof(f307,plain,
    ( v1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f306])).

fof(f306,plain,
    ( spl6_24
  <=> v1_relat_1(k7_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f413,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)
    | ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | spl6_22
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f295,f311])).

fof(f295,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)
    | ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | spl6_22 ),
    inference(resolution,[],[f293,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f293,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl6_22 ),
    inference(avatar_component_clause,[],[f291])).

fof(f315,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f314])).

fof(f314,plain,
    ( spl6_26
  <=> r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f412,plain,
    ( ~ spl6_8
    | spl6_26
    | ~ spl6_33 ),
    inference(avatar_contradiction_clause,[],[f411])).

fof(f411,plain,
    ( $false
    | ~ spl6_8
    | spl6_26
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f410,f360])).

fof(f410,plain,
    ( ~ v1_relat_1(sK4)
    | ~ spl6_8
    | spl6_26 ),
    inference(subsumption_resolution,[],[f409,f145])).

fof(f145,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl6_8
  <=> r1_tarski(k9_relat_1(sK4,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f409,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | ~ v1_relat_1(sK4)
    | spl6_26 ),
    inference(superposition,[],[f316,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f316,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)
    | spl6_26 ),
    inference(avatar_component_clause,[],[f314])).

fof(f401,plain,
    ( spl6_25
    | ~ spl6_33 ),
    inference(avatar_contradiction_clause,[],[f400])).

fof(f400,plain,
    ( $false
    | spl6_25
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f398,f360])).

fof(f398,plain,
    ( ~ v1_relat_1(sK4)
    | spl6_25 ),
    inference(resolution,[],[f312,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f312,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | spl6_25 ),
    inference(avatar_component_clause,[],[f310])).

fof(f397,plain,
    ( ~ spl6_1
    | ~ spl6_5
    | spl6_24 ),
    inference(avatar_contradiction_clause,[],[f396])).

fof(f396,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_5
    | spl6_24 ),
    inference(subsumption_resolution,[],[f393,f58])).

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f393,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK3))
    | ~ spl6_1
    | ~ spl6_5
    | spl6_24 ),
    inference(resolution,[],[f381,f324])).

fof(f324,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k7_relat_1(sK4,sK1),X0)
        | ~ v1_relat_1(X0) )
    | spl6_24 ),
    inference(resolution,[],[f319,f70])).

fof(f319,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(X2))
        | ~ v1_relat_1(X2) )
    | spl6_24 ),
    inference(resolution,[],[f308,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f308,plain,
    ( ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | spl6_24 ),
    inference(avatar_component_clause,[],[f306])).

fof(f381,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK4,X0),k2_zfmisc_1(sK0,sK3))
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f380,f125])).

fof(f380,plain,
    ( ! [X0] :
        ( r1_tarski(k7_relat_1(sK4,X0),k2_zfmisc_1(sK0,sK3))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) )
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(superposition,[],[f302,f271])).

fof(f302,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k2_partfun1(X0,X1,sK4,X2),k2_zfmisc_1(X0,X1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_1 ),
    inference(resolution,[],[f106,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f106,plain,
    ( ! [X4,X5,X3] :
        ( m1_subset_1(k2_partfun1(X3,X4,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
    | ~ spl6_1 ),
    inference(resolution,[],[f98,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f369,plain,
    ( ~ spl6_5
    | spl6_33 ),
    inference(avatar_contradiction_clause,[],[f368])).

fof(f368,plain,
    ( $false
    | ~ spl6_5
    | spl6_33 ),
    inference(subsumption_resolution,[],[f125,f366])).

fof(f366,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_33 ),
    inference(resolution,[],[f361,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f361,plain,
    ( ~ v1_relat_1(sK4)
    | spl6_33 ),
    inference(avatar_component_clause,[],[f359])).

fof(f317,plain,
    ( ~ spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_1
    | ~ spl6_5
    | spl6_9 ),
    inference(avatar_split_clause,[],[f282,f148,f123,f96,f314,f310,f306])).

fof(f282,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl6_1
    | ~ spl6_5
    | spl6_9 ),
    inference(forward_demodulation,[],[f281,f271])).

fof(f281,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2)
    | ~ spl6_1
    | ~ spl6_5
    | spl6_9 ),
    inference(forward_demodulation,[],[f275,f271])).

fof(f275,plain,
    ( ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | ~ r1_tarski(k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK1)
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2)
    | ~ spl6_1
    | ~ spl6_5
    | spl6_9 ),
    inference(backward_demodulation,[],[f161,f271])).

fof(f161,plain,
    ( ~ r1_tarski(k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK1)
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2)
    | ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | spl6_9 ),
    inference(resolution,[],[f150,f72])).

fof(f150,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f148])).

fof(f260,plain,
    ( spl6_19
    | ~ spl6_20
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f139,f134,f257,f253])).

fof(f134,plain,
    ( spl6_7
  <=> r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f139,plain,
    ( ~ r1_tarski(sK2,k7_relset_1(sK0,sK3,sK4,sK1))
    | sK2 = k7_relset_1(sK0,sK3,sK4,sK1)
    | ~ spl6_7 ),
    inference(resolution,[],[f136,f66])).

fof(f136,plain,
    ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f134])).

fof(f226,plain,(
    spl6_18 ),
    inference(avatar_split_clause,[],[f55,f223])).

fof(f55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f220,plain,
    ( spl6_2
    | ~ spl6_15 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | spl6_2
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f55,f217])).

fof(f217,plain,
    ( ! [X2] : ~ v1_xboole_0(X2)
    | spl6_2
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f207,f56])).

fof(f207,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X3,X2))
        | ~ v1_xboole_0(X2) )
    | spl6_2
    | ~ spl6_15 ),
    inference(backward_demodulation,[],[f173,f181])).

fof(f181,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl6_15
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f173,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(sK3,k2_zfmisc_1(X3,X2))
        | ~ v1_xboole_0(X2) )
    | spl6_2 ),
    inference(resolution,[],[f108,f70])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_xboole_0(X1) )
    | spl6_2 ),
    inference(resolution,[],[f103,f59])).

fof(f103,plain,
    ( ~ v1_xboole_0(sK3)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl6_2
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f195,plain,
    ( spl6_17
    | ~ spl6_5
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f185,f175,f123,f192])).

fof(f175,plain,
    ( spl6_14
  <=> sK0 = k1_relset_1(sK0,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f185,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl6_5
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f183,f125])).

fof(f183,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ spl6_14 ),
    inference(superposition,[],[f177,f74])).

fof(f177,plain,
    ( sK0 = k1_relset_1(sK0,sK3,sK4)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f175])).

fof(f182,plain,
    ( spl6_14
    | spl6_15
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f121,f116,f179,f175])).

fof(f116,plain,
    ( spl6_4
  <=> v1_funct_2(sK4,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f121,plain,
    ( k1_xboole_0 = sK3
    | sK0 = k1_relset_1(sK0,sK3,sK4)
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f120,f51])).

fof(f51,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ~ v1_xboole_0(X3)
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
              & v1_funct_2(X4,X0,X3)
              & v1_funct_1(X4) )
           => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
                & r1_tarski(X1,X0) )
             => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
                & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
            & v1_funct_2(X4,X0,X3)
            & v1_funct_1(X4) )
         => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
              & r1_tarski(X1,X0) )
           => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
              & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_funct_2)).

fof(f120,plain,
    ( k1_xboole_0 = sK3
    | sK0 = k1_relset_1(sK0,sK3,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ spl6_4 ),
    inference(resolution,[],[f118,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f118,plain,
    ( v1_funct_2(sK4,sK0,sK3)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f116])).

fof(f159,plain,
    ( ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f48,f156,f152,f148])).

fof(f48,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f25])).

fof(f146,plain,
    ( spl6_8
    | ~ spl6_5
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f141,f134,f123,f143])).

fof(f141,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | ~ spl6_5
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f140,f125])).

fof(f140,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ spl6_7 ),
    inference(superposition,[],[f136,f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f137,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f53,f134])).

fof(f53,plain,(
    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f126,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f51,f123])).

fof(f119,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f50,f116])).

fof(f50,plain,(
    v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f113,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f52,f110])).

fof(f52,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f104,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f54,f101])).

fof(f54,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f99,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f49,f96])).

fof(f49,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 14:40:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.48  % (6143)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.23/0.50  % (6176)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.10/0.52  % (6158)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.10/0.52  % (6159)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.10/0.53  % (6150)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.27/0.53  % (6156)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.27/0.55  % (6146)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.27/0.55  % (6145)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.27/0.55  % (6144)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.27/0.55  % (6173)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.27/0.56  % (6172)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.27/0.56  % (6174)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.27/0.56  % (6175)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.27/0.56  % (6148)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.27/0.56  % (6161)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.27/0.56  % (6149)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.27/0.56  % (6162)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.27/0.56  % (6166)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.27/0.56  % (6164)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.27/0.57  % (6155)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.27/0.57  % (6151)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.27/0.57  % (6169)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.27/0.57  % (6154)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.27/0.57  % (6165)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.27/0.57  % (6168)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.27/0.58  % (6170)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.27/0.58  % (6157)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.27/0.58  % (6153)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.27/0.58  % (6160)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.27/0.59  % (6163)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.27/0.60  % (6168)Refutation not found, incomplete strategy% (6168)------------------------------
% 1.27/0.60  % (6168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.60  % (6168)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.60  
% 1.27/0.60  % (6168)Memory used [KB]: 10874
% 1.27/0.60  % (6168)Time elapsed: 0.134 s
% 1.27/0.60  % (6168)------------------------------
% 1.27/0.60  % (6168)------------------------------
% 1.94/0.63  % (6165)Refutation found. Thanks to Tanya!
% 1.94/0.63  % SZS status Theorem for theBenchmark
% 1.94/0.63  % SZS output start Proof for theBenchmark
% 1.94/0.63  fof(f727,plain,(
% 1.94/0.63    $false),
% 1.94/0.63    inference(avatar_sat_refutation,[],[f99,f104,f113,f119,f126,f137,f146,f159,f182,f195,f220,f226,f260,f317,f369,f397,f401,f412,f416,f425,f446,f459,f465,f466,f481,f498,f509,f537,f563,f660,f671,f695,f706,f714,f726])).
% 1.94/0.63  fof(f726,plain,(
% 1.94/0.63    spl6_53 | ~spl6_55 | ~spl6_56),
% 1.94/0.63    inference(avatar_contradiction_clause,[],[f725])).
% 1.94/0.63  fof(f725,plain,(
% 1.94/0.63    $false | (spl6_53 | ~spl6_55 | ~spl6_56)),
% 1.94/0.63    inference(subsumption_resolution,[],[f724,f694])).
% 1.94/0.63  fof(f694,plain,(
% 1.94/0.63    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | spl6_53),
% 1.94/0.63    inference(avatar_component_clause,[],[f692])).
% 1.94/0.63  fof(f692,plain,(
% 1.94/0.63    spl6_53 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 1.94/0.63  fof(f724,plain,(
% 1.94/0.63    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl6_55 | ~spl6_56)),
% 1.94/0.63    inference(subsumption_resolution,[],[f723,f705])).
% 1.94/0.63  fof(f705,plain,(
% 1.94/0.63    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl6_55),
% 1.94/0.63    inference(avatar_component_clause,[],[f703])).
% 1.94/0.63  fof(f703,plain,(
% 1.94/0.63    spl6_55 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).
% 1.94/0.63  fof(f723,plain,(
% 1.94/0.63    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl6_56),
% 1.94/0.63    inference(trivial_inequality_removal,[],[f721])).
% 1.94/0.63  fof(f721,plain,(
% 1.94/0.63    k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl6_56),
% 1.94/0.63    inference(superposition,[],[f91,f713])).
% 1.94/0.63  fof(f713,plain,(
% 1.94/0.63    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl6_56),
% 1.94/0.63    inference(avatar_component_clause,[],[f711])).
% 1.94/0.63  fof(f711,plain,(
% 1.94/0.63    spl6_56 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).
% 1.94/0.63  fof(f91,plain,(
% 1.94/0.63    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.94/0.63    inference(equality_resolution,[],[f79])).
% 1.94/0.63  fof(f79,plain,(
% 1.94/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 1.94/0.63    inference(cnf_transformation,[],[f41])).
% 1.94/0.63  fof(f41,plain,(
% 1.94/0.63    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.94/0.63    inference(flattening,[],[f40])).
% 1.94/0.63  fof(f40,plain,(
% 1.94/0.63    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.94/0.63    inference(ennf_transformation,[],[f19])).
% 1.94/0.63  fof(f19,axiom,(
% 1.94/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.94/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.94/0.63  fof(f714,plain,(
% 1.94/0.63    spl6_56 | ~spl6_18 | ~spl6_42 | ~spl6_46 | spl6_49 | ~spl6_51),
% 1.94/0.63    inference(avatar_split_clause,[],[f682,f668,f657,f560,f534,f223,f711])).
% 1.94/0.63  fof(f223,plain,(
% 1.94/0.63    spl6_18 <=> v1_xboole_0(k1_xboole_0)),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.94/0.63  fof(f534,plain,(
% 1.94/0.63    spl6_42 <=> m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 1.94/0.63  fof(f560,plain,(
% 1.94/0.63    spl6_46 <=> sK1 = k1_relset_1(sK1,k1_xboole_0,k7_relat_1(sK4,sK1))),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 1.94/0.63  fof(f657,plain,(
% 1.94/0.63    spl6_49 <=> v1_funct_2(k1_xboole_0,sK1,k1_xboole_0)),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).
% 1.94/0.63  fof(f668,plain,(
% 1.94/0.63    spl6_51 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).
% 1.94/0.63  fof(f682,plain,(
% 1.94/0.63    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl6_18 | ~spl6_42 | ~spl6_46 | spl6_49 | ~spl6_51)),
% 1.94/0.63    inference(backward_demodulation,[],[f643,f675])).
% 1.94/0.63  fof(f675,plain,(
% 1.94/0.63    k1_xboole_0 = sK1 | (spl6_49 | ~spl6_51)),
% 1.94/0.63    inference(subsumption_resolution,[],[f672,f659])).
% 1.94/0.63  fof(f659,plain,(
% 1.94/0.63    ~v1_funct_2(k1_xboole_0,sK1,k1_xboole_0) | spl6_49),
% 1.94/0.63    inference(avatar_component_clause,[],[f657])).
% 1.94/0.63  fof(f672,plain,(
% 1.94/0.63    k1_xboole_0 = sK1 | v1_funct_2(k1_xboole_0,sK1,k1_xboole_0) | ~spl6_51),
% 1.94/0.63    inference(resolution,[],[f670,f94])).
% 1.94/0.63  fof(f94,plain,(
% 1.94/0.63    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)) )),
% 1.94/0.63    inference(equality_resolution,[],[f93])).
% 1.94/0.63  fof(f93,plain,(
% 1.94/0.63    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,k1_xboole_0)) )),
% 1.94/0.63    inference(equality_resolution,[],[f77])).
% 1.94/0.63  fof(f77,plain,(
% 1.94/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,X1)) )),
% 1.94/0.63    inference(cnf_transformation,[],[f41])).
% 1.94/0.63  fof(f670,plain,(
% 1.94/0.63    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | ~spl6_51),
% 1.94/0.63    inference(avatar_component_clause,[],[f668])).
% 1.94/0.63  fof(f643,plain,(
% 1.94/0.63    sK1 = k1_relset_1(sK1,k1_xboole_0,k1_xboole_0) | (~spl6_18 | ~spl6_42 | ~spl6_46)),
% 1.94/0.63    inference(backward_demodulation,[],[f562,f632])).
% 1.94/0.63  fof(f632,plain,(
% 1.94/0.63    k1_xboole_0 = k7_relat_1(sK4,sK1) | (~spl6_18 | ~spl6_42)),
% 1.94/0.63    inference(resolution,[],[f616,f56])).
% 1.94/0.63  fof(f56,plain,(
% 1.94/0.63    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.94/0.63    inference(cnf_transformation,[],[f4])).
% 1.94/0.63  fof(f4,axiom,(
% 1.94/0.63    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.94/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.94/0.63  fof(f616,plain,(
% 1.94/0.63    ( ! [X0] : (~r1_tarski(X0,k7_relat_1(sK4,sK1)) | k7_relat_1(sK4,sK1) = X0) ) | (~spl6_18 | ~spl6_42)),
% 1.94/0.63    inference(resolution,[],[f607,f66])).
% 1.94/0.63  fof(f66,plain,(
% 1.94/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.94/0.63    inference(cnf_transformation,[],[f3])).
% 1.94/0.63  fof(f3,axiom,(
% 1.94/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.94/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.94/0.63  fof(f607,plain,(
% 1.94/0.63    ( ! [X0] : (r1_tarski(k7_relat_1(sK4,sK1),X0)) ) | (~spl6_18 | ~spl6_42)),
% 1.94/0.63    inference(resolution,[],[f603,f89])).
% 1.94/0.63  fof(f89,plain,(
% 1.94/0.63    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.94/0.63    inference(equality_resolution,[],[f64])).
% 1.94/0.63  fof(f64,plain,(
% 1.94/0.63    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.94/0.63    inference(cnf_transformation,[],[f3])).
% 1.94/0.63  fof(f603,plain,(
% 1.94/0.63    ( ! [X0,X1] : (~r1_tarski(X0,k7_relat_1(sK4,sK1)) | r1_tarski(X0,X1)) ) | (~spl6_18 | ~spl6_42)),
% 1.94/0.63    inference(resolution,[],[f601,f70])).
% 1.94/0.63  fof(f70,plain,(
% 1.94/0.63    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.94/0.63    inference(cnf_transformation,[],[f5])).
% 1.94/0.63  fof(f5,axiom,(
% 1.94/0.63    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.94/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.94/0.63  fof(f601,plain,(
% 1.94/0.63    ( ! [X8,X9] : (~m1_subset_1(X8,k1_zfmisc_1(k7_relat_1(sK4,sK1))) | r1_tarski(X8,X9)) ) | (~spl6_18 | ~spl6_42)),
% 1.94/0.63    inference(resolution,[],[f382,f536])).
% 1.94/0.63  fof(f536,plain,(
% 1.94/0.63    m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | ~spl6_42),
% 1.94/0.63    inference(avatar_component_clause,[],[f534])).
% 1.94/0.63  fof(f382,plain,(
% 1.94/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_xboole_0))) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X3)) ) | ~spl6_18),
% 1.94/0.63    inference(resolution,[],[f320,f68])).
% 1.94/0.63  fof(f68,plain,(
% 1.94/0.63    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.94/0.63    inference(cnf_transformation,[],[f34])).
% 1.94/0.63  fof(f34,plain,(
% 1.94/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.94/0.63    inference(ennf_transformation,[],[f1])).
% 1.94/0.63  fof(f1,axiom,(
% 1.94/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.94/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.94/0.63  fof(f320,plain,(
% 1.94/0.63    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))) ) | ~spl6_18),
% 1.94/0.63    inference(resolution,[],[f235,f225])).
% 1.94/0.63  fof(f225,plain,(
% 1.94/0.63    v1_xboole_0(k1_xboole_0) | ~spl6_18),
% 1.94/0.63    inference(avatar_component_clause,[],[f223])).
% 1.94/0.63  fof(f235,plain,(
% 1.94/0.63    ( ! [X4,X2,X0,X3,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~r2_hidden(X4,X3)) )),
% 1.94/0.63    inference(resolution,[],[f59,f83])).
% 1.94/0.63  fof(f83,plain,(
% 1.94/0.63    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.94/0.63    inference(cnf_transformation,[],[f42])).
% 1.94/0.63  fof(f42,plain,(
% 1.94/0.63    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.94/0.63    inference(ennf_transformation,[],[f6])).
% 1.94/0.63  fof(f6,axiom,(
% 1.94/0.63    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.94/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.94/0.63  fof(f59,plain,(
% 1.94/0.63    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 1.94/0.63    inference(cnf_transformation,[],[f27])).
% 1.94/0.63  fof(f27,plain,(
% 1.94/0.63    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 1.94/0.63    inference(ennf_transformation,[],[f15])).
% 1.94/0.63  fof(f15,axiom,(
% 1.94/0.63    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 1.94/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 1.94/0.63  fof(f562,plain,(
% 1.94/0.63    sK1 = k1_relset_1(sK1,k1_xboole_0,k7_relat_1(sK4,sK1)) | ~spl6_46),
% 1.94/0.63    inference(avatar_component_clause,[],[f560])).
% 1.94/0.63  fof(f706,plain,(
% 1.94/0.63    spl6_55 | spl6_49 | ~spl6_51),
% 1.94/0.63    inference(avatar_split_clause,[],[f685,f668,f657,f703])).
% 1.94/0.63  fof(f685,plain,(
% 1.94/0.63    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (spl6_49 | ~spl6_51)),
% 1.94/0.63    inference(backward_demodulation,[],[f670,f675])).
% 1.94/0.63  fof(f695,plain,(
% 1.94/0.63    ~spl6_53 | spl6_49 | ~spl6_51),
% 1.94/0.63    inference(avatar_split_clause,[],[f684,f668,f657,f692])).
% 1.94/0.63  fof(f684,plain,(
% 1.94/0.63    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl6_49 | ~spl6_51)),
% 1.94/0.63    inference(backward_demodulation,[],[f659,f675])).
% 1.94/0.63  fof(f671,plain,(
% 1.94/0.63    spl6_51 | ~spl6_18 | ~spl6_42),
% 1.94/0.63    inference(avatar_split_clause,[],[f640,f534,f223,f668])).
% 1.94/0.63  fof(f640,plain,(
% 1.94/0.63    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | (~spl6_18 | ~spl6_42)),
% 1.94/0.63    inference(backward_demodulation,[],[f536,f632])).
% 1.94/0.63  fof(f660,plain,(
% 1.94/0.63    ~spl6_49 | ~spl6_18 | spl6_40 | ~spl6_42),
% 1.94/0.63    inference(avatar_split_clause,[],[f639,f534,f495,f223,f657])).
% 1.94/0.63  fof(f495,plain,(
% 1.94/0.63    spl6_40 <=> v1_funct_2(k7_relat_1(sK4,sK1),sK1,k1_xboole_0)),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 1.94/0.63  fof(f639,plain,(
% 1.94/0.63    ~v1_funct_2(k1_xboole_0,sK1,k1_xboole_0) | (~spl6_18 | spl6_40 | ~spl6_42)),
% 1.94/0.63    inference(backward_demodulation,[],[f497,f632])).
% 1.94/0.63  fof(f497,plain,(
% 1.94/0.63    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,k1_xboole_0) | spl6_40),
% 1.94/0.63    inference(avatar_component_clause,[],[f495])).
% 1.94/0.63  fof(f563,plain,(
% 1.94/0.63    spl6_46 | ~spl6_19 | ~spl6_36 | ~spl6_37),
% 1.94/0.63    inference(avatar_split_clause,[],[f518,f443,f439,f253,f560])).
% 1.94/0.63  fof(f253,plain,(
% 1.94/0.63    spl6_19 <=> sK2 = k7_relset_1(sK0,sK3,sK4,sK1)),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 1.94/0.63  fof(f439,plain,(
% 1.94/0.63    spl6_36 <=> sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 1.94/0.63  fof(f443,plain,(
% 1.94/0.63    spl6_37 <=> k1_xboole_0 = sK2),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 1.94/0.63  fof(f518,plain,(
% 1.94/0.63    sK1 = k1_relset_1(sK1,k1_xboole_0,k7_relat_1(sK4,sK1)) | (~spl6_19 | ~spl6_36 | ~spl6_37)),
% 1.94/0.63    inference(backward_demodulation,[],[f440,f512])).
% 1.94/0.63  fof(f512,plain,(
% 1.94/0.63    k1_xboole_0 = sK2 | (~spl6_19 | ~spl6_37)),
% 1.94/0.63    inference(backward_demodulation,[],[f255,f492])).
% 1.94/0.63  fof(f492,plain,(
% 1.94/0.63    k1_xboole_0 = k7_relset_1(sK0,sK3,sK4,sK1) | (~spl6_19 | ~spl6_37)),
% 1.94/0.63    inference(forward_demodulation,[],[f255,f445])).
% 1.94/0.63  fof(f445,plain,(
% 1.94/0.63    k1_xboole_0 = sK2 | ~spl6_37),
% 1.94/0.63    inference(avatar_component_clause,[],[f443])).
% 1.94/0.63  fof(f255,plain,(
% 1.94/0.63    sK2 = k7_relset_1(sK0,sK3,sK4,sK1) | ~spl6_19),
% 1.94/0.63    inference(avatar_component_clause,[],[f253])).
% 1.94/0.63  fof(f440,plain,(
% 1.94/0.63    sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | ~spl6_36),
% 1.94/0.63    inference(avatar_component_clause,[],[f439])).
% 1.94/0.63  fof(f537,plain,(
% 1.94/0.63    spl6_42 | ~spl6_19 | ~spl6_22 | ~spl6_37),
% 1.94/0.63    inference(avatar_split_clause,[],[f513,f443,f291,f253,f534])).
% 1.94/0.63  fof(f291,plain,(
% 1.94/0.63    spl6_22 <=> m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 1.94/0.63  fof(f513,plain,(
% 1.94/0.63    m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | (~spl6_19 | ~spl6_22 | ~spl6_37)),
% 1.94/0.63    inference(backward_demodulation,[],[f292,f512])).
% 1.94/0.63  fof(f292,plain,(
% 1.94/0.63    m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_22),
% 1.94/0.63    inference(avatar_component_clause,[],[f291])).
% 1.94/0.63  fof(f509,plain,(
% 1.94/0.63    ~spl6_1 | ~spl6_5 | spl6_11),
% 1.94/0.63    inference(avatar_contradiction_clause,[],[f508])).
% 1.94/0.63  fof(f508,plain,(
% 1.94/0.63    $false | (~spl6_1 | ~spl6_5 | spl6_11)),
% 1.94/0.63    inference(subsumption_resolution,[],[f507,f277])).
% 1.94/0.63  fof(f277,plain,(
% 1.94/0.63    ( ! [X0] : (v1_funct_1(k7_relat_1(sK4,X0))) ) | (~spl6_1 | ~spl6_5)),
% 1.94/0.63    inference(backward_demodulation,[],[f248,f271])).
% 1.94/0.63  fof(f271,plain,(
% 1.94/0.63    ( ! [X0] : (k7_relat_1(sK4,X0) = k2_partfun1(sK0,sK3,sK4,X0)) ) | (~spl6_1 | ~spl6_5)),
% 1.94/0.63    inference(resolution,[],[f107,f125])).
% 1.94/0.63  fof(f125,plain,(
% 1.94/0.63    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~spl6_5),
% 1.94/0.63    inference(avatar_component_clause,[],[f123])).
% 1.94/0.63  fof(f123,plain,(
% 1.94/0.63    spl6_5 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.94/0.63  fof(f107,plain,(
% 1.94/0.63    ( ! [X6,X8,X7] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | k2_partfun1(X6,X7,sK4,X8) = k7_relat_1(sK4,X8)) ) | ~spl6_1),
% 1.94/0.63    inference(resolution,[],[f98,f85])).
% 1.94/0.63  fof(f85,plain,(
% 1.94/0.63    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 1.94/0.63    inference(cnf_transformation,[],[f45])).
% 1.94/0.63  fof(f45,plain,(
% 1.94/0.63    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.94/0.63    inference(flattening,[],[f44])).
% 1.94/0.63  fof(f44,plain,(
% 1.94/0.63    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.94/0.63    inference(ennf_transformation,[],[f21])).
% 1.94/0.63  fof(f21,axiom,(
% 1.94/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.94/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.94/0.63  fof(f98,plain,(
% 1.94/0.63    v1_funct_1(sK4) | ~spl6_1),
% 1.94/0.63    inference(avatar_component_clause,[],[f96])).
% 1.94/0.63  fof(f96,plain,(
% 1.94/0.63    spl6_1 <=> v1_funct_1(sK4)),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.94/0.63  fof(f248,plain,(
% 1.94/0.63    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0))) ) | (~spl6_1 | ~spl6_5)),
% 1.94/0.63    inference(resolution,[],[f105,f125])).
% 1.94/0.63  fof(f105,plain,(
% 1.94/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,sK4,X2))) ) | ~spl6_1),
% 1.94/0.63    inference(resolution,[],[f98,f86])).
% 1.94/0.63  fof(f86,plain,(
% 1.94/0.63    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,X2,X3))) )),
% 1.94/0.63    inference(cnf_transformation,[],[f47])).
% 1.94/0.63  fof(f47,plain,(
% 1.94/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.94/0.63    inference(flattening,[],[f46])).
% 1.94/0.63  fof(f46,plain,(
% 1.94/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.94/0.63    inference(ennf_transformation,[],[f20])).
% 1.94/0.63  fof(f20,axiom,(
% 1.94/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.94/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.94/0.63  fof(f507,plain,(
% 1.94/0.63    ~v1_funct_1(k7_relat_1(sK4,sK1)) | (~spl6_1 | ~spl6_5 | spl6_11)),
% 1.94/0.63    inference(forward_demodulation,[],[f158,f271])).
% 1.94/0.63  fof(f158,plain,(
% 1.94/0.63    ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) | spl6_11),
% 1.94/0.63    inference(avatar_component_clause,[],[f156])).
% 1.94/0.63  fof(f156,plain,(
% 1.94/0.63    spl6_11 <=> v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.94/0.63  fof(f498,plain,(
% 1.94/0.63    ~spl6_40 | spl6_35 | ~spl6_37),
% 1.94/0.63    inference(avatar_split_clause,[],[f477,f443,f422,f495])).
% 1.94/0.63  fof(f422,plain,(
% 1.94/0.63    spl6_35 <=> v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 1.94/0.63  fof(f477,plain,(
% 1.94/0.63    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,k1_xboole_0) | (spl6_35 | ~spl6_37)),
% 1.94/0.63    inference(backward_demodulation,[],[f424,f445])).
% 1.94/0.63  fof(f424,plain,(
% 1.94/0.63    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | spl6_35),
% 1.94/0.63    inference(avatar_component_clause,[],[f422])).
% 1.94/0.63  fof(f481,plain,(
% 1.94/0.63    spl6_20 | ~spl6_37),
% 1.94/0.63    inference(avatar_contradiction_clause,[],[f480])).
% 1.94/0.63  fof(f480,plain,(
% 1.94/0.63    $false | (spl6_20 | ~spl6_37)),
% 1.94/0.63    inference(subsumption_resolution,[],[f472,f56])).
% 1.94/0.63  fof(f472,plain,(
% 1.94/0.63    ~r1_tarski(k1_xboole_0,k7_relset_1(sK0,sK3,sK4,sK1)) | (spl6_20 | ~spl6_37)),
% 1.94/0.63    inference(backward_demodulation,[],[f259,f445])).
% 1.94/0.63  fof(f259,plain,(
% 1.94/0.63    ~r1_tarski(sK2,k7_relset_1(sK0,sK3,sK4,sK1)) | spl6_20),
% 1.94/0.63    inference(avatar_component_clause,[],[f257])).
% 1.94/0.63  fof(f257,plain,(
% 1.94/0.63    spl6_20 <=> r1_tarski(sK2,k7_relset_1(sK0,sK3,sK4,sK1))),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 1.94/0.63  fof(f466,plain,(
% 1.94/0.63    sK1 != k1_relat_1(k7_relat_1(sK4,sK1)) | r1_tarski(sK1,k1_relat_1(k7_relat_1(sK4,sK1))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)),
% 1.94/0.63    introduced(theory_tautology_sat_conflict,[])).
% 1.94/0.63  fof(f465,plain,(
% 1.94/0.63    ~spl6_3 | ~spl6_17 | ~spl6_33 | spl6_38),
% 1.94/0.63    inference(avatar_contradiction_clause,[],[f464])).
% 1.94/0.63  fof(f464,plain,(
% 1.94/0.63    $false | (~spl6_3 | ~spl6_17 | ~spl6_33 | spl6_38)),
% 1.94/0.63    inference(subsumption_resolution,[],[f463,f112])).
% 1.94/0.63  fof(f112,plain,(
% 1.94/0.63    r1_tarski(sK1,sK0) | ~spl6_3),
% 1.94/0.63    inference(avatar_component_clause,[],[f110])).
% 1.94/0.63  fof(f110,plain,(
% 1.94/0.63    spl6_3 <=> r1_tarski(sK1,sK0)),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.94/0.63  fof(f463,plain,(
% 1.94/0.63    ~r1_tarski(sK1,sK0) | (~spl6_17 | ~spl6_33 | spl6_38)),
% 1.94/0.63    inference(forward_demodulation,[],[f462,f194])).
% 1.94/0.63  fof(f194,plain,(
% 1.94/0.63    sK0 = k1_relat_1(sK4) | ~spl6_17),
% 1.94/0.63    inference(avatar_component_clause,[],[f192])).
% 1.94/0.63  fof(f192,plain,(
% 1.94/0.63    spl6_17 <=> sK0 = k1_relat_1(sK4)),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.94/0.63  fof(f462,plain,(
% 1.94/0.63    ~r1_tarski(sK1,k1_relat_1(sK4)) | (~spl6_33 | spl6_38)),
% 1.94/0.63    inference(subsumption_resolution,[],[f461,f360])).
% 1.94/0.63  fof(f360,plain,(
% 1.94/0.63    v1_relat_1(sK4) | ~spl6_33),
% 1.94/0.63    inference(avatar_component_clause,[],[f359])).
% 1.94/0.63  fof(f359,plain,(
% 1.94/0.63    spl6_33 <=> v1_relat_1(sK4)),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 1.94/0.63  fof(f461,plain,(
% 1.94/0.63    ~r1_tarski(sK1,k1_relat_1(sK4)) | ~v1_relat_1(sK4) | spl6_38),
% 1.94/0.63    inference(trivial_inequality_removal,[],[f460])).
% 1.94/0.63  fof(f460,plain,(
% 1.94/0.63    sK1 != sK1 | ~r1_tarski(sK1,k1_relat_1(sK4)) | ~v1_relat_1(sK4) | spl6_38),
% 1.94/0.63    inference(superposition,[],[f453,f62])).
% 1.94/0.63  fof(f62,plain,(
% 1.94/0.63    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.94/0.63    inference(cnf_transformation,[],[f31])).
% 1.94/0.63  fof(f31,plain,(
% 1.94/0.63    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.94/0.63    inference(flattening,[],[f30])).
% 1.94/0.63  fof(f30,plain,(
% 1.94/0.63    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.94/0.63    inference(ennf_transformation,[],[f12])).
% 1.94/0.63  fof(f12,axiom,(
% 1.94/0.63    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.94/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.94/0.63  fof(f453,plain,(
% 1.94/0.63    sK1 != k1_relat_1(k7_relat_1(sK4,sK1)) | spl6_38),
% 1.94/0.63    inference(avatar_component_clause,[],[f451])).
% 1.94/0.63  fof(f451,plain,(
% 1.94/0.63    spl6_38 <=> sK1 = k1_relat_1(k7_relat_1(sK4,sK1))),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 1.94/0.63  fof(f459,plain,(
% 1.94/0.63    ~spl6_39 | ~spl6_22 | ~spl6_25 | spl6_36),
% 1.94/0.63    inference(avatar_split_clause,[],[f449,f439,f310,f291,f456])).
% 1.94/0.63  fof(f456,plain,(
% 1.94/0.63    spl6_39 <=> r1_tarski(sK1,k1_relat_1(k7_relat_1(sK4,sK1)))),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 1.94/0.63  fof(f310,plain,(
% 1.94/0.63    spl6_25 <=> r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 1.94/0.63  fof(f449,plain,(
% 1.94/0.63    ~r1_tarski(sK1,k1_relat_1(k7_relat_1(sK4,sK1))) | (~spl6_22 | ~spl6_25 | spl6_36)),
% 1.94/0.63    inference(subsumption_resolution,[],[f407,f448])).
% 1.94/0.63  fof(f448,plain,(
% 1.94/0.63    sK1 != k1_relat_1(k7_relat_1(sK4,sK1)) | (~spl6_22 | spl6_36)),
% 1.94/0.63    inference(subsumption_resolution,[],[f447,f292])).
% 1.94/0.63  fof(f447,plain,(
% 1.94/0.63    sK1 != k1_relat_1(k7_relat_1(sK4,sK1)) | ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl6_36),
% 1.94/0.63    inference(superposition,[],[f441,f74])).
% 1.94/0.63  fof(f74,plain,(
% 1.94/0.63    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.94/0.63    inference(cnf_transformation,[],[f38])).
% 1.94/0.63  fof(f38,plain,(
% 1.94/0.63    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.94/0.63    inference(ennf_transformation,[],[f16])).
% 1.94/0.63  fof(f16,axiom,(
% 1.94/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.94/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.94/0.63  fof(f441,plain,(
% 1.94/0.63    sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | spl6_36),
% 1.94/0.63    inference(avatar_component_clause,[],[f439])).
% 1.94/0.63  fof(f407,plain,(
% 1.94/0.63    ~r1_tarski(sK1,k1_relat_1(k7_relat_1(sK4,sK1))) | sK1 = k1_relat_1(k7_relat_1(sK4,sK1)) | ~spl6_25),
% 1.94/0.63    inference(resolution,[],[f311,f66])).
% 1.94/0.63  fof(f311,plain,(
% 1.94/0.63    r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | ~spl6_25),
% 1.94/0.63    inference(avatar_component_clause,[],[f310])).
% 1.94/0.63  fof(f446,plain,(
% 1.94/0.63    ~spl6_36 | spl6_37 | ~spl6_1 | ~spl6_5 | ~spl6_9 | spl6_35),
% 1.94/0.63    inference(avatar_split_clause,[],[f427,f422,f148,f123,f96,f443,f439])).
% 1.94/0.63  fof(f148,plain,(
% 1.94/0.63    spl6_9 <=> m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.94/0.63  fof(f427,plain,(
% 1.94/0.63    k1_xboole_0 = sK2 | sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | (~spl6_1 | ~spl6_5 | ~spl6_9 | spl6_35)),
% 1.94/0.63    inference(subsumption_resolution,[],[f426,f418])).
% 1.94/0.63  fof(f418,plain,(
% 1.94/0.63    m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl6_1 | ~spl6_5 | ~spl6_9)),
% 1.94/0.63    inference(forward_demodulation,[],[f149,f271])).
% 1.94/0.63  fof(f149,plain,(
% 1.94/0.63    m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_9),
% 1.94/0.63    inference(avatar_component_clause,[],[f148])).
% 1.94/0.63  fof(f426,plain,(
% 1.94/0.63    k1_xboole_0 = sK2 | sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl6_35),
% 1.94/0.63    inference(resolution,[],[f424,f81])).
% 1.94/0.63  fof(f81,plain,(
% 1.94/0.63    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.94/0.63    inference(cnf_transformation,[],[f41])).
% 1.94/0.63  fof(f425,plain,(
% 1.94/0.63    ~spl6_35 | ~spl6_1 | ~spl6_5 | spl6_10),
% 1.94/0.63    inference(avatar_split_clause,[],[f417,f152,f123,f96,f422])).
% 1.94/0.63  fof(f152,plain,(
% 1.94/0.63    spl6_10 <=> v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.94/0.63  fof(f417,plain,(
% 1.94/0.63    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | (~spl6_1 | ~spl6_5 | spl6_10)),
% 1.94/0.63    inference(forward_demodulation,[],[f154,f271])).
% 1.94/0.63  fof(f154,plain,(
% 1.94/0.63    ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | spl6_10),
% 1.94/0.63    inference(avatar_component_clause,[],[f152])).
% 1.94/0.63  fof(f416,plain,(
% 1.94/0.63    spl6_22 | ~spl6_24 | ~spl6_25 | ~spl6_26),
% 1.94/0.63    inference(avatar_contradiction_clause,[],[f415])).
% 1.94/0.63  fof(f415,plain,(
% 1.94/0.63    $false | (spl6_22 | ~spl6_24 | ~spl6_25 | ~spl6_26)),
% 1.94/0.63    inference(subsumption_resolution,[],[f315,f414])).
% 1.94/0.63  fof(f414,plain,(
% 1.94/0.63    ~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) | (spl6_22 | ~spl6_24 | ~spl6_25)),
% 1.94/0.63    inference(subsumption_resolution,[],[f413,f307])).
% 1.94/0.63  fof(f307,plain,(
% 1.94/0.63    v1_relat_1(k7_relat_1(sK4,sK1)) | ~spl6_24),
% 1.94/0.63    inference(avatar_component_clause,[],[f306])).
% 1.94/0.63  fof(f306,plain,(
% 1.94/0.63    spl6_24 <=> v1_relat_1(k7_relat_1(sK4,sK1))),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 1.94/0.63  fof(f413,plain,(
% 1.94/0.63    ~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) | ~v1_relat_1(k7_relat_1(sK4,sK1)) | (spl6_22 | ~spl6_25)),
% 1.94/0.63    inference(subsumption_resolution,[],[f295,f311])).
% 1.94/0.63  fof(f295,plain,(
% 1.94/0.63    ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | ~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) | ~v1_relat_1(k7_relat_1(sK4,sK1)) | spl6_22),
% 1.94/0.63    inference(resolution,[],[f293,f72])).
% 1.94/0.63  fof(f72,plain,(
% 1.94/0.63    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | ~v1_relat_1(X2)) )),
% 1.94/0.63    inference(cnf_transformation,[],[f36])).
% 1.94/0.63  fof(f36,plain,(
% 1.94/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.94/0.63    inference(flattening,[],[f35])).
% 1.94/0.63  fof(f35,plain,(
% 1.94/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.94/0.63    inference(ennf_transformation,[],[f18])).
% 1.94/0.63  fof(f18,axiom,(
% 1.94/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.94/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 1.94/0.63  fof(f293,plain,(
% 1.94/0.63    ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl6_22),
% 1.94/0.63    inference(avatar_component_clause,[],[f291])).
% 1.94/0.63  fof(f315,plain,(
% 1.94/0.63    r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) | ~spl6_26),
% 1.94/0.63    inference(avatar_component_clause,[],[f314])).
% 1.94/0.63  fof(f314,plain,(
% 1.94/0.63    spl6_26 <=> r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 1.94/0.63  fof(f412,plain,(
% 1.94/0.63    ~spl6_8 | spl6_26 | ~spl6_33),
% 1.94/0.63    inference(avatar_contradiction_clause,[],[f411])).
% 1.94/0.63  fof(f411,plain,(
% 1.94/0.63    $false | (~spl6_8 | spl6_26 | ~spl6_33)),
% 1.94/0.63    inference(subsumption_resolution,[],[f410,f360])).
% 1.94/0.63  fof(f410,plain,(
% 1.94/0.63    ~v1_relat_1(sK4) | (~spl6_8 | spl6_26)),
% 1.94/0.63    inference(subsumption_resolution,[],[f409,f145])).
% 1.94/0.63  fof(f145,plain,(
% 1.94/0.63    r1_tarski(k9_relat_1(sK4,sK1),sK2) | ~spl6_8),
% 1.94/0.63    inference(avatar_component_clause,[],[f143])).
% 1.94/0.63  fof(f143,plain,(
% 1.94/0.63    spl6_8 <=> r1_tarski(k9_relat_1(sK4,sK1),sK2)),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.94/0.63  fof(f409,plain,(
% 1.94/0.63    ~r1_tarski(k9_relat_1(sK4,sK1),sK2) | ~v1_relat_1(sK4) | spl6_26),
% 1.94/0.63    inference(superposition,[],[f316,f61])).
% 1.94/0.63  fof(f61,plain,(
% 1.94/0.63    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.94/0.63    inference(cnf_transformation,[],[f29])).
% 1.94/0.63  fof(f29,plain,(
% 1.94/0.63    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.94/0.63    inference(ennf_transformation,[],[f9])).
% 1.94/0.63  fof(f9,axiom,(
% 1.94/0.63    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.94/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.94/0.63  fof(f316,plain,(
% 1.94/0.63    ~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) | spl6_26),
% 1.94/0.63    inference(avatar_component_clause,[],[f314])).
% 1.94/0.63  fof(f401,plain,(
% 1.94/0.63    spl6_25 | ~spl6_33),
% 1.94/0.63    inference(avatar_contradiction_clause,[],[f400])).
% 1.94/0.63  fof(f400,plain,(
% 1.94/0.63    $false | (spl6_25 | ~spl6_33)),
% 1.94/0.63    inference(subsumption_resolution,[],[f398,f360])).
% 1.94/0.63  fof(f398,plain,(
% 1.94/0.63    ~v1_relat_1(sK4) | spl6_25),
% 1.94/0.63    inference(resolution,[],[f312,f60])).
% 1.94/0.63  fof(f60,plain,(
% 1.94/0.63    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.94/0.63    inference(cnf_transformation,[],[f28])).
% 1.94/0.63  fof(f28,plain,(
% 1.94/0.63    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.94/0.63    inference(ennf_transformation,[],[f11])).
% 1.94/0.63  fof(f11,axiom,(
% 1.94/0.63    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.94/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 1.94/0.63  fof(f312,plain,(
% 1.94/0.63    ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | spl6_25),
% 1.94/0.63    inference(avatar_component_clause,[],[f310])).
% 1.94/0.63  fof(f397,plain,(
% 1.94/0.63    ~spl6_1 | ~spl6_5 | spl6_24),
% 1.94/0.63    inference(avatar_contradiction_clause,[],[f396])).
% 1.94/0.63  fof(f396,plain,(
% 1.94/0.63    $false | (~spl6_1 | ~spl6_5 | spl6_24)),
% 1.94/0.63    inference(subsumption_resolution,[],[f393,f58])).
% 1.94/0.63  fof(f58,plain,(
% 1.94/0.63    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.94/0.63    inference(cnf_transformation,[],[f8])).
% 1.94/0.63  fof(f8,axiom,(
% 1.94/0.63    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.94/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.94/0.63  fof(f393,plain,(
% 1.94/0.63    ~v1_relat_1(k2_zfmisc_1(sK0,sK3)) | (~spl6_1 | ~spl6_5 | spl6_24)),
% 1.94/0.63    inference(resolution,[],[f381,f324])).
% 1.94/0.63  fof(f324,plain,(
% 1.94/0.63    ( ! [X0] : (~r1_tarski(k7_relat_1(sK4,sK1),X0) | ~v1_relat_1(X0)) ) | spl6_24),
% 1.94/0.63    inference(resolution,[],[f319,f70])).
% 1.94/0.63  fof(f319,plain,(
% 1.94/0.63    ( ! [X2] : (~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(X2)) | ~v1_relat_1(X2)) ) | spl6_24),
% 1.94/0.63    inference(resolution,[],[f308,f57])).
% 1.94/0.63  fof(f57,plain,(
% 1.94/0.63    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.94/0.63    inference(cnf_transformation,[],[f26])).
% 1.94/0.63  fof(f26,plain,(
% 1.94/0.63    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.94/0.63    inference(ennf_transformation,[],[f7])).
% 1.94/0.63  fof(f7,axiom,(
% 1.94/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.94/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.94/0.63  fof(f308,plain,(
% 1.94/0.63    ~v1_relat_1(k7_relat_1(sK4,sK1)) | spl6_24),
% 1.94/0.63    inference(avatar_component_clause,[],[f306])).
% 1.94/0.63  fof(f381,plain,(
% 1.94/0.63    ( ! [X0] : (r1_tarski(k7_relat_1(sK4,X0),k2_zfmisc_1(sK0,sK3))) ) | (~spl6_1 | ~spl6_5)),
% 1.94/0.63    inference(subsumption_resolution,[],[f380,f125])).
% 1.94/0.63  fof(f380,plain,(
% 1.94/0.63    ( ! [X0] : (r1_tarski(k7_relat_1(sK4,X0),k2_zfmisc_1(sK0,sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))) ) | (~spl6_1 | ~spl6_5)),
% 1.94/0.63    inference(superposition,[],[f302,f271])).
% 1.94/0.63  fof(f302,plain,(
% 1.94/0.63    ( ! [X2,X0,X1] : (r1_tarski(k2_partfun1(X0,X1,sK4,X2),k2_zfmisc_1(X0,X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl6_1),
% 1.94/0.63    inference(resolution,[],[f106,f71])).
% 1.94/0.63  fof(f71,plain,(
% 1.94/0.63    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.94/0.63    inference(cnf_transformation,[],[f5])).
% 1.94/0.63  fof(f106,plain,(
% 1.94/0.63    ( ! [X4,X5,X3] : (m1_subset_1(k2_partfun1(X3,X4,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ) | ~spl6_1),
% 1.94/0.63    inference(resolution,[],[f98,f87])).
% 1.94/0.63  fof(f87,plain,(
% 1.94/0.63    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.94/0.63    inference(cnf_transformation,[],[f47])).
% 1.94/0.63  fof(f369,plain,(
% 1.94/0.63    ~spl6_5 | spl6_33),
% 1.94/0.63    inference(avatar_contradiction_clause,[],[f368])).
% 1.94/0.63  fof(f368,plain,(
% 1.94/0.63    $false | (~spl6_5 | spl6_33)),
% 1.94/0.63    inference(subsumption_resolution,[],[f125,f366])).
% 1.94/0.63  fof(f366,plain,(
% 1.94/0.63    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_33),
% 1.94/0.63    inference(resolution,[],[f361,f73])).
% 1.94/0.63  fof(f73,plain,(
% 1.94/0.63    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.94/0.63    inference(cnf_transformation,[],[f37])).
% 1.94/0.63  fof(f37,plain,(
% 1.94/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.94/0.63    inference(ennf_transformation,[],[f13])).
% 1.94/0.63  fof(f13,axiom,(
% 1.94/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.94/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.94/0.63  fof(f361,plain,(
% 1.94/0.63    ~v1_relat_1(sK4) | spl6_33),
% 1.94/0.63    inference(avatar_component_clause,[],[f359])).
% 1.94/0.63  fof(f317,plain,(
% 1.94/0.63    ~spl6_24 | ~spl6_25 | ~spl6_26 | ~spl6_1 | ~spl6_5 | spl6_9),
% 1.94/0.63    inference(avatar_split_clause,[],[f282,f148,f123,f96,f314,f310,f306])).
% 1.94/0.63  fof(f282,plain,(
% 1.94/0.63    ~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | ~v1_relat_1(k7_relat_1(sK4,sK1)) | (~spl6_1 | ~spl6_5 | spl6_9)),
% 1.94/0.63    inference(forward_demodulation,[],[f281,f271])).
% 1.94/0.63  fof(f281,plain,(
% 1.94/0.63    ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | ~v1_relat_1(k7_relat_1(sK4,sK1)) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2) | (~spl6_1 | ~spl6_5 | spl6_9)),
% 1.94/0.63    inference(forward_demodulation,[],[f275,f271])).
% 1.94/0.63  fof(f275,plain,(
% 1.94/0.63    ~v1_relat_1(k7_relat_1(sK4,sK1)) | ~r1_tarski(k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK1) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2) | (~spl6_1 | ~spl6_5 | spl6_9)),
% 1.94/0.63    inference(backward_demodulation,[],[f161,f271])).
% 1.94/0.63  fof(f161,plain,(
% 1.94/0.63    ~r1_tarski(k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK1) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2) | ~v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) | spl6_9),
% 1.94/0.63    inference(resolution,[],[f150,f72])).
% 1.94/0.63  fof(f150,plain,(
% 1.94/0.63    ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl6_9),
% 1.94/0.63    inference(avatar_component_clause,[],[f148])).
% 1.94/0.63  fof(f260,plain,(
% 1.94/0.63    spl6_19 | ~spl6_20 | ~spl6_7),
% 1.94/0.63    inference(avatar_split_clause,[],[f139,f134,f257,f253])).
% 1.94/0.63  fof(f134,plain,(
% 1.94/0.63    spl6_7 <=> r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.94/0.63  fof(f139,plain,(
% 1.94/0.63    ~r1_tarski(sK2,k7_relset_1(sK0,sK3,sK4,sK1)) | sK2 = k7_relset_1(sK0,sK3,sK4,sK1) | ~spl6_7),
% 1.94/0.63    inference(resolution,[],[f136,f66])).
% 1.94/0.63  fof(f136,plain,(
% 1.94/0.63    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) | ~spl6_7),
% 1.94/0.63    inference(avatar_component_clause,[],[f134])).
% 1.94/0.63  fof(f226,plain,(
% 1.94/0.63    spl6_18),
% 1.94/0.63    inference(avatar_split_clause,[],[f55,f223])).
% 1.94/0.63  fof(f55,plain,(
% 1.94/0.63    v1_xboole_0(k1_xboole_0)),
% 1.94/0.63    inference(cnf_transformation,[],[f2])).
% 1.94/0.63  fof(f2,axiom,(
% 1.94/0.63    v1_xboole_0(k1_xboole_0)),
% 1.94/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.94/0.63  fof(f220,plain,(
% 1.94/0.63    spl6_2 | ~spl6_15),
% 1.94/0.63    inference(avatar_contradiction_clause,[],[f218])).
% 1.94/0.63  fof(f218,plain,(
% 1.94/0.63    $false | (spl6_2 | ~spl6_15)),
% 1.94/0.63    inference(subsumption_resolution,[],[f55,f217])).
% 1.94/0.63  fof(f217,plain,(
% 1.94/0.63    ( ! [X2] : (~v1_xboole_0(X2)) ) | (spl6_2 | ~spl6_15)),
% 1.94/0.63    inference(subsumption_resolution,[],[f207,f56])).
% 1.94/0.63  fof(f207,plain,(
% 1.94/0.63    ( ! [X2,X3] : (~r1_tarski(k1_xboole_0,k2_zfmisc_1(X3,X2)) | ~v1_xboole_0(X2)) ) | (spl6_2 | ~spl6_15)),
% 1.94/0.63    inference(backward_demodulation,[],[f173,f181])).
% 1.94/0.63  fof(f181,plain,(
% 1.94/0.63    k1_xboole_0 = sK3 | ~spl6_15),
% 1.94/0.63    inference(avatar_component_clause,[],[f179])).
% 1.94/0.63  fof(f179,plain,(
% 1.94/0.63    spl6_15 <=> k1_xboole_0 = sK3),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.94/0.63  fof(f173,plain,(
% 1.94/0.63    ( ! [X2,X3] : (~r1_tarski(sK3,k2_zfmisc_1(X3,X2)) | ~v1_xboole_0(X2)) ) | spl6_2),
% 1.94/0.63    inference(resolution,[],[f108,f70])).
% 1.94/0.63  fof(f108,plain,(
% 1.94/0.63    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X1)) ) | spl6_2),
% 1.94/0.63    inference(resolution,[],[f103,f59])).
% 1.94/0.63  fof(f103,plain,(
% 1.94/0.63    ~v1_xboole_0(sK3) | spl6_2),
% 1.94/0.63    inference(avatar_component_clause,[],[f101])).
% 1.94/0.63  fof(f101,plain,(
% 1.94/0.63    spl6_2 <=> v1_xboole_0(sK3)),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.94/0.63  fof(f195,plain,(
% 1.94/0.63    spl6_17 | ~spl6_5 | ~spl6_14),
% 1.94/0.63    inference(avatar_split_clause,[],[f185,f175,f123,f192])).
% 1.94/0.63  fof(f175,plain,(
% 1.94/0.63    spl6_14 <=> sK0 = k1_relset_1(sK0,sK3,sK4)),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.94/0.63  fof(f185,plain,(
% 1.94/0.63    sK0 = k1_relat_1(sK4) | (~spl6_5 | ~spl6_14)),
% 1.94/0.63    inference(subsumption_resolution,[],[f183,f125])).
% 1.94/0.63  fof(f183,plain,(
% 1.94/0.63    sK0 = k1_relat_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~spl6_14),
% 1.94/0.63    inference(superposition,[],[f177,f74])).
% 1.94/0.63  fof(f177,plain,(
% 1.94/0.63    sK0 = k1_relset_1(sK0,sK3,sK4) | ~spl6_14),
% 1.94/0.63    inference(avatar_component_clause,[],[f175])).
% 1.94/0.63  fof(f182,plain,(
% 1.94/0.63    spl6_14 | spl6_15 | ~spl6_4),
% 1.94/0.63    inference(avatar_split_clause,[],[f121,f116,f179,f175])).
% 1.94/0.63  fof(f116,plain,(
% 1.94/0.63    spl6_4 <=> v1_funct_2(sK4,sK0,sK3)),
% 1.94/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.94/0.63  fof(f121,plain,(
% 1.94/0.63    k1_xboole_0 = sK3 | sK0 = k1_relset_1(sK0,sK3,sK4) | ~spl6_4),
% 1.94/0.63    inference(subsumption_resolution,[],[f120,f51])).
% 1.94/0.63  fof(f51,plain,(
% 1.94/0.63    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 1.94/0.63    inference(cnf_transformation,[],[f25])).
% 1.94/0.63  fof(f25,plain,(
% 1.94/0.63    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3))),
% 1.94/0.63    inference(flattening,[],[f24])).
% 1.94/0.63  fof(f24,plain,(
% 1.94/0.63    ? [X0,X1,X2,X3] : (? [X4] : (((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & (r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4))) & ~v1_xboole_0(X3))),
% 1.94/0.63    inference(ennf_transformation,[],[f23])).
% 1.94/0.63  fof(f23,negated_conjecture,(
% 1.94/0.63    ~! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 1.94/0.63    inference(negated_conjecture,[],[f22])).
% 1.94/0.63  fof(f22,conjecture,(
% 1.94/0.63    ! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 1.94/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_funct_2)).
% 1.94/0.63  fof(f120,plain,(
% 1.94/0.63    k1_xboole_0 = sK3 | sK0 = k1_relset_1(sK0,sK3,sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~spl6_4),
% 1.94/0.63    inference(resolution,[],[f118,f82])).
% 1.94/0.63  fof(f82,plain,(
% 1.94/0.63    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.94/0.63    inference(cnf_transformation,[],[f41])).
% 1.94/0.63  fof(f118,plain,(
% 1.94/0.63    v1_funct_2(sK4,sK0,sK3) | ~spl6_4),
% 1.94/0.63    inference(avatar_component_clause,[],[f116])).
% 1.94/0.63  fof(f159,plain,(
% 1.94/0.63    ~spl6_9 | ~spl6_10 | ~spl6_11),
% 1.94/0.63    inference(avatar_split_clause,[],[f48,f156,f152,f148])).
% 1.94/0.63  fof(f48,plain,(
% 1.94/0.63    ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.94/0.63    inference(cnf_transformation,[],[f25])).
% 1.94/0.63  fof(f146,plain,(
% 1.94/0.63    spl6_8 | ~spl6_5 | ~spl6_7),
% 1.94/0.63    inference(avatar_split_clause,[],[f141,f134,f123,f143])).
% 1.94/0.63  fof(f141,plain,(
% 1.94/0.63    r1_tarski(k9_relat_1(sK4,sK1),sK2) | (~spl6_5 | ~spl6_7)),
% 1.94/0.63    inference(subsumption_resolution,[],[f140,f125])).
% 1.94/0.63  fof(f140,plain,(
% 1.94/0.63    r1_tarski(k9_relat_1(sK4,sK1),sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~spl6_7),
% 1.94/0.63    inference(superposition,[],[f136,f84])).
% 1.94/0.63  fof(f84,plain,(
% 1.94/0.63    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.94/0.63    inference(cnf_transformation,[],[f43])).
% 1.94/0.63  fof(f43,plain,(
% 1.94/0.63    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.94/0.63    inference(ennf_transformation,[],[f17])).
% 1.94/0.63  fof(f17,axiom,(
% 1.94/0.63    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.94/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.94/0.63  fof(f137,plain,(
% 1.94/0.63    spl6_7),
% 1.94/0.63    inference(avatar_split_clause,[],[f53,f134])).
% 1.94/0.63  fof(f53,plain,(
% 1.94/0.63    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)),
% 1.94/0.63    inference(cnf_transformation,[],[f25])).
% 1.94/0.63  fof(f126,plain,(
% 1.94/0.63    spl6_5),
% 1.94/0.63    inference(avatar_split_clause,[],[f51,f123])).
% 1.94/0.63  fof(f119,plain,(
% 1.94/0.63    spl6_4),
% 1.94/0.63    inference(avatar_split_clause,[],[f50,f116])).
% 1.94/0.63  fof(f50,plain,(
% 1.94/0.63    v1_funct_2(sK4,sK0,sK3)),
% 1.94/0.63    inference(cnf_transformation,[],[f25])).
% 1.94/0.63  fof(f113,plain,(
% 1.94/0.63    spl6_3),
% 1.94/0.63    inference(avatar_split_clause,[],[f52,f110])).
% 1.94/0.63  fof(f52,plain,(
% 1.94/0.63    r1_tarski(sK1,sK0)),
% 1.94/0.63    inference(cnf_transformation,[],[f25])).
% 1.94/0.63  fof(f104,plain,(
% 1.94/0.63    ~spl6_2),
% 1.94/0.63    inference(avatar_split_clause,[],[f54,f101])).
% 1.94/0.63  fof(f54,plain,(
% 1.94/0.63    ~v1_xboole_0(sK3)),
% 1.94/0.63    inference(cnf_transformation,[],[f25])).
% 1.94/0.63  fof(f99,plain,(
% 1.94/0.63    spl6_1),
% 1.94/0.63    inference(avatar_split_clause,[],[f49,f96])).
% 1.94/0.63  fof(f49,plain,(
% 1.94/0.63    v1_funct_1(sK4)),
% 1.94/0.63    inference(cnf_transformation,[],[f25])).
% 1.94/0.63  % SZS output end Proof for theBenchmark
% 1.94/0.63  % (6165)------------------------------
% 1.94/0.63  % (6165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.94/0.63  % (6165)Termination reason: Refutation
% 1.94/0.63  
% 1.94/0.63  % (6165)Memory used [KB]: 11257
% 1.94/0.63  % (6165)Time elapsed: 0.198 s
% 1.94/0.63  % (6165)------------------------------
% 1.94/0.63  % (6165)------------------------------
% 1.94/0.63  % (6136)Success in time 0.255 s
%------------------------------------------------------------------------------
