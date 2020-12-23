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
% DateTime   : Thu Dec  3 12:57:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 213 expanded)
%              Number of leaves         :   30 ( 103 expanded)
%              Depth                    :    7
%              Number of atoms          :  350 ( 626 expanded)
%              Number of equality atoms :   30 (  61 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f291,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f66,f71,f75,f79,f83,f92,f103,f118,f120,f124,f140,f152,f173,f177,f187,f190,f211,f215,f239,f245,f261,f279,f290])).

fof(f290,plain,
    ( ~ spl9_4
    | ~ spl9_10
    | spl9_42 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | ~ spl9_4
    | ~ spl9_10
    | spl9_42 ),
    inference(unit_resulting_resolution,[],[f54,f278,f78])).

fof(f78,plain,
    ( ! [X2,X0,X1] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl9_10
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f278,plain,
    ( ~ v1_relat_1(sK2)
    | spl9_42 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl9_42
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f54,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl9_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f279,plain,
    ( ~ spl9_42
    | ~ spl9_13
    | ~ spl9_15
    | ~ spl9_31
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f272,f259,f209,f97,f90,f277])).

fof(f90,plain,
    ( spl9_13
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | r2_hidden(sK8(X0,X1,X2),X1)
        | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f97,plain,
    ( spl9_15
  <=> r2_hidden(sK3,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f209,plain,
    ( spl9_31
  <=> k1_relat_1(sK2) = k10_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f259,plain,
    ( spl9_40
  <=> ! [X0] :
        ( ~ r2_hidden(sK3,k10_relat_1(sK2,X0))
        | ~ r2_hidden(sK8(sK3,X0,sK2),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f272,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl9_13
    | ~ spl9_15
    | ~ spl9_31
    | ~ spl9_40 ),
    inference(subsumption_resolution,[],[f271,f119])).

fof(f119,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f97])).

fof(f271,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl9_13
    | ~ spl9_31
    | ~ spl9_40 ),
    inference(forward_demodulation,[],[f270,f210])).

fof(f210,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK1)
    | ~ spl9_31 ),
    inference(avatar_component_clause,[],[f209])).

fof(f270,plain,
    ( ~ r2_hidden(sK3,k10_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl9_13
    | ~ spl9_40 ),
    inference(duplicate_literal_removal,[],[f269])).

fof(f269,plain,
    ( ~ r2_hidden(sK3,k10_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK3,k10_relat_1(sK2,sK1))
    | ~ spl9_13
    | ~ spl9_40 ),
    inference(resolution,[],[f260,f91])).

fof(f91,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK8(X0,X1,X2),X1)
        | ~ v1_relat_1(X2)
        | ~ r2_hidden(X0,k10_relat_1(X2,X1)) )
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f90])).

fof(f260,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK8(sK3,X0,sK2),sK1)
        | ~ r2_hidden(sK3,k10_relat_1(sK2,X0)) )
    | ~ spl9_40 ),
    inference(avatar_component_clause,[],[f259])).

fof(f261,plain,
    ( spl9_40
    | ~ spl9_9
    | ~ spl9_37 ),
    inference(avatar_split_clause,[],[f253,f243,f73,f259])).

fof(f73,plain,
    ( spl9_9
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | m1_subset_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f243,plain,
    ( spl9_37
  <=> ! [X0] :
        ( ~ r2_hidden(sK3,k10_relat_1(sK2,X0))
        | ~ m1_subset_1(sK8(sK3,X0,sK2),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).

fof(f253,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,k10_relat_1(sK2,X0))
        | ~ r2_hidden(sK8(sK3,X0,sK2),sK1) )
    | ~ spl9_9
    | ~ spl9_37 ),
    inference(resolution,[],[f244,f74])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f73])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK8(sK3,X0,sK2),sK1)
        | ~ r2_hidden(sK3,k10_relat_1(sK2,X0)) )
    | ~ spl9_37 ),
    inference(avatar_component_clause,[],[f243])).

fof(f245,plain,
    ( spl9_37
    | ~ spl9_8
    | ~ spl9_36 ),
    inference(avatar_split_clause,[],[f240,f237,f69,f243])).

fof(f69,plain,
    ( spl9_8
  <=> ! [X4] :
        ( ~ m1_subset_1(X4,sK1)
        | ~ r2_hidden(k4_tarski(sK3,X4),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f237,plain,
    ( spl9_36
  <=> ! [X5,X6] :
        ( ~ r2_hidden(X5,k10_relat_1(sK2,X6))
        | r2_hidden(k4_tarski(X5,sK8(X5,X6,sK2)),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f240,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,k10_relat_1(sK2,X0))
        | ~ m1_subset_1(sK8(sK3,X0,sK2),sK1) )
    | ~ spl9_8
    | ~ spl9_36 ),
    inference(resolution,[],[f238,f70])).

fof(f70,plain,
    ( ! [X4] :
        ( ~ r2_hidden(k4_tarski(sK3,X4),sK2)
        | ~ m1_subset_1(X4,sK1) )
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f69])).

fof(f238,plain,
    ( ! [X6,X5] :
        ( r2_hidden(k4_tarski(X5,sK8(X5,X6,sK2)),sK2)
        | ~ r2_hidden(X5,k10_relat_1(sK2,X6)) )
    | ~ spl9_36 ),
    inference(avatar_component_clause,[],[f237])).

fof(f239,plain,
    ( spl9_36
    | ~ spl9_4
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f217,f213,f53,f237])).

fof(f213,plain,
    ( spl9_32
  <=> ! [X1,X3,X0,X2,X4] :
        ( r2_hidden(k4_tarski(X0,sK8(X0,X1,X2)),X2)
        | ~ r2_hidden(X0,k10_relat_1(X2,X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f217,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X5,k10_relat_1(sK2,X6))
        | r2_hidden(k4_tarski(X5,sK8(X5,X6,sK2)),sK2) )
    | ~ spl9_4
    | ~ spl9_32 ),
    inference(resolution,[],[f214,f54])).

fof(f214,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ r2_hidden(X0,k10_relat_1(X2,X1))
        | r2_hidden(k4_tarski(X0,sK8(X0,X1,X2)),X2) )
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f213])).

fof(f215,plain,
    ( spl9_32
    | ~ spl9_10
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f141,f116,f77,f213])).

fof(f116,plain,
    ( spl9_18
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | r2_hidden(k4_tarski(X0,sK8(X0,X1,X2)),X2)
        | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f141,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( r2_hidden(k4_tarski(X0,sK8(X0,X1,X2)),X2)
        | ~ r2_hidden(X0,k10_relat_1(X2,X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
    | ~ spl9_10
    | ~ spl9_18 ),
    inference(resolution,[],[f117,f78])).

fof(f117,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | r2_hidden(k4_tarski(X0,sK8(X0,X1,X2)),X2)
        | ~ r2_hidden(X0,k10_relat_1(X2,X1)) )
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f116])).

fof(f211,plain,
    ( spl9_31
    | ~ spl9_4
    | ~ spl9_16
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f181,f175,f101,f53,f209])).

fof(f101,plain,
    ( spl9_16
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f175,plain,
    ( spl9_28
  <=> k1_relset_1(sK0,sK1,sK2) = k10_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f181,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK1)
    | ~ spl9_4
    | ~ spl9_16
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f179,f54])).

fof(f179,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl9_16
    | ~ spl9_28 ),
    inference(superposition,[],[f176,f102])).

fof(f102,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f101])).

fof(f176,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k10_relat_1(sK2,sK1)
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f175])).

fof(f190,plain,
    ( ~ spl9_7
    | ~ spl9_11
    | spl9_15 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | ~ spl9_7
    | ~ spl9_11
    | spl9_15 ),
    inference(unit_resulting_resolution,[],[f65,f98,f82])).

fof(f82,plain,
    ( ! [X2,X0,X3] :
        ( r2_hidden(X2,k1_relat_1(X0))
        | ~ r2_hidden(k4_tarski(X2,X3),X0) )
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl9_11
  <=> ! [X3,X0,X2] :
        ( ~ r2_hidden(k4_tarski(X2,X3),X0)
        | r2_hidden(X2,k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f98,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | spl9_15 ),
    inference(avatar_component_clause,[],[f97])).

fof(f65,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),sK2)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl9_7
  <=> r2_hidden(k4_tarski(sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f187,plain,
    ( ~ spl9_15
    | ~ spl9_4
    | ~ spl9_16
    | spl9_27
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f183,f175,f163,f101,f53,f97])).

fof(f163,plain,
    ( spl9_27
  <=> r2_hidden(sK3,k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f183,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl9_4
    | ~ spl9_16
    | spl9_27
    | ~ spl9_28 ),
    inference(backward_demodulation,[],[f172,f181])).

fof(f172,plain,
    ( ~ r2_hidden(sK3,k10_relat_1(sK2,sK1))
    | spl9_27 ),
    inference(avatar_component_clause,[],[f163])).

fof(f177,plain,
    ( spl9_28
    | ~ spl9_4
    | ~ spl9_19
    | ~ spl9_25 ),
    inference(avatar_split_clause,[],[f159,f150,f122,f53,f175])).

fof(f122,plain,
    ( spl9_19
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f150,plain,
    ( spl9_25
  <=> k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f159,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k10_relat_1(sK2,sK1)
    | ~ spl9_4
    | ~ spl9_19
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f157,f54])).

fof(f157,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k10_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl9_19
    | ~ spl9_25 ),
    inference(superposition,[],[f151,f123])).

fof(f123,plain,
    ( ! [X2,X0,X3,X1] :
        ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f122])).

fof(f151,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,sK1)
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f150])).

fof(f173,plain,
    ( ~ spl9_27
    | ~ spl9_4
    | spl9_5
    | ~ spl9_19
    | ~ spl9_25 ),
    inference(avatar_split_clause,[],[f166,f150,f122,f57,f53,f163])).

fof(f57,plain,
    ( spl9_5
  <=> r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f166,plain,
    ( ~ r2_hidden(sK3,k10_relat_1(sK2,sK1))
    | ~ spl9_4
    | spl9_5
    | ~ spl9_19
    | ~ spl9_25 ),
    inference(forward_demodulation,[],[f67,f159])).

fof(f67,plain,
    ( ~ r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))
    | spl9_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f152,plain,
    ( spl9_25
    | ~ spl9_4
    | ~ spl9_23 ),
    inference(avatar_split_clause,[],[f144,f138,f53,f150])).

fof(f138,plain,
    ( spl9_23
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f144,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,sK1)
    | ~ spl9_4
    | ~ spl9_23 ),
    inference(resolution,[],[f139,f54])).

fof(f139,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) )
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f138])).

fof(f140,plain,(
    spl9_23 ),
    inference(avatar_split_clause,[],[f36,f138])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f124,plain,(
    spl9_19 ),
    inference(avatar_split_clause,[],[f37,f122])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f120,plain,
    ( spl9_15
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f114,f101,f57,f53,f97])).

fof(f114,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f110,f54])).

fof(f110,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl9_5
    | ~ spl9_16 ),
    inference(superposition,[],[f58,f102])).

fof(f58,plain,
    ( r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f118,plain,(
    spl9_18 ),
    inference(avatar_split_clause,[],[f30,f116])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X0,sK8(X0,X1,X2)),X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f103,plain,(
    spl9_16 ),
    inference(avatar_split_clause,[],[f34,f101])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f92,plain,(
    spl9_13 ),
    inference(avatar_split_clause,[],[f31,f90])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK8(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f83,plain,(
    spl9_11 ),
    inference(avatar_split_clause,[],[f39,f81])).

fof(f39,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f79,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f33,f77])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f75,plain,(
    spl9_9 ),
    inference(avatar_split_clause,[],[f24,f73])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f71,plain,
    ( ~ spl9_5
    | spl9_8 ),
    inference(avatar_split_clause,[],[f17,f69,f57])).

fof(f17,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK1)
      | ~ r2_hidden(k4_tarski(sK3,X4),sK2)
      | ~ r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                  <~> ? [X4] :
                        ( r2_hidden(k4_tarski(X3,X4),X2)
                        & m1_subset_1(X4,X1) ) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,X0)
                   => ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                    <=> ? [X4] :
                          ( r2_hidden(k4_tarski(X3,X4),X2)
                          & m1_subset_1(X4,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                  <=> ? [X4] :
                        ( r2_hidden(k4_tarski(X3,X4),X2)
                        & m1_subset_1(X4,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relset_1)).

fof(f66,plain,
    ( spl9_5
    | spl9_7 ),
    inference(avatar_split_clause,[],[f19,f64,f57])).

fof(f19,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),sK2)
    | r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f55,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f21,f53])).

fof(f21,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.16/0.36  % Computer   : n024.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % WCLimit    : 600
% 0.16/0.36  % DateTime   : Tue Dec  1 14:11:36 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.22/0.47  % (15042)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.47  % (15034)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.48  % (15038)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (15039)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (15038)Refutation not found, incomplete strategy% (15038)------------------------------
% 0.22/0.48  % (15038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (15030)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (15038)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (15038)Memory used [KB]: 1663
% 0.22/0.48  % (15038)Time elapsed: 0.053 s
% 0.22/0.48  % (15038)------------------------------
% 0.22/0.48  % (15038)------------------------------
% 0.22/0.48  % (15034)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (15031)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f291,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f55,f66,f71,f75,f79,f83,f92,f103,f118,f120,f124,f140,f152,f173,f177,f187,f190,f211,f215,f239,f245,f261,f279,f290])).
% 0.22/0.50  fof(f290,plain,(
% 0.22/0.50    ~spl9_4 | ~spl9_10 | spl9_42),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f288])).
% 0.22/0.50  fof(f288,plain,(
% 0.22/0.50    $false | (~spl9_4 | ~spl9_10 | spl9_42)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f54,f278,f78])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl9_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f77])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    spl9_10 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.22/0.50  fof(f278,plain,(
% 0.22/0.50    ~v1_relat_1(sK2) | spl9_42),
% 0.22/0.50    inference(avatar_component_clause,[],[f277])).
% 0.22/0.50  fof(f277,plain,(
% 0.22/0.50    spl9_42 <=> v1_relat_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl9_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    spl9_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.22/0.50  fof(f279,plain,(
% 0.22/0.50    ~spl9_42 | ~spl9_13 | ~spl9_15 | ~spl9_31 | ~spl9_40),
% 0.22/0.50    inference(avatar_split_clause,[],[f272,f259,f209,f97,f90,f277])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    spl9_13 <=> ! [X1,X0,X2] : (~v1_relat_1(X2) | r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    spl9_15 <=> r2_hidden(sK3,k1_relat_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.22/0.50  fof(f209,plain,(
% 0.22/0.50    spl9_31 <=> k1_relat_1(sK2) = k10_relat_1(sK2,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).
% 0.22/0.50  fof(f259,plain,(
% 0.22/0.50    spl9_40 <=> ! [X0] : (~r2_hidden(sK3,k10_relat_1(sK2,X0)) | ~r2_hidden(sK8(sK3,X0,sK2),sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).
% 0.22/0.50  fof(f272,plain,(
% 0.22/0.50    ~v1_relat_1(sK2) | (~spl9_13 | ~spl9_15 | ~spl9_31 | ~spl9_40)),
% 0.22/0.50    inference(subsumption_resolution,[],[f271,f119])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    r2_hidden(sK3,k1_relat_1(sK2)) | ~spl9_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f97])).
% 0.22/0.50  fof(f271,plain,(
% 0.22/0.50    ~r2_hidden(sK3,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl9_13 | ~spl9_31 | ~spl9_40)),
% 0.22/0.50    inference(forward_demodulation,[],[f270,f210])).
% 0.22/0.50  fof(f210,plain,(
% 0.22/0.50    k1_relat_1(sK2) = k10_relat_1(sK2,sK1) | ~spl9_31),
% 0.22/0.50    inference(avatar_component_clause,[],[f209])).
% 0.22/0.50  fof(f270,plain,(
% 0.22/0.50    ~r2_hidden(sK3,k10_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | (~spl9_13 | ~spl9_40)),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f269])).
% 0.22/0.50  fof(f269,plain,(
% 0.22/0.50    ~r2_hidden(sK3,k10_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | ~r2_hidden(sK3,k10_relat_1(sK2,sK1)) | (~spl9_13 | ~spl9_40)),
% 0.22/0.50    inference(resolution,[],[f260,f91])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r2_hidden(sK8(X0,X1,X2),X1) | ~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) ) | ~spl9_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f90])).
% 0.22/0.50  fof(f260,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(sK8(sK3,X0,sK2),sK1) | ~r2_hidden(sK3,k10_relat_1(sK2,X0))) ) | ~spl9_40),
% 0.22/0.50    inference(avatar_component_clause,[],[f259])).
% 0.22/0.50  fof(f261,plain,(
% 0.22/0.50    spl9_40 | ~spl9_9 | ~spl9_37),
% 0.22/0.50    inference(avatar_split_clause,[],[f253,f243,f73,f259])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    spl9_9 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.22/0.50  fof(f243,plain,(
% 0.22/0.50    spl9_37 <=> ! [X0] : (~r2_hidden(sK3,k10_relat_1(sK2,X0)) | ~m1_subset_1(sK8(sK3,X0,sK2),sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).
% 0.22/0.50  fof(f253,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(sK3,k10_relat_1(sK2,X0)) | ~r2_hidden(sK8(sK3,X0,sK2),sK1)) ) | (~spl9_9 | ~spl9_37)),
% 0.22/0.50    inference(resolution,[],[f244,f74])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) ) | ~spl9_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f73])).
% 0.22/0.50  fof(f244,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(sK8(sK3,X0,sK2),sK1) | ~r2_hidden(sK3,k10_relat_1(sK2,X0))) ) | ~spl9_37),
% 0.22/0.50    inference(avatar_component_clause,[],[f243])).
% 0.22/0.50  fof(f245,plain,(
% 0.22/0.50    spl9_37 | ~spl9_8 | ~spl9_36),
% 0.22/0.50    inference(avatar_split_clause,[],[f240,f237,f69,f243])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    spl9_8 <=> ! [X4] : (~m1_subset_1(X4,sK1) | ~r2_hidden(k4_tarski(sK3,X4),sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.22/0.50  fof(f237,plain,(
% 0.22/0.50    spl9_36 <=> ! [X5,X6] : (~r2_hidden(X5,k10_relat_1(sK2,X6)) | r2_hidden(k4_tarski(X5,sK8(X5,X6,sK2)),sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).
% 0.22/0.50  fof(f240,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(sK3,k10_relat_1(sK2,X0)) | ~m1_subset_1(sK8(sK3,X0,sK2),sK1)) ) | (~spl9_8 | ~spl9_36)),
% 0.22/0.50    inference(resolution,[],[f238,f70])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ( ! [X4] : (~r2_hidden(k4_tarski(sK3,X4),sK2) | ~m1_subset_1(X4,sK1)) ) | ~spl9_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f69])).
% 0.22/0.50  fof(f238,plain,(
% 0.22/0.50    ( ! [X6,X5] : (r2_hidden(k4_tarski(X5,sK8(X5,X6,sK2)),sK2) | ~r2_hidden(X5,k10_relat_1(sK2,X6))) ) | ~spl9_36),
% 0.22/0.50    inference(avatar_component_clause,[],[f237])).
% 0.22/0.50  fof(f239,plain,(
% 0.22/0.50    spl9_36 | ~spl9_4 | ~spl9_32),
% 0.22/0.50    inference(avatar_split_clause,[],[f217,f213,f53,f237])).
% 0.22/0.50  fof(f213,plain,(
% 0.22/0.50    spl9_32 <=> ! [X1,X3,X0,X2,X4] : (r2_hidden(k4_tarski(X0,sK8(X0,X1,X2)),X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).
% 0.22/0.50  fof(f217,plain,(
% 0.22/0.50    ( ! [X6,X5] : (~r2_hidden(X5,k10_relat_1(sK2,X6)) | r2_hidden(k4_tarski(X5,sK8(X5,X6,sK2)),sK2)) ) | (~spl9_4 | ~spl9_32)),
% 0.22/0.50    inference(resolution,[],[f214,f54])).
% 0.22/0.50  fof(f214,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(k4_tarski(X0,sK8(X0,X1,X2)),X2)) ) | ~spl9_32),
% 0.22/0.50    inference(avatar_component_clause,[],[f213])).
% 0.22/0.50  fof(f215,plain,(
% 0.22/0.50    spl9_32 | ~spl9_10 | ~spl9_18),
% 0.22/0.50    inference(avatar_split_clause,[],[f141,f116,f77,f213])).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    spl9_18 <=> ! [X1,X0,X2] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(X0,sK8(X0,X1,X2)),X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,sK8(X0,X1,X2)),X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ) | (~spl9_10 | ~spl9_18)),
% 0.22/0.50    inference(resolution,[],[f117,f78])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(X0,sK8(X0,X1,X2)),X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) ) | ~spl9_18),
% 0.22/0.50    inference(avatar_component_clause,[],[f116])).
% 0.22/0.50  fof(f211,plain,(
% 0.22/0.50    spl9_31 | ~spl9_4 | ~spl9_16 | ~spl9_28),
% 0.22/0.50    inference(avatar_split_clause,[],[f181,f175,f101,f53,f209])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    spl9_16 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.22/0.50  fof(f175,plain,(
% 0.22/0.50    spl9_28 <=> k1_relset_1(sK0,sK1,sK2) = k10_relat_1(sK2,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).
% 0.22/0.50  fof(f181,plain,(
% 0.22/0.50    k1_relat_1(sK2) = k10_relat_1(sK2,sK1) | (~spl9_4 | ~spl9_16 | ~spl9_28)),
% 0.22/0.50    inference(subsumption_resolution,[],[f179,f54])).
% 0.22/0.50  fof(f179,plain,(
% 0.22/0.50    k1_relat_1(sK2) = k10_relat_1(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl9_16 | ~spl9_28)),
% 0.22/0.50    inference(superposition,[],[f176,f102])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl9_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f101])).
% 0.22/0.50  fof(f176,plain,(
% 0.22/0.50    k1_relset_1(sK0,sK1,sK2) = k10_relat_1(sK2,sK1) | ~spl9_28),
% 0.22/0.50    inference(avatar_component_clause,[],[f175])).
% 0.22/0.50  fof(f190,plain,(
% 0.22/0.50    ~spl9_7 | ~spl9_11 | spl9_15),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f188])).
% 0.22/0.50  fof(f188,plain,(
% 0.22/0.50    $false | (~spl9_7 | ~spl9_11 | spl9_15)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f65,f98,f82])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    ( ! [X2,X0,X3] : (r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X2,X3),X0)) ) | ~spl9_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f81])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    spl9_11 <=> ! [X3,X0,X2] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    ~r2_hidden(sK3,k1_relat_1(sK2)) | spl9_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f97])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    r2_hidden(k4_tarski(sK3,sK4),sK2) | ~spl9_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f64])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    spl9_7 <=> r2_hidden(k4_tarski(sK3,sK4),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.22/0.50  fof(f187,plain,(
% 0.22/0.50    ~spl9_15 | ~spl9_4 | ~spl9_16 | spl9_27 | ~spl9_28),
% 0.22/0.50    inference(avatar_split_clause,[],[f183,f175,f163,f101,f53,f97])).
% 0.22/0.50  fof(f163,plain,(
% 0.22/0.50    spl9_27 <=> r2_hidden(sK3,k10_relat_1(sK2,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).
% 0.22/0.50  fof(f183,plain,(
% 0.22/0.50    ~r2_hidden(sK3,k1_relat_1(sK2)) | (~spl9_4 | ~spl9_16 | spl9_27 | ~spl9_28)),
% 0.22/0.50    inference(backward_demodulation,[],[f172,f181])).
% 0.22/0.50  fof(f172,plain,(
% 0.22/0.50    ~r2_hidden(sK3,k10_relat_1(sK2,sK1)) | spl9_27),
% 0.22/0.50    inference(avatar_component_clause,[],[f163])).
% 0.22/0.50  fof(f177,plain,(
% 0.22/0.50    spl9_28 | ~spl9_4 | ~spl9_19 | ~spl9_25),
% 0.22/0.50    inference(avatar_split_clause,[],[f159,f150,f122,f53,f175])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    spl9_19 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 0.22/0.50  fof(f150,plain,(
% 0.22/0.50    spl9_25 <=> k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    k1_relset_1(sK0,sK1,sK2) = k10_relat_1(sK2,sK1) | (~spl9_4 | ~spl9_19 | ~spl9_25)),
% 0.22/0.50    inference(subsumption_resolution,[],[f157,f54])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    k1_relset_1(sK0,sK1,sK2) = k10_relat_1(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl9_19 | ~spl9_25)),
% 0.22/0.50    inference(superposition,[],[f151,f123])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl9_19),
% 0.22/0.50    inference(avatar_component_clause,[],[f122])).
% 0.22/0.50  fof(f151,plain,(
% 0.22/0.50    k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,sK1) | ~spl9_25),
% 0.22/0.50    inference(avatar_component_clause,[],[f150])).
% 0.22/0.50  fof(f173,plain,(
% 0.22/0.50    ~spl9_27 | ~spl9_4 | spl9_5 | ~spl9_19 | ~spl9_25),
% 0.22/0.50    inference(avatar_split_clause,[],[f166,f150,f122,f57,f53,f163])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    spl9_5 <=> r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.22/0.50  fof(f166,plain,(
% 0.22/0.50    ~r2_hidden(sK3,k10_relat_1(sK2,sK1)) | (~spl9_4 | spl9_5 | ~spl9_19 | ~spl9_25)),
% 0.22/0.50    inference(forward_demodulation,[],[f67,f159])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    ~r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) | spl9_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f57])).
% 0.22/0.50  fof(f152,plain,(
% 0.22/0.50    spl9_25 | ~spl9_4 | ~spl9_23),
% 0.22/0.50    inference(avatar_split_clause,[],[f144,f138,f53,f150])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    spl9_23 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 0.22/0.50  fof(f144,plain,(
% 0.22/0.50    k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,sK1) | (~spl9_4 | ~spl9_23)),
% 0.22/0.50    inference(resolution,[],[f139,f54])).
% 0.22/0.50  fof(f139,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)) ) | ~spl9_23),
% 0.22/0.50    inference(avatar_component_clause,[],[f138])).
% 0.22/0.50  fof(f140,plain,(
% 0.22/0.50    spl9_23),
% 0.22/0.50    inference(avatar_split_clause,[],[f36,f138])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    spl9_19),
% 0.22/0.50    inference(avatar_split_clause,[],[f37,f122])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    spl9_15 | ~spl9_4 | ~spl9_5 | ~spl9_16),
% 0.22/0.50    inference(avatar_split_clause,[],[f114,f101,f57,f53,f97])).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    r2_hidden(sK3,k1_relat_1(sK2)) | (~spl9_4 | ~spl9_5 | ~spl9_16)),
% 0.22/0.50    inference(subsumption_resolution,[],[f110,f54])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    r2_hidden(sK3,k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl9_5 | ~spl9_16)),
% 0.22/0.50    inference(superposition,[],[f58,f102])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) | ~spl9_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f57])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    spl9_18),
% 0.22/0.50    inference(avatar_split_clause,[],[f30,f116])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(X0,sK8(X0,X1,X2)),X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    spl9_16),
% 0.22/0.50    inference(avatar_split_clause,[],[f34,f101])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    spl9_13),
% 0.22/0.50    inference(avatar_split_clause,[],[f31,f90])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    spl9_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f39,f81])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 0.22/0.50    inference(equality_resolution,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    spl9_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f33,f77])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    spl9_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f24,f73])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    ~spl9_5 | spl9_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f17,f69,f57])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ( ! [X4] : (~m1_subset_1(X4,sK1) | ~r2_hidden(k4_tarski(sK3,X4),sK2) | ~r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_hidden(X3,k1_relset_1(X0,X1,X2)) <~> ? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1))) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,k1_relset_1(X0,X1,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1)))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f8])).
% 0.22/0.50  fof(f8,conjecture,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,k1_relset_1(X0,X1,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1)))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relset_1)).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    spl9_5 | spl9_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f19,f64,f57])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    r2_hidden(k4_tarski(sK3,sK4),sK2) | r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))),
% 0.22/0.50    inference(cnf_transformation,[],[f10])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    spl9_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f21,f53])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    inference(cnf_transformation,[],[f10])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (15034)------------------------------
% 0.22/0.50  % (15034)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (15034)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (15034)Memory used [KB]: 10874
% 0.22/0.50  % (15034)Time elapsed: 0.065 s
% 0.22/0.50  % (15034)------------------------------
% 0.22/0.50  % (15034)------------------------------
% 0.22/0.50  % (15027)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.50  % (15024)Success in time 0.13 s
%------------------------------------------------------------------------------
