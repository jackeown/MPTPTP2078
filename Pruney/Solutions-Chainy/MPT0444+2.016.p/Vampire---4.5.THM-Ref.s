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
% DateTime   : Thu Dec  3 12:47:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 142 expanded)
%              Number of leaves         :   27 (  65 expanded)
%              Depth                    :    6
%              Number of atoms          :  239 ( 386 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f191,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f57,f61,f65,f73,f77,f106,f111,f117,f127,f148,f157,f169,f176,f188,f190])).

fof(f190,plain,
    ( ~ spl2_2
    | ~ spl2_18
    | spl2_21
    | ~ spl2_22
    | ~ spl2_25 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_18
    | spl2_21
    | ~ spl2_22
    | ~ spl2_25 ),
    inference(subsumption_resolution,[],[f158,f187])).

fof(f187,plain,
    ( ! [X0] : v1_relat_1(k3_xboole_0(sK0,X0))
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl2_25
  <=> ! [X0] : v1_relat_1(k3_xboole_0(sK0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f158,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_18
    | spl2_21
    | ~ spl2_22 ),
    inference(unit_resulting_resolution,[],[f51,f147,f156,f126])).

fof(f126,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl2_18
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f156,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0)
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl2_22
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f147,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1))
    | spl2_21 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl2_21
  <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f51,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f188,plain,
    ( spl2_25
    | ~ spl2_1
    | ~ spl2_8
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f170,f167,f75,f44,f186])).

fof(f44,plain,
    ( spl2_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f75,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f167,plain,
    ( spl2_23
  <=> ! [X1,X0] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f170,plain,
    ( ! [X0] : v1_relat_1(k3_xboole_0(sK0,X0))
    | ~ spl2_1
    | ~ spl2_8
    | ~ spl2_23 ),
    inference(unit_resulting_resolution,[],[f46,f168,f76])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f75])).

fof(f168,plain,
    ( ! [X0,X1] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f167])).

fof(f46,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f176,plain,
    ( ~ spl2_1
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_18
    | spl2_20
    | ~ spl2_23 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_18
    | spl2_20
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f149,f170])).

fof(f149,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_18
    | spl2_20 ),
    inference(unit_resulting_resolution,[],[f46,f64,f143,f126])).

fof(f143,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0))
    | spl2_20 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl2_20
  <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f64,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl2_5
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f169,plain,
    ( spl2_23
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f91,f71,f63,f167])).

fof(f71,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f91,plain,
    ( ! [X0,X1] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f64,f72])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f71])).

fof(f157,plain,
    ( spl2_22
    | ~ spl2_4
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f113,f109,f59,f155])).

fof(f59,plain,
    ( spl2_4
  <=> ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f109,plain,
    ( spl2_15
  <=> ! [X1,X0,X2] : r1_tarski(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f113,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0)
    | ~ spl2_4
    | ~ spl2_15 ),
    inference(superposition,[],[f110,f60])).

fof(f60,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = X0
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f110,plain,
    ( ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f109])).

fof(f148,plain,
    ( ~ spl2_20
    | ~ spl2_21
    | spl2_3
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f132,f115,f54,f145,f141])).

fof(f54,plain,
    ( spl2_3
  <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f115,plain,
    ( spl2_16
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f132,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0))
    | spl2_3
    | ~ spl2_16 ),
    inference(resolution,[],[f116,f56])).

fof(f56,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f116,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f115])).

fof(f127,plain,(
    spl2_18 ),
    inference(avatar_split_clause,[],[f30,f125])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f117,plain,(
    spl2_16 ),
    inference(avatar_split_clause,[],[f42,f115])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f111,plain,
    ( spl2_15
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f107,f104,f109])).

fof(f104,plain,
    ( spl2_14
  <=> ! [X1,X0,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f107,plain,
    ( ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2))
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f105,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f105,plain,
    ( ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f104])).

fof(f106,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f40,f104])).

fof(f40,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f77,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f31,f75])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f73,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f38,f71])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f65,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f33,f63])).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f61,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f32,f59])).

fof(f32,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f57,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f28,f54])).

fof(f28,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

fof(f52,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f27,f49])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f26,f44])).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:37:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (31216)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (31219)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.47  % (31216)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f191,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f47,f52,f57,f61,f65,f73,f77,f106,f111,f117,f127,f148,f157,f169,f176,f188,f190])).
% 0.21/0.47  fof(f190,plain,(
% 0.21/0.47    ~spl2_2 | ~spl2_18 | spl2_21 | ~spl2_22 | ~spl2_25),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f189])).
% 0.21/0.47  fof(f189,plain,(
% 0.21/0.47    $false | (~spl2_2 | ~spl2_18 | spl2_21 | ~spl2_22 | ~spl2_25)),
% 0.21/0.47    inference(subsumption_resolution,[],[f158,f187])).
% 0.21/0.47  fof(f187,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k3_xboole_0(sK0,X0))) ) | ~spl2_25),
% 0.21/0.47    inference(avatar_component_clause,[],[f186])).
% 0.21/0.47  fof(f186,plain,(
% 0.21/0.47    spl2_25 <=> ! [X0] : v1_relat_1(k3_xboole_0(sK0,X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.21/0.47  fof(f158,plain,(
% 0.21/0.47    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | (~spl2_2 | ~spl2_18 | spl2_21 | ~spl2_22)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f51,f147,f156,f126])).
% 0.21/0.47  fof(f126,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_18),
% 0.21/0.47    inference(avatar_component_clause,[],[f125])).
% 0.21/0.47  fof(f125,plain,(
% 0.21/0.47    spl2_18 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.47  fof(f156,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) ) | ~spl2_22),
% 0.21/0.47    inference(avatar_component_clause,[],[f155])).
% 0.21/0.47  fof(f155,plain,(
% 0.21/0.47    spl2_22 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X1,X0),X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.21/0.47  fof(f147,plain,(
% 0.21/0.47    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1)) | spl2_21),
% 0.21/0.47    inference(avatar_component_clause,[],[f145])).
% 0.21/0.47  fof(f145,plain,(
% 0.21/0.47    spl2_21 <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    v1_relat_1(sK1) | ~spl2_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    spl2_2 <=> v1_relat_1(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.47  fof(f188,plain,(
% 0.21/0.47    spl2_25 | ~spl2_1 | ~spl2_8 | ~spl2_23),
% 0.21/0.47    inference(avatar_split_clause,[],[f170,f167,f75,f44,f186])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    spl2_1 <=> v1_relat_1(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    spl2_8 <=> ! [X1,X0] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.47  fof(f167,plain,(
% 0.21/0.47    spl2_23 <=> ! [X1,X0] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.21/0.47  fof(f170,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k3_xboole_0(sK0,X0))) ) | (~spl2_1 | ~spl2_8 | ~spl2_23)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f46,f168,f76])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f75])).
% 0.21/0.47  fof(f168,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | ~spl2_23),
% 0.21/0.47    inference(avatar_component_clause,[],[f167])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    v1_relat_1(sK0) | ~spl2_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f44])).
% 0.21/0.47  fof(f176,plain,(
% 0.21/0.47    ~spl2_1 | ~spl2_5 | ~spl2_8 | ~spl2_18 | spl2_20 | ~spl2_23),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f175])).
% 0.21/0.47  fof(f175,plain,(
% 0.21/0.47    $false | (~spl2_1 | ~spl2_5 | ~spl2_8 | ~spl2_18 | spl2_20 | ~spl2_23)),
% 0.21/0.47    inference(subsumption_resolution,[],[f149,f170])).
% 0.21/0.47  fof(f149,plain,(
% 0.21/0.47    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | (~spl2_1 | ~spl2_5 | ~spl2_18 | spl2_20)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f46,f64,f143,f126])).
% 0.21/0.47  fof(f143,plain,(
% 0.21/0.47    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0)) | spl2_20),
% 0.21/0.47    inference(avatar_component_clause,[],[f141])).
% 0.21/0.47  fof(f141,plain,(
% 0.21/0.47    spl2_20 <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl2_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f63])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    spl2_5 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.47  fof(f169,plain,(
% 0.21/0.47    spl2_23 | ~spl2_5 | ~spl2_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f91,f71,f63,f167])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    spl2_7 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | (~spl2_5 | ~spl2_7)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f64,f72])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl2_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f71])).
% 0.21/0.47  fof(f157,plain,(
% 0.21/0.47    spl2_22 | ~spl2_4 | ~spl2_15),
% 0.21/0.47    inference(avatar_split_clause,[],[f113,f109,f59,f155])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    spl2_4 <=> ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    spl2_15 <=> ! [X1,X0,X2] : r1_tarski(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) ) | (~spl2_4 | ~spl2_15)),
% 0.21/0.47    inference(superposition,[],[f110,f60])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) ) | ~spl2_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f59])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2))) ) | ~spl2_15),
% 0.21/0.47    inference(avatar_component_clause,[],[f109])).
% 0.21/0.47  fof(f148,plain,(
% 0.21/0.47    ~spl2_20 | ~spl2_21 | spl2_3 | ~spl2_16),
% 0.21/0.47    inference(avatar_split_clause,[],[f132,f115,f54,f145,f141])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    spl2_3 <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    spl2_16 <=> ! [X1,X0,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1)) | ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0)) | (spl2_3 | ~spl2_16)),
% 0.21/0.47    inference(resolution,[],[f116,f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) | spl2_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f54])).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl2_16),
% 0.21/0.47    inference(avatar_component_clause,[],[f115])).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    spl2_18),
% 0.21/0.47    inference(avatar_split_clause,[],[f30,f125])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    spl2_16),
% 0.21/0.47    inference(avatar_split_clause,[],[f42,f115])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    spl2_15 | ~spl2_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f107,f104,f109])).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    spl2_14 <=> ! [X1,X0,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2))) ) | ~spl2_14),
% 0.21/0.47    inference(forward_demodulation,[],[f105,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) ) | ~spl2_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f104])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    spl2_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f40,f104])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    spl2_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f31,f75])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    spl2_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f38,f71])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.47    inference(nnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    spl2_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f33,f63])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    spl2_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f32,f59])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.47    inference(rectify,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ~spl2_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f28,f54])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f23,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 0.21/0.47    inference(negated_conjecture,[],[f13])).
% 0.21/0.47  fof(f13,conjecture,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f27,f49])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    v1_relat_1(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    spl2_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f26,f44])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    v1_relat_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (31216)------------------------------
% 0.21/0.47  % (31216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (31216)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (31216)Memory used [KB]: 6140
% 0.21/0.47  % (31216)Time elapsed: 0.054 s
% 0.21/0.47  % (31216)------------------------------
% 0.21/0.47  % (31216)------------------------------
% 0.21/0.47  % (31210)Success in time 0.11 s
%------------------------------------------------------------------------------
