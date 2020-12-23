%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 256 expanded)
%              Number of leaves         :   35 ( 103 expanded)
%              Depth                    :    9
%              Number of atoms          :  367 ( 693 expanded)
%              Number of equality atoms :   50 ( 128 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f394,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f98,f103,f111,f127,f136,f145,f162,f173,f194,f212,f230,f235,f293,f306,f316,f340,f367,f379,f392])).

fof(f392,plain,(
    ~ spl7_31 ),
    inference(avatar_contradiction_clause,[],[f385])).

fof(f385,plain,
    ( $false
    | ~ spl7_31 ),
    inference(unit_resulting_resolution,[],[f50,f366,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f366,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f364])).

fof(f364,plain,
    ( spl7_31
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f379,plain,(
    ~ spl7_29 ),
    inference(avatar_contradiction_clause,[],[f373])).

fof(f373,plain,
    ( $false
    | ~ spl7_29 ),
    inference(unit_resulting_resolution,[],[f50,f339,f64])).

fof(f339,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0)
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f337])).

fof(f337,plain,
    ( spl7_29
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f367,plain,
    ( spl7_31
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f356,f191,f138,f364])).

fof(f138,plain,
    ( spl7_9
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f191,plain,
    ( spl7_15
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f356,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(forward_demodulation,[],[f355,f47])).

fof(f47,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f355,plain,
    ( r2_hidden(sK0,k1_relat_1(k1_xboole_0))
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(forward_demodulation,[],[f140,f193])).

fof(f193,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f191])).

fof(f140,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f138])).

fof(f340,plain,
    ( ~ spl7_18
    | ~ spl7_17
    | spl7_10
    | spl7_29
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f322,f290,f337,f142,f227,f232])).

fof(f232,plain,
    ( spl7_18
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f227,plain,
    ( spl7_17
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f142,plain,
    ( spl7_10
  <=> r2_hidden(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f290,plain,
    ( spl7_25
  <=> r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f322,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0)
    | r2_hidden(k1_xboole_0,sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl7_25 ),
    inference(forward_demodulation,[],[f320,f47])).

fof(f320,plain,
    ( r2_hidden(k1_xboole_0,sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl7_25 ),
    inference(superposition,[],[f292,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_funct_1(X0,X1)
      | ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | k1_xboole_0 != X2
      | k1_funct_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f292,plain,
    ( r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),sK1)
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f290])).

fof(f316,plain,(
    spl7_26 ),
    inference(avatar_contradiction_clause,[],[f312])).

fof(f312,plain,
    ( $false
    | spl7_26 ),
    inference(unit_resulting_resolution,[],[f46,f305])).

fof(f305,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl7_26 ),
    inference(avatar_component_clause,[],[f303])).

fof(f303,plain,
    ( spl7_26
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f306,plain,
    ( ~ spl7_26
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f301,f286,f303])).

fof(f286,plain,
    ( spl7_24
  <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f301,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_24 ),
    inference(superposition,[],[f77,f288])).

fof(f288,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f286])).

fof(f77,plain,(
    ! [X0] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f49,f74])).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f61,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f61,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f49,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f293,plain,
    ( spl7_24
    | spl7_25
    | ~ spl7_12
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f275,f191,f160,f290,f286])).

fof(f160,plain,
    ( spl7_12
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | r2_hidden(k1_funct_1(sK2,X0),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f275,plain,
    ( r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),sK1)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl7_12
    | ~ spl7_15 ),
    inference(resolution,[],[f269,f60])).

fof(f60,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

fof(f269,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | r2_hidden(k1_funct_1(k1_xboole_0,X0),sK1) )
    | ~ spl7_12
    | ~ spl7_15 ),
    inference(forward_demodulation,[],[f161,f193])).

fof(f161,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | r2_hidden(k1_funct_1(sK2,X0),sK1) )
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f160])).

fof(f235,plain,
    ( spl7_18
    | ~ spl7_8
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f221,f191,f133,f232])).

fof(f133,plain,
    ( spl7_8
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f221,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_8
    | ~ spl7_15 ),
    inference(backward_demodulation,[],[f135,f193])).

fof(f135,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f133])).

fof(f230,plain,
    ( spl7_17
    | ~ spl7_1
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f216,f191,f90,f227])).

fof(f90,plain,
    ( spl7_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f216,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_15 ),
    inference(backward_demodulation,[],[f92,f193])).

fof(f92,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f212,plain,
    ( ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_7
    | ~ spl7_14 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_7
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f92,f97,f102,f172,f110,f126,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(X3,X2),X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f126,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl7_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f110,plain,
    ( v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl7_4
  <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f172,plain,
    ( r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl7_14
  <=> r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f102,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl7_3
  <=> r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f97,plain,
    ( k1_xboole_0 != sK1
    | spl7_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f194,plain,
    ( spl7_15
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f176,f167,f191])).

fof(f167,plain,
    ( spl7_13
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f176,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_13 ),
    inference(resolution,[],[f168,f60])).

fof(f168,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f167])).

fof(f173,plain,
    ( spl7_13
    | spl7_14
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f165,f124,f170,f167])).

fof(f165,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl7_7 ),
    inference(duplicate_literal_removal,[],[f164])).

fof(f164,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK2) )
    | ~ spl7_7 ),
    inference(superposition,[],[f154,f152])).

fof(f152,plain,
    ( ! [X0] :
        ( k1_mcart_1(X0) = sK0
        | ~ r2_hidden(X0,sK2) )
    | ~ spl7_7 ),
    inference(resolution,[],[f131,f79])).

% (7340)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f69,f74])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f17])).

% (7350)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f131,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
        | ~ r2_hidden(X2,sK2) )
    | ~ spl7_7 ),
    inference(resolution,[],[f126,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f154,plain,
    ( ! [X2] :
        ( r2_hidden(k1_mcart_1(X2),k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X2,sK2) )
    | ~ spl7_7 ),
    inference(resolution,[],[f131,f66])).

% (7323)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f162,plain,
    ( spl7_2
    | spl7_12
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f128,f124,f108,f90,f160,f95])).

fof(f128,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
        | ~ v1_funct_1(sK2)
        | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | k1_xboole_0 = sK1
        | r2_hidden(k1_funct_1(sK2,X0),sK1) )
    | ~ spl7_7 ),
    inference(resolution,[],[f126,f72])).

fof(f145,plain,
    ( ~ spl7_8
    | spl7_9
    | ~ spl7_1
    | ~ spl7_10
    | spl7_3 ),
    inference(avatar_split_clause,[],[f105,f100,f142,f90,f138,f133])).

fof(f105,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | ~ v1_funct_1(sK2)
    | r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | spl7_3 ),
    inference(superposition,[],[f102,f82])).

fof(f136,plain,
    ( spl7_8
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f129,f124,f133])).

fof(f129,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_7 ),
    inference(resolution,[],[f126,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f127,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f75,f124])).

fof(f75,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f43,f74])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

fof(f111,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f76,f108])).

fof(f76,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f42,f74])).

fof(f42,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f103,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f45,f100])).

fof(f45,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f98,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f44,f95])).

fof(f44,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f93,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f41,f90])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:26:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (7344)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (7335)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (7326)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (7327)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (7330)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (7325)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (7349)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (7321)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (7344)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (7322)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f394,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f93,f98,f103,f111,f127,f136,f145,f162,f173,f194,f212,f230,f235,f293,f306,f316,f340,f367,f379,f392])).
% 0.21/0.54  fof(f392,plain,(
% 0.21/0.54    ~spl7_31),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f385])).
% 0.21/0.54  fof(f385,plain,(
% 0.21/0.54    $false | ~spl7_31),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f50,f366,f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.54  fof(f366,plain,(
% 0.21/0.54    r2_hidden(sK0,k1_xboole_0) | ~spl7_31),
% 0.21/0.54    inference(avatar_component_clause,[],[f364])).
% 0.21/0.54  fof(f364,plain,(
% 0.21/0.54    spl7_31 <=> r2_hidden(sK0,k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.54  fof(f379,plain,(
% 0.21/0.54    ~spl7_29),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f373])).
% 0.21/0.54  fof(f373,plain,(
% 0.21/0.54    $false | ~spl7_29),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f50,f339,f64])).
% 0.21/0.54  fof(f339,plain,(
% 0.21/0.54    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0) | ~spl7_29),
% 0.21/0.54    inference(avatar_component_clause,[],[f337])).
% 0.21/0.54  fof(f337,plain,(
% 0.21/0.54    spl7_29 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 0.21/0.54  fof(f367,plain,(
% 0.21/0.54    spl7_31 | ~spl7_9 | ~spl7_15),
% 0.21/0.54    inference(avatar_split_clause,[],[f356,f191,f138,f364])).
% 0.21/0.54  fof(f138,plain,(
% 0.21/0.54    spl7_9 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.54  fof(f191,plain,(
% 0.21/0.54    spl7_15 <=> k1_xboole_0 = sK2),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.54  fof(f356,plain,(
% 0.21/0.54    r2_hidden(sK0,k1_xboole_0) | (~spl7_9 | ~spl7_15)),
% 0.21/0.54    inference(forward_demodulation,[],[f355,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.54    inference(cnf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.54  fof(f355,plain,(
% 0.21/0.54    r2_hidden(sK0,k1_relat_1(k1_xboole_0)) | (~spl7_9 | ~spl7_15)),
% 0.21/0.54    inference(forward_demodulation,[],[f140,f193])).
% 0.21/0.54  fof(f193,plain,(
% 0.21/0.54    k1_xboole_0 = sK2 | ~spl7_15),
% 0.21/0.54    inference(avatar_component_clause,[],[f191])).
% 0.21/0.54  fof(f140,plain,(
% 0.21/0.54    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl7_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f138])).
% 0.21/0.54  fof(f340,plain,(
% 0.21/0.54    ~spl7_18 | ~spl7_17 | spl7_10 | spl7_29 | ~spl7_25),
% 0.21/0.54    inference(avatar_split_clause,[],[f322,f290,f337,f142,f227,f232])).
% 0.21/0.54  fof(f232,plain,(
% 0.21/0.54    spl7_18 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.21/0.54  fof(f227,plain,(
% 0.21/0.54    spl7_17 <=> v1_funct_1(k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.21/0.54  fof(f142,plain,(
% 0.21/0.54    spl7_10 <=> r2_hidden(k1_xboole_0,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.54  fof(f290,plain,(
% 0.21/0.54    spl7_25 <=> r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.21/0.54  fof(f322,plain,(
% 0.21/0.54    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0) | r2_hidden(k1_xboole_0,sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl7_25),
% 0.21/0.54    inference(forward_demodulation,[],[f320,f47])).
% 0.21/0.54  fof(f320,plain,(
% 0.21/0.54    r2_hidden(k1_xboole_0,sK1) | ~v1_funct_1(k1_xboole_0) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~spl7_25),
% 0.21/0.54    inference(superposition,[],[f292,f82])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 = k1_funct_1(X0,X1) | ~v1_funct_1(X0) | r2_hidden(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f55])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(X1,k1_relat_1(X0)) | k1_xboole_0 != X2 | k1_funct_1(X0,X1) = X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).
% 0.21/0.54  fof(f292,plain,(
% 0.21/0.54    r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),sK1) | ~spl7_25),
% 0.21/0.54    inference(avatar_component_clause,[],[f290])).
% 0.21/0.54  fof(f316,plain,(
% 0.21/0.54    spl7_26),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f312])).
% 0.21/0.54  fof(f312,plain,(
% 0.21/0.54    $false | spl7_26),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f46,f305])).
% 0.21/0.54  fof(f305,plain,(
% 0.21/0.54    ~v1_xboole_0(k1_xboole_0) | spl7_26),
% 0.21/0.54    inference(avatar_component_clause,[],[f303])).
% 0.21/0.54  fof(f303,plain,(
% 0.21/0.54    spl7_26 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.54  fof(f306,plain,(
% 0.21/0.54    ~spl7_26 | ~spl7_24),
% 0.21/0.54    inference(avatar_split_clause,[],[f301,f286,f303])).
% 0.21/0.54  fof(f286,plain,(
% 0.21/0.54    spl7_24 <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.21/0.54  fof(f301,plain,(
% 0.21/0.54    ~v1_xboole_0(k1_xboole_0) | ~spl7_24),
% 0.21/0.54    inference(superposition,[],[f77,f288])).
% 0.21/0.54  fof(f288,plain,(
% 0.21/0.54    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl7_24),
% 0.21/0.54    inference(avatar_component_clause,[],[f286])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X0))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f49,f74])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f53,f73])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f61,f65])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.21/0.54  fof(f293,plain,(
% 0.21/0.54    spl7_24 | spl7_25 | ~spl7_12 | ~spl7_15),
% 0.21/0.54    inference(avatar_split_clause,[],[f275,f191,f160,f290,f286])).
% 0.21/0.54  fof(f160,plain,(
% 0.21/0.54    spl7_12 <=> ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(k1_funct_1(sK2,X0),sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.54  fof(f275,plain,(
% 0.21/0.54    r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),sK1) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | (~spl7_12 | ~spl7_15)),
% 0.21/0.54    inference(resolution,[],[f269,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.54    inference(flattening,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | (~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.54    inference(ennf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,axiom,(
% 0.21/0.54    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).
% 0.21/0.54  fof(f269,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(k1_funct_1(k1_xboole_0,X0),sK1)) ) | (~spl7_12 | ~spl7_15)),
% 0.21/0.54    inference(forward_demodulation,[],[f161,f193])).
% 0.21/0.54  fof(f161,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(k1_funct_1(sK2,X0),sK1)) ) | ~spl7_12),
% 0.21/0.54    inference(avatar_component_clause,[],[f160])).
% 0.21/0.54  fof(f235,plain,(
% 0.21/0.54    spl7_18 | ~spl7_8 | ~spl7_15),
% 0.21/0.54    inference(avatar_split_clause,[],[f221,f191,f133,f232])).
% 0.21/0.54  fof(f133,plain,(
% 0.21/0.54    spl7_8 <=> v1_relat_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.54  fof(f221,plain,(
% 0.21/0.54    v1_relat_1(k1_xboole_0) | (~spl7_8 | ~spl7_15)),
% 0.21/0.54    inference(backward_demodulation,[],[f135,f193])).
% 0.21/0.54  fof(f135,plain,(
% 0.21/0.54    v1_relat_1(sK2) | ~spl7_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f133])).
% 0.21/0.54  fof(f230,plain,(
% 0.21/0.54    spl7_17 | ~spl7_1 | ~spl7_15),
% 0.21/0.54    inference(avatar_split_clause,[],[f216,f191,f90,f227])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    spl7_1 <=> v1_funct_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.54  fof(f216,plain,(
% 0.21/0.54    v1_funct_1(k1_xboole_0) | (~spl7_1 | ~spl7_15)),
% 0.21/0.54    inference(backward_demodulation,[],[f92,f193])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    v1_funct_1(sK2) | ~spl7_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f90])).
% 0.21/0.54  fof(f212,plain,(
% 0.21/0.54    ~spl7_1 | spl7_2 | spl7_3 | ~spl7_4 | ~spl7_7 | ~spl7_14),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f207])).
% 0.21/0.54  fof(f207,plain,(
% 0.21/0.54    $false | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_4 | ~spl7_7 | ~spl7_14)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f92,f97,f102,f172,f110,f126,f72])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(X3,X2),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.54    inference(flattening,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.54    inference(ennf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~spl7_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f124])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    spl7_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl7_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f108])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    spl7_4 <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.54  fof(f172,plain,(
% 0.21/0.54    r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl7_14),
% 0.21/0.54    inference(avatar_component_clause,[],[f170])).
% 0.21/0.54  fof(f170,plain,(
% 0.21/0.54    spl7_14 <=> r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | spl7_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f100])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    spl7_3 <=> r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    k1_xboole_0 != sK1 | spl7_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f95])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    spl7_2 <=> k1_xboole_0 = sK1),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.54  fof(f194,plain,(
% 0.21/0.54    spl7_15 | ~spl7_13),
% 0.21/0.54    inference(avatar_split_clause,[],[f176,f167,f191])).
% 0.21/0.54  fof(f167,plain,(
% 0.21/0.54    spl7_13 <=> ! [X0] : ~r2_hidden(X0,sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.54  fof(f176,plain,(
% 0.21/0.54    k1_xboole_0 = sK2 | ~spl7_13),
% 0.21/0.54    inference(resolution,[],[f168,f60])).
% 0.21/0.54  fof(f168,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl7_13),
% 0.21/0.54    inference(avatar_component_clause,[],[f167])).
% 0.21/0.54  fof(f173,plain,(
% 0.21/0.54    spl7_13 | spl7_14 | ~spl7_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f165,f124,f170,f167])).
% 0.21/0.54  fof(f165,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(X0,sK2)) ) | ~spl7_7),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f164])).
% 0.21/0.54  fof(f164,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(X0,sK2) | ~r2_hidden(X0,sK2)) ) | ~spl7_7),
% 0.21/0.54    inference(superposition,[],[f154,f152])).
% 0.21/0.54  fof(f152,plain,(
% 0.21/0.54    ( ! [X0] : (k1_mcart_1(X0) = sK0 | ~r2_hidden(X0,sK2)) ) | ~spl7_7),
% 0.21/0.54    inference(resolution,[],[f131,f79])).
% 0.21/0.54  % (7340)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)) | k1_mcart_1(X0) = X1) )),
% 0.21/0.54    inference(definition_unfolding,[],[f69,f74])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) | k1_mcart_1(X0) = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f17])).
% 0.21/0.54  % (7350)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  fof(f17,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).
% 0.21/0.54  fof(f131,plain,(
% 0.21/0.54    ( ! [X2] : (r2_hidden(X2,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | ~r2_hidden(X2,sK2)) ) | ~spl7_7),
% 0.21/0.54    inference(resolution,[],[f126,f63])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.54  fof(f154,plain,(
% 0.21/0.54    ( ! [X2] : (r2_hidden(k1_mcart_1(X2),k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(X2,sK2)) ) | ~spl7_7),
% 0.21/0.54    inference(resolution,[],[f131,f66])).
% 0.21/0.54  % (7323)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.54  fof(f162,plain,(
% 0.21/0.54    spl7_2 | spl7_12 | ~spl7_1 | ~spl7_4 | ~spl7_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f128,f124,f108,f90,f160,f95])).
% 0.21/0.54  fof(f128,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~v1_funct_1(sK2) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | k1_xboole_0 = sK1 | r2_hidden(k1_funct_1(sK2,X0),sK1)) ) | ~spl7_7),
% 0.21/0.54    inference(resolution,[],[f126,f72])).
% 0.21/0.54  fof(f145,plain,(
% 0.21/0.54    ~spl7_8 | spl7_9 | ~spl7_1 | ~spl7_10 | spl7_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f105,f100,f142,f90,f138,f133])).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    ~r2_hidden(k1_xboole_0,sK1) | ~v1_funct_1(sK2) | r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | spl7_3),
% 0.21/0.54    inference(superposition,[],[f102,f82])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    spl7_8 | ~spl7_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f129,f124,f133])).
% 0.21/0.54  fof(f129,plain,(
% 0.21/0.54    v1_relat_1(sK2) | ~spl7_7),
% 0.21/0.54    inference(resolution,[],[f126,f68])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.54  fof(f127,plain,(
% 0.21/0.54    spl7_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f75,f124])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.21/0.54    inference(definition_unfolding,[],[f43,f74])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.21/0.54    inference(flattening,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.21/0.54    inference(negated_conjecture,[],[f21])).
% 0.21/0.54  fof(f21,conjecture,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    spl7_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f76,f108])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.54    inference(definition_unfolding,[],[f42,f74])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    ~spl7_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f45,f100])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    ~spl7_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f44,f95])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    k1_xboole_0 != sK1),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    spl7_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f41,f90])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    v1_funct_1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (7344)------------------------------
% 0.21/0.54  % (7344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7344)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (7344)Memory used [KB]: 10874
% 0.21/0.54  % (7344)Time elapsed: 0.079 s
% 0.21/0.54  % (7344)------------------------------
% 0.21/0.54  % (7344)------------------------------
% 0.21/0.54  % (7337)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (7331)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (7347)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (7345)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (7331)Refutation not found, incomplete strategy% (7331)------------------------------
% 0.21/0.54  % (7331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7331)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (7331)Memory used [KB]: 10618
% 0.21/0.54  % (7331)Time elapsed: 0.113 s
% 0.21/0.54  % (7331)------------------------------
% 0.21/0.54  % (7331)------------------------------
% 0.21/0.54  % (7348)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (7320)Success in time 0.183 s
%------------------------------------------------------------------------------
