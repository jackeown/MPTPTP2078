%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : finset_1__t30_finset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:13 EDT 2019

% Result     : Theorem 232.58s
% Output     : Refutation 232.58s
% Verified   : 
% Statistics : Number of formulae       :  298 ( 697 expanded)
%              Number of leaves         :   50 ( 189 expanded)
%              Depth                    :   17
%              Number of atoms          : 1027 (3263 expanded)
%              Number of equality atoms :  125 ( 545 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f453313,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1109,f3143,f3588,f3954,f3971,f7601,f11711,f12295,f18165,f31291,f36469,f168691,f168692,f189336,f189341,f190338,f191923,f196305,f196316,f196597,f196603,f214221,f214222,f244152,f249533,f249558,f250727,f453312])).

fof(f453312,plain,
    ( spl11_31
    | ~ spl11_126
    | ~ spl11_216
    | ~ spl11_342
    | spl11_447
    | spl11_1003 ),
    inference(avatar_contradiction_clause,[],[f453311])).

fof(f453311,plain,
    ( $false
    | ~ spl11_31
    | ~ spl11_126
    | ~ spl11_216
    | ~ spl11_342
    | ~ spl11_447
    | ~ spl11_1003 ),
    inference(subsumption_resolution,[],[f453310,f258367])).

fof(f258367,plain,
    ( r2_hidden(sK6(sK0),sK0)
    | ~ spl11_31
    | ~ spl11_216
    | ~ spl11_342 ),
    inference(resolution,[],[f252332,f7600])).

fof(f7600,plain,
    ( r2_hidden(sK6(sK0),sK3(sK0))
    | ~ spl11_342 ),
    inference(avatar_component_clause,[],[f7599])).

fof(f7599,plain,
    ( spl11_342
  <=> r2_hidden(sK6(sK0),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_342])])).

fof(f252332,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3(sK0))
        | r2_hidden(X0,sK0) )
    | ~ spl11_31
    | ~ spl11_216 ),
    inference(subsumption_resolution,[],[f252329,f985])).

fof(f985,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl11_31 ),
    inference(avatar_component_clause,[],[f984])).

fof(f984,plain,
    ( spl11_31
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).

fof(f252329,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3(sK0))
        | v1_xboole_0(sK0)
        | r2_hidden(X0,sK0) )
    | ~ spl11_216 ),
    inference(resolution,[],[f3953,f412])).

fof(f412,plain,(
    ! [X8,X7,X9] :
      ( ~ r1_tarski(X8,X9)
      | ~ r2_hidden(X7,X8)
      | v1_xboole_0(X9)
      | r2_hidden(X7,X9) ) ),
    inference(resolution,[],[f404,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/finset_1__t30_finset_1.p',t2_subset)).

fof(f404,plain,(
    ! [X4,X2,X3] :
      ( m1_subset_1(X2,X4)
      | ~ r2_hidden(X2,X3)
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f123,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/finset_1__t30_finset_1.p',t3_subset)).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/finset_1__t30_finset_1.p',t4_subset)).

fof(f3953,plain,
    ( r1_tarski(sK3(sK0),sK0)
    | ~ spl11_216 ),
    inference(avatar_component_clause,[],[f3952])).

fof(f3952,plain,
    ( spl11_216
  <=> r1_tarski(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_216])])).

fof(f453310,plain,
    ( ~ r2_hidden(sK6(sK0),sK0)
    | ~ spl11_126
    | ~ spl11_447
    | ~ spl11_1003 ),
    inference(subsumption_resolution,[],[f453308,f9778])).

fof(f9778,plain,
    ( ~ r1_tarski(sK2(sK0),sK6(sK0))
    | ~ spl11_447 ),
    inference(avatar_component_clause,[],[f9777])).

fof(f9777,plain,
    ( spl11_447
  <=> ~ r1_tarski(sK2(sK0),sK6(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_447])])).

fof(f453308,plain,
    ( r1_tarski(sK2(sK0),sK6(sK0))
    | ~ r2_hidden(sK6(sK0),sK0)
    | ~ spl11_126
    | ~ spl11_1003 ),
    inference(resolution,[],[f3657,f31694])).

fof(f31694,plain,
    ( ~ r1_tarski(sK6(sK0),sK2(sK0))
    | ~ spl11_1003 ),
    inference(avatar_component_clause,[],[f31693])).

fof(f31693,plain,
    ( spl11_1003
  <=> ~ r1_tarski(sK6(sK0),sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1003])])).

fof(f3657,plain,
    ( ! [X0] :
        ( r1_tarski(sK2(sK0),X0)
        | r1_tarski(X0,sK2(sK0))
        | ~ r2_hidden(X0,sK0) )
    | ~ spl11_126 ),
    inference(resolution,[],[f3596,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r3_xboole_0(X0,X1)
      | r1_tarski(X1,X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/finset_1__t30_finset_1.p',d9_xboole_0)).

fof(f3596,plain,
    ( ! [X2] :
        ( r3_xboole_0(X2,sK2(sK0))
        | ~ r2_hidden(X2,sK0) )
    | ~ spl11_126 ),
    inference(resolution,[],[f2415,f795])).

fof(f795,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X0,sK0)
      | r3_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f102,f56])).

fof(f56,plain,(
    v6_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,X2)
              & r2_hidden(X2,X0) )
          | ~ r2_hidden(X1,X0) )
      & v6_ordinal1(X0)
      & k1_xboole_0 != X0
      & v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ~ ( ! [X2] :
                    ( r2_hidden(X2,X0)
                   => r1_tarski(X1,X2) )
                & r2_hidden(X1,X0) )
          & v6_ordinal1(X0)
          & k1_xboole_0 != X0
          & v1_finset_1(X0) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2] :
                  ( r2_hidden(X2,X0)
                 => r1_tarski(X1,X2) )
              & r2_hidden(X1,X0) )
        & v6_ordinal1(X0)
        & k1_xboole_0 != X0
        & v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/finset_1__t30_finset_1.p',t30_finset_1)).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_ordinal1(X0)
      | ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X2,X0)
      | r3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r3_xboole_0(X1,X2)
          | ~ r2_hidden(X2,X0)
          | ~ r2_hidden(X1,X0) )
      | ~ v6_ordinal1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r3_xboole_0(X1,X2)
          | ~ r2_hidden(X2,X0)
          | ~ r2_hidden(X1,X0) )
      | ~ v6_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v6_ordinal1(X0)
     => ! [X1,X2] :
          ( ( r2_hidden(X2,X0)
            & r2_hidden(X1,X0) )
         => r3_xboole_0(X1,X2) ) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v6_ordinal1(X0)
    <=> ! [X1,X2] :
          ( ( r2_hidden(X2,X0)
            & r2_hidden(X1,X0) )
         => r3_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/finset_1__t30_finset_1.p',d9_ordinal1)).

fof(f2415,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ spl11_126 ),
    inference(avatar_component_clause,[],[f2414])).

fof(f2414,plain,
    ( spl11_126
  <=> r2_hidden(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_126])])).

fof(f250727,plain,
    ( ~ spl11_498
    | spl11_523
    | ~ spl11_524
    | ~ spl11_1002
    | ~ spl11_1796 ),
    inference(avatar_contradiction_clause,[],[f250726])).

fof(f250726,plain,
    ( $false
    | ~ spl11_498
    | ~ spl11_523
    | ~ spl11_524
    | ~ spl11_1002
    | ~ spl11_1796 ),
    inference(subsumption_resolution,[],[f250725,f12261])).

fof(f12261,plain,
    ( r2_hidden(sK6(sK0),k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0))))
    | ~ spl11_524 ),
    inference(avatar_component_clause,[],[f12260])).

fof(f12260,plain,
    ( spl11_524
  <=> r2_hidden(sK6(sK0),k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_524])])).

fof(f250725,plain,
    ( ~ r2_hidden(sK6(sK0),k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0))))
    | ~ spl11_498
    | ~ spl11_523
    | ~ spl11_524
    | ~ spl11_1002
    | ~ spl11_1796 ),
    inference(subsumption_resolution,[],[f249859,f31697])).

fof(f31697,plain,
    ( r1_tarski(sK6(sK0),sK2(sK0))
    | ~ spl11_1002 ),
    inference(avatar_component_clause,[],[f31696])).

fof(f31696,plain,
    ( spl11_1002
  <=> r1_tarski(sK6(sK0),sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1002])])).

fof(f249859,plain,
    ( ~ r1_tarski(sK6(sK0),sK2(sK0))
    | ~ r2_hidden(sK6(sK0),k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0))))
    | ~ spl11_498
    | ~ spl11_523
    | ~ spl11_524
    | ~ spl11_1796 ),
    inference(superposition,[],[f168690,f168071])).

fof(f168071,plain,
    ( sK2(sK0) = sK7(sK0,sK6(sK0))
    | ~ spl11_498
    | ~ spl11_523
    | ~ spl11_524 ),
    inference(resolution,[],[f167732,f131])).

fof(f131,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/finset_1__t30_finset_1.p',d1_tarski)).

fof(f167732,plain,
    ( r2_hidden(sK7(sK0,sK6(sK0)),k1_tarski(sK2(sK0)))
    | ~ spl11_498
    | ~ spl11_523
    | ~ spl11_524 ),
    inference(subsumption_resolution,[],[f167626,f12258])).

fof(f12258,plain,
    ( ~ r2_hidden(sK7(sK0,sK6(sK0)),sK3(sK0))
    | ~ spl11_523 ),
    inference(avatar_component_clause,[],[f12257])).

fof(f12257,plain,
    ( spl11_523
  <=> ~ r2_hidden(sK7(sK0,sK6(sK0)),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_523])])).

fof(f167626,plain,
    ( r2_hidden(sK7(sK0,sK6(sK0)),k1_tarski(sK2(sK0)))
    | r2_hidden(sK7(sK0,sK6(sK0)),sK3(sK0))
    | ~ spl11_498
    | ~ spl11_524 ),
    inference(resolution,[],[f33252,f12261])).

fof(f33252,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0))))
        | r2_hidden(sK7(sK0,X0),k1_tarski(sK2(sK0)))
        | r2_hidden(sK7(sK0,X0),sK3(sK0)) )
    | ~ spl11_498 ),
    inference(resolution,[],[f11710,f136])).

fof(f136,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f127])).

fof(f127,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/finset_1__t30_finset_1.p',d3_xboole_0)).

fof(f11710,plain,
    ( ! [X0] :
        ( r2_hidden(sK7(sK0,X0),k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0))))
        | ~ r2_hidden(X0,k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0)))) )
    | ~ spl11_498 ),
    inference(avatar_component_clause,[],[f11709])).

fof(f11709,plain,
    ( spl11_498
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0))))
        | r2_hidden(sK7(sK0,X0),k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_498])])).

fof(f168690,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK7(sK0,X0))
        | ~ r2_hidden(X0,k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0)))) )
    | ~ spl11_1796 ),
    inference(avatar_component_clause,[],[f168689])).

fof(f168689,plain,
    ( spl11_1796
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0))))
        | ~ r1_tarski(X0,sK7(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1796])])).

fof(f249558,plain,
    ( ~ spl11_298
    | ~ spl11_522
    | ~ spl11_524
    | ~ spl11_1796 ),
    inference(avatar_contradiction_clause,[],[f249557])).

fof(f249557,plain,
    ( $false
    | ~ spl11_298
    | ~ spl11_522
    | ~ spl11_524
    | ~ spl11_1796 ),
    inference(subsumption_resolution,[],[f12255,f241089])).

fof(f241089,plain,
    ( ~ r2_hidden(sK7(sK0,sK6(sK0)),sK3(sK0))
    | ~ spl11_298
    | ~ spl11_524
    | ~ spl11_1796 ),
    inference(subsumption_resolution,[],[f241086,f12261])).

fof(f241086,plain,
    ( ~ r2_hidden(sK6(sK0),k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0))))
    | ~ r2_hidden(sK7(sK0,sK6(sK0)),sK3(sK0))
    | ~ spl11_298
    | ~ spl11_1796 ),
    inference(resolution,[],[f168690,f7045])).

fof(f7045,plain,
    ( ! [X0] :
        ( r1_tarski(sK6(sK0),X0)
        | ~ r2_hidden(X0,sK3(sK0)) )
    | ~ spl11_298 ),
    inference(avatar_component_clause,[],[f7044])).

fof(f7044,plain,
    ( spl11_298
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK3(sK0))
        | r1_tarski(sK6(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_298])])).

fof(f12255,plain,
    ( r2_hidden(sK7(sK0,sK6(sK0)),sK3(sK0))
    | ~ spl11_522 ),
    inference(avatar_component_clause,[],[f12254])).

fof(f12254,plain,
    ( spl11_522
  <=> r2_hidden(sK7(sK0,sK6(sK0)),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_522])])).

fof(f249533,plain,
    ( ~ spl11_298
    | ~ spl11_446
    | ~ spl11_512
    | ~ spl11_514
    | ~ spl11_1796 ),
    inference(avatar_contradiction_clause,[],[f249532])).

fof(f249532,plain,
    ( $false
    | ~ spl11_298
    | ~ spl11_446
    | ~ spl11_512
    | ~ spl11_514
    | ~ spl11_1796 ),
    inference(subsumption_resolution,[],[f12222,f249517])).

fof(f249517,plain,
    ( ~ r2_hidden(sK7(sK0,sK2(sK0)),sK3(sK0))
    | ~ spl11_298
    | ~ spl11_446
    | ~ spl11_514
    | ~ spl11_1796 ),
    inference(subsumption_resolution,[],[f249508,f12228])).

fof(f12228,plain,
    ( r2_hidden(sK2(sK0),k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0))))
    | ~ spl11_514 ),
    inference(avatar_component_clause,[],[f12227])).

fof(f12227,plain,
    ( spl11_514
  <=> r2_hidden(sK2(sK0),k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_514])])).

fof(f249508,plain,
    ( ~ r2_hidden(sK7(sK0,sK2(sK0)),sK3(sK0))
    | ~ r2_hidden(sK2(sK0),k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0))))
    | ~ spl11_298
    | ~ spl11_446
    | ~ spl11_1796 ),
    inference(resolution,[],[f209421,f168690])).

fof(f209421,plain,
    ( ! [X14] :
        ( r1_tarski(sK2(sK0),X14)
        | ~ r2_hidden(X14,sK3(sK0)) )
    | ~ spl11_298
    | ~ spl11_446 ),
    inference(resolution,[],[f205161,f9781])).

fof(f9781,plain,
    ( r1_tarski(sK2(sK0),sK6(sK0))
    | ~ spl11_446 ),
    inference(avatar_component_clause,[],[f9780])).

fof(f9780,plain,
    ( spl11_446
  <=> r1_tarski(sK2(sK0),sK6(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_446])])).

fof(f205161,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(X4,sK6(sK0))
        | ~ r2_hidden(X3,sK3(sK0))
        | r1_tarski(X4,X3) )
    | ~ spl11_298 ),
    inference(resolution,[],[f7045,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/finset_1__t30_finset_1.p',t1_xboole_1)).

fof(f12222,plain,
    ( r2_hidden(sK7(sK0,sK2(sK0)),sK3(sK0))
    | ~ spl11_512 ),
    inference(avatar_component_clause,[],[f12221])).

fof(f12221,plain,
    ( spl11_512
  <=> r2_hidden(sK7(sK0,sK2(sK0)),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_512])])).

fof(f244152,plain,
    ( spl11_179
    | spl11_523
    | ~ spl11_524
    | ~ spl11_1002
    | ~ spl11_1796 ),
    inference(avatar_contradiction_clause,[],[f244151])).

fof(f244151,plain,
    ( $false
    | ~ spl11_179
    | ~ spl11_523
    | ~ spl11_524
    | ~ spl11_1002
    | ~ spl11_1796 ),
    inference(subsumption_resolution,[],[f31697,f212944])).

fof(f212944,plain,
    ( ~ r1_tarski(sK6(sK0),sK2(sK0))
    | ~ spl11_179
    | ~ spl11_523
    | ~ spl11_524
    | ~ spl11_1796 ),
    inference(subsumption_resolution,[],[f212941,f12261])).

fof(f212941,plain,
    ( ~ r1_tarski(sK6(sK0),sK2(sK0))
    | ~ r2_hidden(sK6(sK0),k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0))))
    | ~ spl11_179
    | ~ spl11_523
    | ~ spl11_524
    | ~ spl11_1796 ),
    inference(superposition,[],[f168690,f212884])).

fof(f212884,plain,
    ( sK2(sK0) = sK7(sK0,sK6(sK0))
    | ~ spl11_179
    | ~ spl11_523
    | ~ spl11_524 ),
    inference(resolution,[],[f212872,f131])).

fof(f212872,plain,
    ( r2_hidden(sK7(sK0,sK6(sK0)),k1_tarski(sK2(sK0)))
    | ~ spl11_179
    | ~ spl11_523
    | ~ spl11_524 ),
    inference(subsumption_resolution,[],[f212831,f12258])).

fof(f212831,plain,
    ( r2_hidden(sK7(sK0,sK6(sK0)),k1_tarski(sK2(sK0)))
    | r2_hidden(sK7(sK0,sK6(sK0)),sK3(sK0))
    | ~ spl11_179
    | ~ spl11_524 ),
    inference(resolution,[],[f196314,f12261])).

fof(f196314,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0))))
        | r2_hidden(sK7(sK0,X0),k1_tarski(sK2(sK0)))
        | r2_hidden(sK7(sK0,X0),sK3(sK0)) )
    | ~ spl11_179 ),
    inference(subsumption_resolution,[],[f191915,f3131])).

fof(f3131,plain,
    ( ~ r2_hidden(sK4(sK0),sK0)
    | ~ spl11_179 ),
    inference(avatar_component_clause,[],[f3130])).

fof(f3130,plain,
    ( spl11_179
  <=> ~ r2_hidden(sK4(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_179])])).

fof(f191915,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0))))
      | r2_hidden(sK4(sK0),sK0)
      | r2_hidden(sK7(sK0,X0),k1_tarski(sK2(sK0)))
      | r2_hidden(sK7(sK0,X0),sK3(sK0)) ) ),
    inference(subsumption_resolution,[],[f41006,f55])).

fof(f55,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f34])).

fof(f41006,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0))))
      | k1_xboole_0 = sK0
      | r2_hidden(sK4(sK0),sK0)
      | r2_hidden(sK7(sK0,X0),k1_tarski(sK2(sK0)))
      | r2_hidden(sK7(sK0,X0),sK3(sK0)) ) ),
    inference(resolution,[],[f11482,f54])).

fof(f54,plain,(
    v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f11482,plain,(
    ! [X0,X1] :
      ( ~ v1_finset_1(X1)
      | ~ r2_hidden(X0,k2_xboole_0(sK3(X1),k1_tarski(sK2(X1))))
      | k1_xboole_0 = X1
      | r2_hidden(sK4(X1),X1)
      | r2_hidden(sK7(X1,X0),k1_tarski(sK2(X1)))
      | r2_hidden(sK7(X1,X0),sK3(X1)) ) ),
    inference(resolution,[],[f139,f136])).

fof(f139,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK7(X0,X5),k2_xboole_0(sK3(X0),k1_tarski(sK2(X0))))
      | ~ r2_hidden(X5,k2_xboole_0(sK3(X0),k1_tarski(sK2(X0))))
      | ~ v1_finset_1(X0)
      | k1_xboole_0 = X0
      | r2_hidden(sK4(X0),X0) ) ),
    inference(trivial_inequality_removal,[],[f66])).

fof(f66,plain,(
    ! [X0,X5] :
      ( ~ v1_finset_1(X0)
      | k1_xboole_0 != k1_xboole_0
      | ~ r2_hidden(X5,k2_xboole_0(sK3(X0),k1_tarski(sK2(X0))))
      | r2_hidden(sK7(X0,X5),k2_xboole_0(sK3(X0),k1_tarski(sK2(X0))))
      | k1_xboole_0 = X0
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X9] :
          ( ! [X10] :
              ( r1_tarski(X9,X10)
              | ~ r2_hidden(X10,X0) )
          & r2_hidden(X9,X0) )
      | k1_xboole_0 = X0
      | ? [X1,X2] :
          ( ! [X5] :
              ( ? [X6] :
                  ( ~ r1_tarski(X5,X6)
                  & r2_hidden(X6,k2_xboole_0(X2,k1_tarski(X1))) )
              | ~ r2_hidden(X5,k2_xboole_0(X2,k1_tarski(X1))) )
          & k1_xboole_0 != k2_xboole_0(X2,k1_tarski(X1))
          & ( ? [X3] :
                ( ! [X4] :
                    ( r1_tarski(X3,X4)
                    | ~ r2_hidden(X4,X2) )
                & r2_hidden(X3,X2) )
            | k1_xboole_0 = X2 )
          & r1_tarski(X2,X0)
          & r2_hidden(X1,X0) )
      | ( ! [X7] :
            ( ? [X8] :
                ( ~ r1_tarski(X7,X8)
                & r2_hidden(X8,k1_xboole_0) )
            | ~ r2_hidden(X7,k1_xboole_0) )
        & k1_xboole_0 != k1_xboole_0 )
      | ~ v1_finset_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X9] :
          ( ! [X10] :
              ( r1_tarski(X9,X10)
              | ~ r2_hidden(X10,X0) )
          & r2_hidden(X9,X0) )
      | k1_xboole_0 = X0
      | ? [X1,X2] :
          ( ! [X5] :
              ( ? [X6] :
                  ( ~ r1_tarski(X5,X6)
                  & r2_hidden(X6,k2_xboole_0(X2,k1_tarski(X1))) )
              | ~ r2_hidden(X5,k2_xboole_0(X2,k1_tarski(X1))) )
          & k1_xboole_0 != k2_xboole_0(X2,k1_tarski(X1))
          & ( ? [X3] :
                ( ! [X4] :
                    ( r1_tarski(X3,X4)
                    | ~ r2_hidden(X4,X2) )
                & r2_hidden(X3,X2) )
            | k1_xboole_0 = X2 )
          & r1_tarski(X2,X0)
          & r2_hidden(X1,X0) )
      | ( ! [X7] :
            ( ? [X8] :
                ( ~ r1_tarski(X7,X8)
                & r2_hidden(X8,k1_xboole_0) )
            | ~ r2_hidden(X7,k1_xboole_0) )
        & k1_xboole_0 != k1_xboole_0 )
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( ! [X1,X2] :
            ( ( ~ ( ! [X3] :
                      ~ ( ! [X4] :
                            ( r2_hidden(X4,X2)
                           => r1_tarski(X3,X4) )
                        & r2_hidden(X3,X2) )
                  & k1_xboole_0 != X2 )
              & r1_tarski(X2,X0)
              & r2_hidden(X1,X0) )
           => ~ ( ! [X5] :
                    ~ ( ! [X6] :
                          ( r2_hidden(X6,k2_xboole_0(X2,k1_tarski(X1)))
                         => r1_tarski(X5,X6) )
                      & r2_hidden(X5,k2_xboole_0(X2,k1_tarski(X1))) )
                & k1_xboole_0 != k2_xboole_0(X2,k1_tarski(X1)) ) )
        & ~ ( ! [X7] :
                ~ ( ! [X8] :
                      ( r2_hidden(X8,k1_xboole_0)
                     => r1_tarski(X7,X8) )
                  & r2_hidden(X7,k1_xboole_0) )
            & k1_xboole_0 != k1_xboole_0 )
        & v1_finset_1(X0) )
     => ~ ( ! [X9] :
              ~ ( ! [X10] :
                    ( r2_hidden(X10,X0)
                   => r1_tarski(X9,X10) )
                & r2_hidden(X9,X0) )
          & k1_xboole_0 != X0 ) ) ),
    inference(rectify,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( ! [X3,X4] :
            ( ( ~ ( ! [X5] :
                      ~ ( ! [X6] :
                            ( r2_hidden(X6,X4)
                           => r1_tarski(X5,X6) )
                        & r2_hidden(X5,X4) )
                  & k1_xboole_0 != X4 )
              & r1_tarski(X4,X0)
              & r2_hidden(X3,X0) )
           => ~ ( ! [X7] :
                    ~ ( ! [X8] :
                          ( r2_hidden(X8,k2_xboole_0(X4,k1_tarski(X3)))
                         => r1_tarski(X7,X8) )
                      & r2_hidden(X7,k2_xboole_0(X4,k1_tarski(X3))) )
                & k1_xboole_0 != k2_xboole_0(X4,k1_tarski(X3)) ) )
        & ~ ( ! [X1] :
                ~ ( ! [X2] :
                      ( r2_hidden(X2,k1_xboole_0)
                     => r1_tarski(X1,X2) )
                  & r2_hidden(X1,k1_xboole_0) )
            & k1_xboole_0 != k1_xboole_0 )
        & v1_finset_1(X0) )
     => ~ ( ! [X9] :
              ~ ( ! [X10] :
                    ( r2_hidden(X10,X0)
                   => r1_tarski(X9,X10) )
                & r2_hidden(X9,X0) )
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/finset_1__t30_finset_1.p',s2_finset_1__e6_53__finset_1)).

fof(f214222,plain,
    ( spl11_512
    | spl11_1792
    | spl11_179
    | ~ spl11_514 ),
    inference(avatar_split_clause,[],[f214143,f12227,f3130,f168107,f12221])).

fof(f168107,plain,
    ( spl11_1792
  <=> r2_hidden(sK7(sK0,sK2(sK0)),k1_tarski(sK2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1792])])).

fof(f214143,plain,
    ( r2_hidden(sK7(sK0,sK2(sK0)),k1_tarski(sK2(sK0)))
    | r2_hidden(sK7(sK0,sK2(sK0)),sK3(sK0))
    | ~ spl11_179
    | ~ spl11_514 ),
    inference(resolution,[],[f12228,f196314])).

fof(f214221,plain,
    ( ~ spl11_514
    | ~ spl11_1792
    | ~ spl11_1796 ),
    inference(avatar_contradiction_clause,[],[f214220])).

fof(f214220,plain,
    ( $false
    | ~ spl11_514
    | ~ spl11_1792
    | ~ spl11_1796 ),
    inference(subsumption_resolution,[],[f214219,f12228])).

fof(f214219,plain,
    ( ~ r2_hidden(sK2(sK0),k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0))))
    | ~ spl11_1792
    | ~ spl11_1796 ),
    inference(subsumption_resolution,[],[f214216,f311])).

fof(f311,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f308])).

fof(f308,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f111,f104])).

fof(f104,plain,(
    ! [X0] : r3_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] : r3_xboole_0(X0,X0) ),
    inference(rectify,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : r3_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/finset_1__t30_finset_1.p',reflexivity_r3_xboole_0)).

fof(f214216,plain,
    ( ~ r1_tarski(sK2(sK0),sK2(sK0))
    | ~ r2_hidden(sK2(sK0),k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0))))
    | ~ spl11_1792
    | ~ spl11_1796 ),
    inference(superposition,[],[f168690,f196226])).

fof(f196226,plain,
    ( sK2(sK0) = sK7(sK0,sK2(sK0))
    | ~ spl11_1792 ),
    inference(resolution,[],[f168108,f131])).

fof(f168108,plain,
    ( r2_hidden(sK7(sK0,sK2(sK0)),k1_tarski(sK2(sK0)))
    | ~ spl11_1792 ),
    inference(avatar_component_clause,[],[f168107])).

fof(f196603,plain,
    ( spl11_179
    | spl11_225
    | spl11_343 ),
    inference(avatar_contradiction_clause,[],[f196602])).

fof(f196602,plain,
    ( $false
    | ~ spl11_179
    | ~ spl11_225
    | ~ spl11_343 ),
    inference(subsumption_resolution,[],[f196601,f3131])).

fof(f196601,plain,
    ( r2_hidden(sK4(sK0),sK0)
    | ~ spl11_225
    | ~ spl11_343 ),
    inference(subsumption_resolution,[],[f196600,f55])).

fof(f196600,plain,
    ( k1_xboole_0 = sK0
    | r2_hidden(sK4(sK0),sK0)
    | ~ spl11_225
    | ~ spl11_343 ),
    inference(subsumption_resolution,[],[f196599,f54])).

fof(f196599,plain,
    ( ~ v1_finset_1(sK0)
    | k1_xboole_0 = sK0
    | r2_hidden(sK4(sK0),sK0)
    | ~ spl11_225
    | ~ spl11_343 ),
    inference(subsumption_resolution,[],[f196598,f4067])).

fof(f4067,plain,
    ( k1_xboole_0 != sK3(sK0)
    | ~ spl11_225 ),
    inference(avatar_component_clause,[],[f4066])).

fof(f4066,plain,
    ( spl11_225
  <=> k1_xboole_0 != sK3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_225])])).

fof(f196598,plain,
    ( k1_xboole_0 = sK3(sK0)
    | ~ v1_finset_1(sK0)
    | k1_xboole_0 = sK0
    | r2_hidden(sK4(sK0),sK0)
    | ~ spl11_343 ),
    inference(resolution,[],[f7597,f143])).

fof(f143,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),sK3(X0))
      | k1_xboole_0 = sK3(X0)
      | ~ v1_finset_1(X0)
      | k1_xboole_0 = X0
      | r2_hidden(sK4(X0),X0) ) ),
    inference(trivial_inequality_removal,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_finset_1(X0)
      | k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = sK3(X0)
      | r2_hidden(sK6(X0),sK3(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7597,plain,
    ( ~ r2_hidden(sK6(sK0),sK3(sK0))
    | ~ spl11_343 ),
    inference(avatar_component_clause,[],[f7596])).

fof(f7596,plain,
    ( spl11_343
  <=> ~ r2_hidden(sK6(sK0),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_343])])).

fof(f196597,plain,
    ( spl11_179
    | spl11_225
    | spl11_525 ),
    inference(avatar_contradiction_clause,[],[f196596])).

fof(f196596,plain,
    ( $false
    | ~ spl11_179
    | ~ spl11_225
    | ~ spl11_525 ),
    inference(subsumption_resolution,[],[f196595,f3131])).

fof(f196595,plain,
    ( r2_hidden(sK4(sK0),sK0)
    | ~ spl11_225
    | ~ spl11_525 ),
    inference(subsumption_resolution,[],[f196594,f55])).

fof(f196594,plain,
    ( k1_xboole_0 = sK0
    | r2_hidden(sK4(sK0),sK0)
    | ~ spl11_225
    | ~ spl11_525 ),
    inference(subsumption_resolution,[],[f196593,f54])).

fof(f196593,plain,
    ( ~ v1_finset_1(sK0)
    | k1_xboole_0 = sK0
    | r2_hidden(sK4(sK0),sK0)
    | ~ spl11_225
    | ~ spl11_525 ),
    inference(subsumption_resolution,[],[f196592,f4067])).

fof(f196592,plain,
    ( k1_xboole_0 = sK3(sK0)
    | ~ v1_finset_1(sK0)
    | k1_xboole_0 = sK0
    | r2_hidden(sK4(sK0),sK0)
    | ~ spl11_525 ),
    inference(resolution,[],[f12292,f143])).

fof(f12292,plain,
    ( ~ r2_hidden(sK6(sK0),sK3(sK0))
    | ~ spl11_525 ),
    inference(resolution,[],[f12264,f135])).

fof(f135,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f128])).

fof(f128,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f12264,plain,
    ( ~ r2_hidden(sK6(sK0),k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0))))
    | ~ spl11_525 ),
    inference(avatar_component_clause,[],[f12263])).

fof(f12263,plain,
    ( spl11_525
  <=> ~ r2_hidden(sK6(sK0),k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_525])])).

fof(f196316,plain,
    ( spl11_298
    | spl11_224
    | spl11_179 ),
    inference(avatar_split_clause,[],[f196315,f3130,f4069,f7044])).

fof(f4069,plain,
    ( spl11_224
  <=> k1_xboole_0 = sK3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_224])])).

fof(f196315,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK3(sK0)
        | ~ r2_hidden(X0,sK3(sK0))
        | r1_tarski(sK6(sK0),X0) )
    | ~ spl11_179 ),
    inference(subsumption_resolution,[],[f7041,f3131])).

fof(f7041,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK3(sK0)
      | ~ r2_hidden(X0,sK3(sK0))
      | r1_tarski(sK6(sK0),X0)
      | r2_hidden(sK4(sK0),sK0) ) ),
    inference(subsumption_resolution,[],[f7040,f55])).

fof(f7040,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK3(sK0)
      | ~ r2_hidden(X0,sK3(sK0))
      | r1_tarski(sK6(sK0),X0)
      | k1_xboole_0 = sK0
      | r2_hidden(sK4(sK0),sK0) ) ),
    inference(resolution,[],[f138,f54])).

fof(f138,plain,(
    ! [X4,X0] :
      ( ~ v1_finset_1(X0)
      | k1_xboole_0 = sK3(X0)
      | ~ r2_hidden(X4,sK3(X0))
      | r1_tarski(sK6(X0),X4)
      | k1_xboole_0 = X0
      | r2_hidden(sK4(X0),X0) ) ),
    inference(trivial_inequality_removal,[],[f65])).

fof(f65,plain,(
    ! [X4,X0] :
      ( ~ v1_finset_1(X0)
      | k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = sK3(X0)
      | ~ r2_hidden(X4,sK3(X0))
      | r1_tarski(sK6(X0),X4)
      | k1_xboole_0 = X0
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f196305,plain,
    ( spl11_1793
    | ~ spl11_1836 ),
    inference(avatar_contradiction_clause,[],[f196304])).

fof(f196304,plain,
    ( $false
    | ~ spl11_1793
    | ~ spl11_1836 ),
    inference(subsumption_resolution,[],[f196303,f133])).

fof(f133,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f132])).

fof(f132,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f196303,plain,
    ( ~ r2_hidden(sK2(sK0),k1_tarski(sK2(sK0)))
    | ~ spl11_1793
    | ~ spl11_1836 ),
    inference(resolution,[],[f168105,f191922])).

fof(f191922,plain,
    ( ! [X0] :
        ( r2_hidden(sK7(sK0,X0),k1_tarski(sK2(sK0)))
        | ~ r2_hidden(X0,k1_tarski(sK2(sK0))) )
    | ~ spl11_1836 ),
    inference(avatar_component_clause,[],[f191921])).

fof(f191921,plain,
    ( spl11_1836
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(sK2(sK0)))
        | r2_hidden(sK7(sK0,X0),k1_tarski(sK2(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1836])])).

fof(f168105,plain,
    ( ~ r2_hidden(sK7(sK0,sK2(sK0)),k1_tarski(sK2(sK0)))
    | ~ spl11_1793 ),
    inference(avatar_component_clause,[],[f168104])).

fof(f168104,plain,
    ( spl11_1793
  <=> ~ r2_hidden(sK7(sK0,sK2(sK0)),k1_tarski(sK2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1793])])).

fof(f191923,plain,
    ( spl11_178
    | spl11_1836
    | spl11_479 ),
    inference(avatar_split_clause,[],[f191919,f10272,f191921,f3127])).

fof(f3127,plain,
    ( spl11_178
  <=> r2_hidden(sK4(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_178])])).

fof(f10272,plain,
    ( spl11_479
  <=> ~ r2_hidden(sK8(sK3(sK0)),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_479])])).

fof(f191919,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(sK2(sK0)))
        | r2_hidden(sK4(sK0),sK0)
        | r2_hidden(sK7(sK0,X0),k1_tarski(sK2(sK0))) )
    | ~ spl11_479 ),
    inference(subsumption_resolution,[],[f191918,f191])).

fof(f191,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f121,f189])).

fof(f189,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f188,f57])).

fof(f57,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/finset_1__t30_finset_1.p',dt_o_0_0_xboole_0)).

fof(f188,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(resolution,[],[f59,f57])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/finset_1__t30_finset_1.p',t6_boole)).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/finset_1__t30_finset_1.p',t7_boole)).

fof(f191918,plain,
    ( ! [X0] :
        ( r2_hidden(sK7(sK0,X0),k1_xboole_0)
        | ~ r2_hidden(X0,k1_tarski(sK2(sK0)))
        | r2_hidden(sK4(sK0),sK0)
        | r2_hidden(sK7(sK0,X0),k1_tarski(sK2(sK0))) )
    | ~ spl11_479 ),
    inference(forward_demodulation,[],[f191917,f10358])).

fof(f10358,plain,
    ( k1_xboole_0 = sK3(sK0)
    | ~ spl11_479 ),
    inference(resolution,[],[f10354,f59])).

fof(f10354,plain,
    ( v1_xboole_0(sK3(sK0))
    | ~ spl11_479 ),
    inference(resolution,[],[f10273,f210])).

fof(f210,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f108,f103])).

fof(f103,plain,(
    ! [X0] : m1_subset_1(sK8(X0),X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/finset_1__t30_finset_1.p',existence_m1_subset_1)).

fof(f10273,plain,
    ( ~ r2_hidden(sK8(sK3(sK0)),sK3(sK0))
    | ~ spl11_479 ),
    inference(avatar_component_clause,[],[f10272])).

fof(f191917,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(sK2(sK0)))
        | r2_hidden(sK4(sK0),sK0)
        | r2_hidden(sK7(sK0,X0),k1_tarski(sK2(sK0)))
        | r2_hidden(sK7(sK0,X0),sK3(sK0)) )
    | ~ spl11_479 ),
    inference(forward_demodulation,[],[f191916,f197])).

fof(f197,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f106,f58])).

fof(f58,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/finset_1__t30_finset_1.p',t1_boole)).

fof(f106,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/finset_1__t30_finset_1.p',commutativity_k2_xboole_0)).

fof(f191916,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_xboole_0(k1_xboole_0,k1_tarski(sK2(sK0))))
        | r2_hidden(sK4(sK0),sK0)
        | r2_hidden(sK7(sK0,X0),k1_tarski(sK2(sK0)))
        | r2_hidden(sK7(sK0,X0),sK3(sK0)) )
    | ~ spl11_479 ),
    inference(forward_demodulation,[],[f191915,f10358])).

fof(f190338,plain,
    ( spl11_479
    | ~ spl11_512 ),
    inference(avatar_contradiction_clause,[],[f190337])).

fof(f190337,plain,
    ( $false
    | ~ spl11_479
    | ~ spl11_512 ),
    inference(subsumption_resolution,[],[f189419,f191])).

fof(f189419,plain,
    ( r2_hidden(sK7(sK0,sK2(sK0)),k1_xboole_0)
    | ~ spl11_479
    | ~ spl11_512 ),
    inference(backward_demodulation,[],[f10358,f12222])).

fof(f189341,plain,
    ( spl11_198
    | spl11_298
    | spl11_224 ),
    inference(avatar_split_clause,[],[f189340,f4069,f7044,f3591])).

fof(f3591,plain,
    ( spl11_198
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r1_tarski(sK4(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_198])])).

fof(f189340,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = sK3(sK0)
      | ~ r2_hidden(X0,sK3(sK0))
      | r1_tarski(sK6(sK0),X0)
      | ~ r2_hidden(X1,sK0)
      | r1_tarski(sK4(sK0),X1) ) ),
    inference(subsumption_resolution,[],[f9242,f55])).

fof(f9242,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = sK3(sK0)
      | ~ r2_hidden(X0,sK3(sK0))
      | r1_tarski(sK6(sK0),X0)
      | k1_xboole_0 = sK0
      | ~ r2_hidden(X1,sK0)
      | r1_tarski(sK4(sK0),X1) ) ),
    inference(resolution,[],[f137,f54])).

fof(f137,plain,(
    ! [X4,X0,X10] :
      ( ~ v1_finset_1(X0)
      | k1_xboole_0 = sK3(X0)
      | ~ r2_hidden(X4,sK3(X0))
      | r1_tarski(sK6(X0),X4)
      | k1_xboole_0 = X0
      | ~ r2_hidden(X10,X0)
      | r1_tarski(sK4(X0),X10) ) ),
    inference(trivial_inequality_removal,[],[f64])).

fof(f64,plain,(
    ! [X4,X0,X10] :
      ( ~ v1_finset_1(X0)
      | k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = sK3(X0)
      | ~ r2_hidden(X4,sK3(X0))
      | r1_tarski(sK6(X0),X4)
      | k1_xboole_0 = X0
      | ~ r2_hidden(X10,X0)
      | r1_tarski(sK4(X0),X10) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f189336,plain,
    ( ~ spl11_498
    | spl11_513
    | ~ spl11_514
    | ~ spl11_1796 ),
    inference(avatar_contradiction_clause,[],[f189335])).

fof(f189335,plain,
    ( $false
    | ~ spl11_498
    | ~ spl11_513
    | ~ spl11_514
    | ~ spl11_1796 ),
    inference(subsumption_resolution,[],[f189334,f12228])).

fof(f189334,plain,
    ( ~ r2_hidden(sK2(sK0),k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0))))
    | ~ spl11_498
    | ~ spl11_513
    | ~ spl11_514
    | ~ spl11_1796 ),
    inference(subsumption_resolution,[],[f189331,f311])).

fof(f189331,plain,
    ( ~ r1_tarski(sK2(sK0),sK2(sK0))
    | ~ r2_hidden(sK2(sK0),k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0))))
    | ~ spl11_498
    | ~ spl11_513
    | ~ spl11_514
    | ~ spl11_1796 ),
    inference(superposition,[],[f168690,f168091])).

fof(f168091,plain,
    ( sK2(sK0) = sK7(sK0,sK2(sK0))
    | ~ spl11_498
    | ~ spl11_513
    | ~ spl11_514 ),
    inference(resolution,[],[f167712,f131])).

fof(f167712,plain,
    ( r2_hidden(sK7(sK0,sK2(sK0)),k1_tarski(sK2(sK0)))
    | ~ spl11_498
    | ~ spl11_513
    | ~ spl11_514 ),
    inference(subsumption_resolution,[],[f167624,f12225])).

fof(f12225,plain,
    ( ~ r2_hidden(sK7(sK0,sK2(sK0)),sK3(sK0))
    | ~ spl11_513 ),
    inference(avatar_component_clause,[],[f12224])).

fof(f12224,plain,
    ( spl11_513
  <=> ~ r2_hidden(sK7(sK0,sK2(sK0)),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_513])])).

fof(f167624,plain,
    ( r2_hidden(sK7(sK0,sK2(sK0)),k1_tarski(sK2(sK0)))
    | r2_hidden(sK7(sK0,sK2(sK0)),sK3(sK0))
    | ~ spl11_498
    | ~ spl11_514 ),
    inference(resolution,[],[f33252,f12228])).

fof(f168692,plain,
    ( spl11_178
    | spl11_1796 ),
    inference(avatar_split_clause,[],[f8007,f168689,f3127])).

fof(f8007,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0))))
      | ~ r1_tarski(X0,sK7(sK0,X0))
      | r2_hidden(sK4(sK0),sK0) ) ),
    inference(subsumption_resolution,[],[f8006,f55])).

fof(f8006,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0))))
      | ~ r1_tarski(X0,sK7(sK0,X0))
      | k1_xboole_0 = sK0
      | r2_hidden(sK4(sK0),sK0) ) ),
    inference(resolution,[],[f140,f54])).

fof(f140,plain,(
    ! [X0,X5] :
      ( ~ v1_finset_1(X0)
      | ~ r2_hidden(X5,k2_xboole_0(sK3(X0),k1_tarski(sK2(X0))))
      | ~ r1_tarski(X5,sK7(X0,X5))
      | k1_xboole_0 = X0
      | r2_hidden(sK4(X0),X0) ) ),
    inference(trivial_inequality_removal,[],[f67])).

fof(f67,plain,(
    ! [X0,X5] :
      ( ~ v1_finset_1(X0)
      | k1_xboole_0 != k1_xboole_0
      | ~ r2_hidden(X5,k2_xboole_0(sK3(X0),k1_tarski(sK2(X0))))
      | ~ r1_tarski(X5,sK7(X0,X5))
      | k1_xboole_0 = X0
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f168691,plain,
    ( spl11_198
    | spl11_1796 ),
    inference(avatar_split_clause,[],[f168687,f168689,f3591])).

fof(f168687,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0))))
      | ~ r1_tarski(X0,sK7(sK0,X0))
      | ~ r2_hidden(X1,sK0)
      | r1_tarski(sK4(sK0),X1) ) ),
    inference(subsumption_resolution,[],[f10009,f55])).

fof(f10009,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0))))
      | ~ r1_tarski(X0,sK7(sK0,X0))
      | k1_xboole_0 = sK0
      | ~ r2_hidden(X1,sK0)
      | r1_tarski(sK4(sK0),X1) ) ),
    inference(resolution,[],[f142,f54])).

fof(f142,plain,(
    ! [X0,X10,X5] :
      ( ~ v1_finset_1(X0)
      | ~ r2_hidden(X5,k2_xboole_0(sK3(X0),k1_tarski(sK2(X0))))
      | ~ r1_tarski(X5,sK7(X0,X5))
      | k1_xboole_0 = X0
      | ~ r2_hidden(X10,X0)
      | r1_tarski(sK4(X0),X10) ) ),
    inference(trivial_inequality_removal,[],[f69])).

fof(f69,plain,(
    ! [X0,X10,X5] :
      ( ~ v1_finset_1(X0)
      | k1_xboole_0 != k1_xboole_0
      | ~ r2_hidden(X5,k2_xboole_0(sK3(X0),k1_tarski(sK2(X0))))
      | ~ r1_tarski(X5,sK7(X0,X5))
      | k1_xboole_0 = X0
      | ~ r2_hidden(X10,X0)
      | r1_tarski(sK4(X0),X10) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f36469,plain,
    ( ~ spl11_224
    | ~ spl11_478 ),
    inference(avatar_contradiction_clause,[],[f36468])).

fof(f36468,plain,
    ( $false
    | ~ spl11_224
    | ~ spl11_478 ),
    inference(subsumption_resolution,[],[f35705,f191])).

fof(f35705,plain,
    ( r2_hidden(sK8(k1_xboole_0),k1_xboole_0)
    | ~ spl11_224
    | ~ spl11_478 ),
    inference(backward_demodulation,[],[f4070,f10270])).

fof(f10270,plain,
    ( r2_hidden(sK8(sK3(sK0)),sK3(sK0))
    | ~ spl11_478 ),
    inference(avatar_component_clause,[],[f10269])).

fof(f10269,plain,
    ( spl11_478
  <=> r2_hidden(sK8(sK3(sK0)),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_478])])).

fof(f4070,plain,
    ( k1_xboole_0 = sK3(sK0)
    | ~ spl11_224 ),
    inference(avatar_component_clause,[],[f4069])).

fof(f31291,plain,(
    spl11_515 ),
    inference(avatar_contradiction_clause,[],[f31290])).

fof(f31290,plain,
    ( $false
    | ~ spl11_515 ),
    inference(subsumption_resolution,[],[f31289,f133])).

fof(f31289,plain,
    ( ~ r2_hidden(sK2(sK0),k1_tarski(sK2(sK0)))
    | ~ spl11_515 ),
    inference(resolution,[],[f12231,f134])).

fof(f134,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f129])).

fof(f129,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f12231,plain,
    ( ~ r2_hidden(sK2(sK0),k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0))))
    | ~ spl11_515 ),
    inference(avatar_component_clause,[],[f12230])).

fof(f12230,plain,
    ( spl11_515
  <=> ~ r2_hidden(sK2(sK0),k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_515])])).

fof(f18165,plain,
    ( spl11_179
    | spl11_217 ),
    inference(avatar_contradiction_clause,[],[f18164])).

fof(f18164,plain,
    ( $false
    | ~ spl11_179
    | ~ spl11_217 ),
    inference(subsumption_resolution,[],[f18163,f3131])).

fof(f18163,plain,
    ( r2_hidden(sK4(sK0),sK0)
    | ~ spl11_217 ),
    inference(subsumption_resolution,[],[f18162,f55])).

fof(f18162,plain,
    ( k1_xboole_0 = sK0
    | r2_hidden(sK4(sK0),sK0)
    | ~ spl11_217 ),
    inference(subsumption_resolution,[],[f18161,f54])).

fof(f18161,plain,
    ( ~ v1_finset_1(sK0)
    | k1_xboole_0 = sK0
    | r2_hidden(sK4(sK0),sK0)
    | ~ spl11_217 ),
    inference(resolution,[],[f3950,f149])).

fof(f149,plain,(
    ! [X0] :
      ( r1_tarski(sK3(X0),X0)
      | ~ v1_finset_1(X0)
      | k1_xboole_0 = X0
      | r2_hidden(sK4(X0),X0) ) ),
    inference(trivial_inequality_removal,[],[f100])).

fof(f100,plain,(
    ! [X0] :
      ( ~ v1_finset_1(X0)
      | k1_xboole_0 != k1_xboole_0
      | r1_tarski(sK3(X0),X0)
      | k1_xboole_0 = X0
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3950,plain,
    ( ~ r1_tarski(sK3(sK0),sK0)
    | ~ spl11_217 ),
    inference(avatar_component_clause,[],[f3949])).

fof(f3949,plain,
    ( spl11_217
  <=> ~ r1_tarski(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_217])])).

fof(f12295,plain,
    ( ~ spl11_342
    | spl11_525 ),
    inference(avatar_contradiction_clause,[],[f12294])).

fof(f12294,plain,
    ( $false
    | ~ spl11_342
    | ~ spl11_525 ),
    inference(subsumption_resolution,[],[f12292,f7600])).

fof(f11711,plain,
    ( spl11_198
    | spl11_498 ),
    inference(avatar_split_clause,[],[f11707,f11709,f3591])).

fof(f11707,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0))))
      | r2_hidden(sK7(sK0,X0),k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0))))
      | ~ r2_hidden(X1,sK0)
      | r1_tarski(sK4(sK0),X1) ) ),
    inference(subsumption_resolution,[],[f11706,f55])).

fof(f11706,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0))))
      | r2_hidden(sK7(sK0,X0),k2_xboole_0(sK3(sK0),k1_tarski(sK2(sK0))))
      | k1_xboole_0 = sK0
      | ~ r2_hidden(X1,sK0)
      | r1_tarski(sK4(sK0),X1) ) ),
    inference(resolution,[],[f141,f54])).

fof(f141,plain,(
    ! [X0,X10,X5] :
      ( ~ v1_finset_1(X0)
      | ~ r2_hidden(X5,k2_xboole_0(sK3(X0),k1_tarski(sK2(X0))))
      | r2_hidden(sK7(X0,X5),k2_xboole_0(sK3(X0),k1_tarski(sK2(X0))))
      | k1_xboole_0 = X0
      | ~ r2_hidden(X10,X0)
      | r1_tarski(sK4(X0),X10) ) ),
    inference(trivial_inequality_removal,[],[f68])).

fof(f68,plain,(
    ! [X0,X10,X5] :
      ( ~ v1_finset_1(X0)
      | k1_xboole_0 != k1_xboole_0
      | ~ r2_hidden(X5,k2_xboole_0(sK3(X0),k1_tarski(sK2(X0))))
      | r2_hidden(sK7(X0,X5),k2_xboole_0(sK3(X0),k1_tarski(sK2(X0))))
      | k1_xboole_0 = X0
      | ~ r2_hidden(X10,X0)
      | r1_tarski(sK4(X0),X10) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7601,plain,
    ( spl11_198
    | spl11_342
    | spl11_224 ),
    inference(avatar_split_clause,[],[f7594,f4069,f7599,f3591])).

fof(f7594,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK3(sK0)
      | r2_hidden(sK6(sK0),sK3(sK0))
      | ~ r2_hidden(X0,sK0)
      | r1_tarski(sK4(sK0),X0) ) ),
    inference(subsumption_resolution,[],[f7593,f55])).

fof(f7593,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK3(sK0)
      | r2_hidden(sK6(sK0),sK3(sK0))
      | k1_xboole_0 = sK0
      | ~ r2_hidden(X0,sK0)
      | r1_tarski(sK4(sK0),X0) ) ),
    inference(resolution,[],[f144,f54])).

fof(f144,plain,(
    ! [X0,X10] :
      ( ~ v1_finset_1(X0)
      | k1_xboole_0 = sK3(X0)
      | r2_hidden(sK6(X0),sK3(X0))
      | k1_xboole_0 = X0
      | ~ r2_hidden(X10,X0)
      | r1_tarski(sK4(X0),X10) ) ),
    inference(trivial_inequality_removal,[],[f79])).

fof(f79,plain,(
    ! [X0,X10] :
      ( ~ v1_finset_1(X0)
      | k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = sK3(X0)
      | r2_hidden(sK6(X0),sK3(X0))
      | k1_xboole_0 = X0
      | ~ r2_hidden(X10,X0)
      | r1_tarski(sK4(X0),X10) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3971,plain,
    ( ~ spl11_178
    | ~ spl11_198 ),
    inference(avatar_contradiction_clause,[],[f3970])).

fof(f3970,plain,
    ( $false
    | ~ spl11_178
    | ~ spl11_198 ),
    inference(subsumption_resolution,[],[f3969,f3128])).

fof(f3128,plain,
    ( r2_hidden(sK4(sK0),sK0)
    | ~ spl11_178 ),
    inference(avatar_component_clause,[],[f3127])).

fof(f3969,plain,
    ( ~ r2_hidden(sK4(sK0),sK0)
    | ~ spl11_178
    | ~ spl11_198 ),
    inference(resolution,[],[f3968,f52])).

fof(f52,plain,(
    ! [X1] :
      ( r2_hidden(sK1(X1),sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3968,plain,
    ( ~ r2_hidden(sK1(sK4(sK0)),sK0)
    | ~ spl11_178
    | ~ spl11_198 ),
    inference(subsumption_resolution,[],[f3962,f3128])).

fof(f3962,plain,
    ( ~ r2_hidden(sK1(sK4(sK0)),sK0)
    | ~ r2_hidden(sK4(sK0),sK0)
    | ~ spl11_198 ),
    inference(resolution,[],[f3592,f53])).

fof(f53,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK1(X1))
      | ~ r2_hidden(X1,sK0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3592,plain,
    ( ! [X0] :
        ( r1_tarski(sK4(sK0),X0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl11_198 ),
    inference(avatar_component_clause,[],[f3591])).

fof(f3954,plain,
    ( spl11_198
    | spl11_216 ),
    inference(avatar_split_clause,[],[f3947,f3952,f3591])).

fof(f3947,plain,(
    ! [X0] :
      ( r1_tarski(sK3(sK0),sK0)
      | ~ r2_hidden(X0,sK0)
      | r1_tarski(sK4(sK0),X0) ) ),
    inference(subsumption_resolution,[],[f3946,f55])).

fof(f3946,plain,(
    ! [X0] :
      ( r1_tarski(sK3(sK0),sK0)
      | k1_xboole_0 = sK0
      | ~ r2_hidden(X0,sK0)
      | r1_tarski(sK4(sK0),X0) ) ),
    inference(resolution,[],[f146,f54])).

fof(f146,plain,(
    ! [X0,X10] :
      ( ~ v1_finset_1(X0)
      | r1_tarski(sK3(X0),X0)
      | k1_xboole_0 = X0
      | ~ r2_hidden(X10,X0)
      | r1_tarski(sK4(X0),X10) ) ),
    inference(trivial_inequality_removal,[],[f97])).

fof(f97,plain,(
    ! [X0,X10] :
      ( ~ v1_finset_1(X0)
      | k1_xboole_0 != k1_xboole_0
      | r1_tarski(sK3(X0),X0)
      | k1_xboole_0 = X0
      | ~ r2_hidden(X10,X0)
      | r1_tarski(sK4(X0),X10) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3588,plain,
    ( spl11_127
    | ~ spl11_178 ),
    inference(avatar_contradiction_clause,[],[f3587])).

fof(f3587,plain,
    ( $false
    | ~ spl11_127
    | ~ spl11_178 ),
    inference(subsumption_resolution,[],[f3586,f3128])).

fof(f3586,plain,
    ( ~ r2_hidden(sK4(sK0),sK0)
    | ~ spl11_127
    | ~ spl11_178 ),
    inference(resolution,[],[f3585,f52])).

fof(f3585,plain,
    ( ~ r2_hidden(sK1(sK4(sK0)),sK0)
    | ~ spl11_127
    | ~ spl11_178 ),
    inference(subsumption_resolution,[],[f3582,f3128])).

fof(f3582,plain,
    ( ~ r2_hidden(sK1(sK4(sK0)),sK0)
    | ~ r2_hidden(sK4(sK0),sK0)
    | ~ spl11_127 ),
    inference(resolution,[],[f3535,f53])).

fof(f3535,plain,
    ( ! [X0] :
        ( r1_tarski(sK4(sK0),X0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl11_127 ),
    inference(subsumption_resolution,[],[f3534,f55])).

fof(f3534,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK0
        | ~ r2_hidden(X0,sK0)
        | r1_tarski(sK4(sK0),X0) )
    | ~ spl11_127 ),
    inference(subsumption_resolution,[],[f3533,f2412])).

fof(f2412,plain,
    ( ~ r2_hidden(sK2(sK0),sK0)
    | ~ spl11_127 ),
    inference(avatar_component_clause,[],[f2411])).

fof(f2411,plain,
    ( spl11_127
  <=> ~ r2_hidden(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_127])])).

fof(f3533,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK0),sK0)
      | k1_xboole_0 = sK0
      | ~ r2_hidden(X0,sK0)
      | r1_tarski(sK4(sK0),X0) ) ),
    inference(resolution,[],[f145,f54])).

fof(f145,plain,(
    ! [X0,X10] :
      ( ~ v1_finset_1(X0)
      | r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0
      | ~ r2_hidden(X10,X0)
      | r1_tarski(sK4(X0),X10) ) ),
    inference(trivial_inequality_removal,[],[f96])).

fof(f96,plain,(
    ! [X0,X10] :
      ( ~ v1_finset_1(X0)
      | k1_xboole_0 != k1_xboole_0
      | r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0
      | ~ r2_hidden(X10,X0)
      | r1_tarski(sK4(X0),X10) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3143,plain,
    ( spl11_127
    | spl11_179 ),
    inference(avatar_contradiction_clause,[],[f3142])).

fof(f3142,plain,
    ( $false
    | ~ spl11_127
    | ~ spl11_179 ),
    inference(subsumption_resolution,[],[f3141,f54])).

fof(f3141,plain,
    ( ~ v1_finset_1(sK0)
    | ~ spl11_127
    | ~ spl11_179 ),
    inference(subsumption_resolution,[],[f3140,f55])).

fof(f3140,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_finset_1(sK0)
    | ~ spl11_127
    | ~ spl11_179 ),
    inference(subsumption_resolution,[],[f3139,f2412])).

fof(f3139,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | k1_xboole_0 = sK0
    | ~ v1_finset_1(sK0)
    | ~ spl11_179 ),
    inference(resolution,[],[f3131,f150])).

fof(f150,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0
      | ~ v1_finset_1(X0) ) ),
    inference(trivial_inequality_removal,[],[f101])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v1_finset_1(X0)
      | k1_xboole_0 != k1_xboole_0
      | r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1109,plain,(
    ~ spl11_30 ),
    inference(avatar_contradiction_clause,[],[f1108])).

fof(f1108,plain,
    ( $false
    | ~ spl11_30 ),
    inference(subsumption_resolution,[],[f1104,f55])).

fof(f1104,plain,
    ( k1_xboole_0 = sK0
    | ~ spl11_30 ),
    inference(resolution,[],[f988,f59])).

fof(f988,plain,
    ( v1_xboole_0(sK0)
    | ~ spl11_30 ),
    inference(avatar_component_clause,[],[f987])).

fof(f987,plain,
    ( spl11_30
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).
%------------------------------------------------------------------------------
