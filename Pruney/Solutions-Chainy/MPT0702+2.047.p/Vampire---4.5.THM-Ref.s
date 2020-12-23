%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 363 expanded)
%              Number of leaves         :   27 ( 159 expanded)
%              Depth                    :    7
%              Number of atoms          :  305 (1105 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f164,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f38,f43,f48,f53,f58,f67,f72,f77,f83,f96,f101,f106,f111,f116,f125,f130,f135,f140,f152,f161,f162,f163])).

fof(f163,plain,
    ( ~ spl3_11
    | ~ spl3_3
    | spl3_12 ),
    inference(avatar_split_clause,[],[f153,f98,f40,f93])).

fof(f93,plain,
    ( spl3_11
  <=> r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k9_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f40,plain,
    ( spl3_3
  <=> r1_tarski(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f98,plain,
    ( spl3_12
  <=> r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f153,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k9_relat_1(sK2,sK1)))
    | ~ spl3_3
    | spl3_12 ),
    inference(unit_resulting_resolution,[],[f42,f100,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f100,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1)))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f98])).

fof(f42,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f162,plain,
    ( ~ spl3_10
    | ~ spl3_9
    | spl3_12 ),
    inference(avatar_split_clause,[],[f154,f98,f74,f80])).

fof(f80,plain,
    ( spl3_10
  <=> r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,k9_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f74,plain,
    ( spl3_9
  <=> r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f154,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,k9_relat_1(sK2,sK1)))
    | ~ spl3_9
    | spl3_12 ),
    inference(unit_resulting_resolution,[],[f76,f100,f28])).

fof(f76,plain,
    ( r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f74])).

fof(f161,plain,
    ( ~ spl3_21
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_6
    | spl3_12 ),
    inference(avatar_split_clause,[],[f156,f98,f55,f50,f35,f158])).

fof(f158,plain,
    ( spl3_21
  <=> r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,k10_relat_1(sK2,k9_relat_1(sK2,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f35,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f50,plain,
    ( spl3_5
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f55,plain,
    ( spl3_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f156,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,k10_relat_1(sK2,k9_relat_1(sK2,sK1)))))
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_6
    | spl3_12 ),
    inference(unit_resulting_resolution,[],[f59,f100,f28])).

fof(f59,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f37,f52,f57,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(f57,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f55])).

fof(f52,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f37,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f152,plain,
    ( spl3_20
    | ~ spl3_6
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f147,f132,f55,f149])).

fof(f149,plain,
    ( spl3_20
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f132,plain,
    ( spl3_18
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f147,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0))
    | ~ spl3_6
    | ~ spl3_18 ),
    inference(unit_resulting_resolution,[],[f57,f134,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

fof(f134,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f132])).

fof(f140,plain,
    ( ~ spl3_19
    | spl3_1
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f117,f74,f30,f137])).

fof(f137,plain,
    ( spl3_19
  <=> r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f30,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f117,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK1)
    | spl3_1
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f32,f76,f28])).

fof(f32,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f135,plain,
    ( spl3_18
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f118,f74,f55,f50,f35,f132])).

fof(f118,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f59,f76,f28])).

fof(f130,plain,
    ( spl3_17
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f119,f74,f55,f50,f35,f127])).

fof(f127,plain,
    ( spl3_17
  <=> r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,k9_relat_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f119,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f59,f76,f28])).

fof(f125,plain,
    ( spl3_16
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f120,f74,f55,f122])).

fof(f122,plain,
    ( spl3_16
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f120,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k10_relat_1(sK2,k9_relat_1(sK2,sK0))))
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f57,f76,f27])).

fof(f116,plain,
    ( spl3_15
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f84,f55,f50,f35,f113])).

fof(f113,plain,
    ( spl3_15
  <=> r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,k1_relat_1(sK2))),k10_relat_1(sK2,k9_relat_1(sK2,k10_relat_1(sK2,k9_relat_1(sK2,k1_relat_1(sK2)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f84,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,k1_relat_1(sK2))),k10_relat_1(sK2,k9_relat_1(sK2,k10_relat_1(sK2,k9_relat_1(sK2,k1_relat_1(sK2))))))
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f57,f59,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f111,plain,
    ( spl3_14
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f85,f55,f50,f40,f35,f108])).

fof(f108,plain,
    ( spl3_14
  <=> r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f85,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_relat_1(sK2))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f42,f59,f28])).

fof(f106,plain,
    ( spl3_13
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f86,f55,f50,f45,f35,f103])).

fof(f103,plain,
    ( spl3_13
  <=> r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,k9_relat_1(sK2,sK0))),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f45,plain,
    ( spl3_4
  <=> r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f86,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,k9_relat_1(sK2,sK0))),k9_relat_1(sK2,sK1))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f47,f59,f28])).

fof(f47,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f101,plain,
    ( ~ spl3_12
    | spl3_1
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f88,f55,f50,f35,f30,f98])).

fof(f88,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f32,f59,f28])).

fof(f96,plain,
    ( ~ spl3_11
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_6
    | spl3_8 ),
    inference(avatar_split_clause,[],[f89,f69,f55,f50,f35,f93])).

fof(f69,plain,
    ( spl3_8
  <=> r1_tarski(k1_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f89,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k9_relat_1(sK2,sK1)))
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_6
    | spl3_8 ),
    inference(unit_resulting_resolution,[],[f71,f59,f28])).

fof(f71,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK1)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f69])).

fof(f83,plain,
    ( spl3_10
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f78,f55,f45,f80])).

fof(f78,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,k9_relat_1(sK2,sK1)))
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f57,f47,f27])).

fof(f77,plain,
    ( spl3_9
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f60,f55,f40,f74])).

fof(f60,plain,
    ( r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f57,f42,f25])).

fof(f72,plain,
    ( ~ spl3_8
    | spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f61,f40,f30,f69])).

fof(f61,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK1)
    | spl3_1
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f32,f42,f28])).

fof(f67,plain,
    ( spl3_7
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f62,f55,f40,f64])).

fof(f64,plain,
    ( spl3_7
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f62,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k1_relat_1(sK2)))
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f57,f42,f27])).

fof(f58,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f19,f55])).

fof(f19,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & v2_funct_1(X2)
        & r1_tarski(X0,k1_relat_1(X2))
        & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & v2_funct_1(sK2)
      & r1_tarski(sK0,k1_relat_1(sK2))
      & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

fof(f53,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f20,f50])).

fof(f20,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f48,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f21,f45])).

fof(f21,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f22,f40])).

fof(f22,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f23,f35])).

fof(f23,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f33,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f24,f30])).

fof(f24,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:14:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (26118)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.47  % (26118)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f164,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f33,f38,f43,f48,f53,f58,f67,f72,f77,f83,f96,f101,f106,f111,f116,f125,f130,f135,f140,f152,f161,f162,f163])).
% 0.21/0.47  fof(f163,plain,(
% 0.21/0.47    ~spl3_11 | ~spl3_3 | spl3_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f153,f98,f40,f93])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    spl3_11 <=> r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k9_relat_1(sK2,sK1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    spl3_3 <=> r1_tarski(sK0,k1_relat_1(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    spl3_12 <=> r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.47  fof(f153,plain,(
% 0.21/0.47    ~r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k9_relat_1(sK2,sK1))) | (~spl3_3 | spl3_12)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f42,f100,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    ~r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1))) | spl3_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f98])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    r1_tarski(sK0,k1_relat_1(sK2)) | ~spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f40])).
% 0.21/0.47  fof(f162,plain,(
% 0.21/0.47    ~spl3_10 | ~spl3_9 | spl3_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f154,f98,f74,f80])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    spl3_10 <=> r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,k9_relat_1(sK2,sK1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    spl3_9 <=> r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.47  fof(f154,plain,(
% 0.21/0.47    ~r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,k9_relat_1(sK2,sK1))) | (~spl3_9 | spl3_12)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f76,f100,f28])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) | ~spl3_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f74])).
% 0.21/0.47  fof(f161,plain,(
% 0.21/0.47    ~spl3_21 | ~spl3_2 | ~spl3_5 | ~spl3_6 | spl3_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f156,f98,f55,f50,f35,f158])).
% 0.21/0.47  fof(f158,plain,(
% 0.21/0.47    spl3_21 <=> r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,k10_relat_1(sK2,k9_relat_1(sK2,sK1)))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    spl3_2 <=> v2_funct_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    spl3_5 <=> v1_funct_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    spl3_6 <=> v1_relat_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.47  fof(f156,plain,(
% 0.21/0.47    ~r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,k10_relat_1(sK2,k9_relat_1(sK2,sK1))))) | (~spl3_2 | ~spl3_5 | ~spl3_6 | spl3_12)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f59,f100,f28])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)) ) | (~spl3_2 | ~spl3_5 | ~spl3_6)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f37,f52,f57,f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    v1_relat_1(sK2) | ~spl3_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f55])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    v1_funct_1(sK2) | ~spl3_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f50])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    v2_funct_1(sK2) | ~spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f35])).
% 0.21/0.47  fof(f152,plain,(
% 0.21/0.47    spl3_20 | ~spl3_6 | ~spl3_18),
% 0.21/0.47    inference(avatar_split_clause,[],[f147,f132,f55,f149])).
% 0.21/0.47  fof(f149,plain,(
% 0.21/0.47    spl3_20 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    spl3_18 <=> r1_tarski(sK0,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.47  fof(f147,plain,(
% 0.21/0.47    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0)) | (~spl3_6 | ~spl3_18)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f57,f134,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(flattening,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).
% 0.21/0.47  fof(f134,plain,(
% 0.21/0.47    r1_tarski(sK0,sK0) | ~spl3_18),
% 0.21/0.47    inference(avatar_component_clause,[],[f132])).
% 0.21/0.47  fof(f140,plain,(
% 0.21/0.47    ~spl3_19 | spl3_1 | ~spl3_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f117,f74,f30,f137])).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    spl3_19 <=> r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    ~r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK1) | (spl3_1 | ~spl3_9)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f32,f76,f28])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ~r1_tarski(sK0,sK1) | spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f30])).
% 0.21/0.47  fof(f135,plain,(
% 0.21/0.47    spl3_18 | ~spl3_2 | ~spl3_5 | ~spl3_6 | ~spl3_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f118,f74,f55,f50,f35,f132])).
% 0.21/0.47  fof(f118,plain,(
% 0.21/0.47    r1_tarski(sK0,sK0) | (~spl3_2 | ~spl3_5 | ~spl3_6 | ~spl3_9)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f59,f76,f28])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    spl3_17 | ~spl3_2 | ~spl3_5 | ~spl3_6 | ~spl3_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f119,f74,f55,f50,f35,f127])).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    spl3_17 <=> r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,k9_relat_1(sK2,sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,k9_relat_1(sK2,sK0))) | (~spl3_2 | ~spl3_5 | ~spl3_6 | ~spl3_9)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f59,f76,f28])).
% 0.21/0.47  fof(f125,plain,(
% 0.21/0.47    spl3_16 | ~spl3_6 | ~spl3_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f120,f74,f55,f122])).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    spl3_16 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k10_relat_1(sK2,k9_relat_1(sK2,sK0))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))) | (~spl3_6 | ~spl3_9)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f57,f76,f27])).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    spl3_15 | ~spl3_2 | ~spl3_5 | ~spl3_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f84,f55,f50,f35,f113])).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    spl3_15 <=> r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,k1_relat_1(sK2))),k10_relat_1(sK2,k9_relat_1(sK2,k10_relat_1(sK2,k9_relat_1(sK2,k1_relat_1(sK2))))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,k1_relat_1(sK2))),k10_relat_1(sK2,k9_relat_1(sK2,k10_relat_1(sK2,k9_relat_1(sK2,k1_relat_1(sK2)))))) | (~spl3_2 | ~spl3_5 | ~spl3_6)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f57,f59,f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    spl3_14 | ~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f85,f55,f50,f40,f35,f108])).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    spl3_14 <=> r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_relat_1(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_relat_1(sK2)) | (~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_6)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f42,f59,f28])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    spl3_13 | ~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f86,f55,f50,f45,f35,f103])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    spl3_13 <=> r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,k9_relat_1(sK2,sK0))),k9_relat_1(sK2,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    spl3_4 <=> r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,k9_relat_1(sK2,sK0))),k9_relat_1(sK2,sK1)) | (~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_6)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f47,f59,f28])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) | ~spl3_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f45])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    ~spl3_12 | spl3_1 | ~spl3_2 | ~spl3_5 | ~spl3_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f88,f55,f50,f35,f30,f98])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    ~r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1))) | (spl3_1 | ~spl3_2 | ~spl3_5 | ~spl3_6)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f32,f59,f28])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    ~spl3_11 | ~spl3_2 | ~spl3_5 | ~spl3_6 | spl3_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f89,f69,f55,f50,f35,f93])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    spl3_8 <=> r1_tarski(k1_relat_1(sK2),sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    ~r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k9_relat_1(sK2,sK1))) | (~spl3_2 | ~spl3_5 | ~spl3_6 | spl3_8)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f71,f59,f28])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    ~r1_tarski(k1_relat_1(sK2),sK1) | spl3_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f69])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    spl3_10 | ~spl3_4 | ~spl3_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f78,f55,f45,f80])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,k9_relat_1(sK2,sK1))) | (~spl3_4 | ~spl3_6)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f57,f47,f27])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    spl3_9 | ~spl3_3 | ~spl3_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f60,f55,f40,f74])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) | (~spl3_3 | ~spl3_6)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f57,f42,f25])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    ~spl3_8 | spl3_1 | ~spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f61,f40,f30,f69])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    ~r1_tarski(k1_relat_1(sK2),sK1) | (spl3_1 | ~spl3_3)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f32,f42,f28])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    spl3_7 | ~spl3_3 | ~spl3_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f62,f55,f40,f64])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    spl3_7 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k1_relat_1(sK2)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k1_relat_1(sK2))) | (~spl3_3 | ~spl3_6)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f57,f42,f27])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    spl3_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f19,f55])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    v1_relat_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.47    inference(flattening,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.21/0.47    inference(negated_conjecture,[],[f5])).
% 0.21/0.47  fof(f5,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    spl3_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f20,f50])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    v1_funct_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f21,f45])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f22,f40])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    r1_tarski(sK0,k1_relat_1(sK2))),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f23,f35])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    v2_funct_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ~spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f24,f30])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ~r1_tarski(sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (26118)------------------------------
% 0.21/0.47  % (26118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (26118)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (26118)Memory used [KB]: 5373
% 0.21/0.47  % (26118)Time elapsed: 0.064 s
% 0.21/0.47  % (26118)------------------------------
% 0.21/0.47  % (26118)------------------------------
% 0.21/0.47  % (26104)Success in time 0.116 s
%------------------------------------------------------------------------------
