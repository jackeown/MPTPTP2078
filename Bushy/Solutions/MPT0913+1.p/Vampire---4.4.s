%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t73_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:13 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  264 ( 723 expanded)
%              Number of leaves         :   69 ( 293 expanded)
%              Depth                    :   12
%              Number of atoms          :  619 (1911 expanded)
%              Number of equality atoms :    9 (  17 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f888,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f67,f86,f95,f102,f109,f118,f125,f132,f142,f151,f158,f175,f190,f197,f204,f206,f210,f217,f228,f235,f236,f263,f278,f285,f292,f299,f314,f321,f328,f343,f350,f381,f396,f403,f421,f436,f443,f457,f472,f479,f493,f508,f515,f533,f548,f555,f602,f606,f608,f610,f618,f620,f621,f622,f629,f644,f651,f692,f707,f714,f752,f767,f778,f875,f883,f885])).

fof(f885,plain,
    ( spl7_7
    | ~ spl7_106 ),
    inference(avatar_contradiction_clause,[],[f884])).

fof(f884,plain,
    ( $false
    | ~ spl7_7
    | ~ spl7_106 ),
    inference(subsumption_resolution,[],[f877,f82])).

fof(f82,plain,
    ( ~ r2_hidden(sK0,sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl7_7
  <=> ~ r2_hidden(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f877,plain,
    ( r2_hidden(sK0,sK3)
    | ~ spl7_106 ),
    inference(resolution,[],[f874,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t73_mcart_1.p',t106_zfmisc_1)).

fof(f874,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4))
    | ~ spl7_106 ),
    inference(avatar_component_clause,[],[f873])).

fof(f873,plain,
    ( spl7_106
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_106])])).

fof(f883,plain,
    ( spl7_13
    | ~ spl7_106 ),
    inference(avatar_contradiction_clause,[],[f882])).

fof(f882,plain,
    ( $false
    | ~ spl7_13
    | ~ spl7_106 ),
    inference(subsumption_resolution,[],[f876,f105])).

fof(f105,plain,
    ( ~ r2_hidden(sK1,sK4)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl7_13
  <=> ~ r2_hidden(sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f876,plain,
    ( r2_hidden(sK1,sK4)
    | ~ spl7_106 ),
    inference(resolution,[],[f874,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f875,plain,
    ( spl7_106
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f861,f78,f873])).

fof(f78,plain,
    ( spl7_4
  <=> r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f861,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4))
    | ~ spl7_4 ),
    inference(resolution,[],[f659,f79])).

fof(f79,plain,
    ( r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f659,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(k3_mcart_1(X3,X4,X5),k3_zfmisc_1(X0,X1,X2))
      | r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X0,X1)) ) ),
    inference(superposition,[],[f135,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t73_mcart_1.p',d3_zfmisc_1)).

fof(f135,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k3_mcart_1(X0,X1,X2),k2_zfmisc_1(X3,X4))
      | r2_hidden(k4_tarski(X0,X1),X3) ) ),
    inference(superposition,[],[f50,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t73_mcart_1.p',d3_mcart_1)).

fof(f778,plain,
    ( ~ spl7_105
    | ~ spl7_100 ),
    inference(avatar_split_clause,[],[f757,f750,f776])).

fof(f776,plain,
    ( spl7_105
  <=> ~ r2_hidden(k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,k3_zfmisc_1(sK3,sK4,sK5))),k4_tarski(sK2,k4_tarski(sK2,k3_mcart_1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_105])])).

fof(f750,plain,
    ( spl7_100
  <=> r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k3_mcart_1(sK0,sK1,sK2))),k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,k3_zfmisc_1(sK3,sK4,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_100])])).

fof(f757,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,k3_zfmisc_1(sK3,sK4,sK5))),k4_tarski(sK2,k4_tarski(sK2,k3_mcart_1(sK0,sK1,sK2))))
    | ~ spl7_100 ),
    inference(resolution,[],[f751,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t73_mcart_1.p',antisymmetry_r2_hidden)).

fof(f751,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k3_mcart_1(sK0,sK1,sK2))),k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,k3_zfmisc_1(sK3,sK4,sK5))))
    | ~ spl7_100 ),
    inference(avatar_component_clause,[],[f750])).

fof(f767,plain,
    ( ~ spl7_103
    | ~ spl7_100 ),
    inference(avatar_split_clause,[],[f758,f750,f765])).

fof(f765,plain,
    ( spl7_103
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,k3_zfmisc_1(sK3,sK4,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_103])])).

fof(f758,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,k3_zfmisc_1(sK3,sK4,sK5))))
    | ~ spl7_100 ),
    inference(resolution,[],[f751,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t73_mcart_1.p',t7_boole)).

fof(f752,plain,
    ( spl7_100
    | ~ spl7_18
    | ~ spl7_88 ),
    inference(avatar_split_clause,[],[f632,f627,f130,f750])).

fof(f130,plain,
    ( spl7_18
  <=> r2_hidden(sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f627,plain,
    ( spl7_88
  <=> r2_hidden(k4_tarski(sK2,k3_mcart_1(sK0,sK1,sK2)),k2_zfmisc_1(sK5,k3_zfmisc_1(sK3,sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_88])])).

fof(f632,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k3_mcart_1(sK0,sK1,sK2))),k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,k3_zfmisc_1(sK3,sK4,sK5))))
    | ~ spl7_18
    | ~ spl7_88 ),
    inference(resolution,[],[f628,f161])).

fof(f161,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,X5)
        | r2_hidden(k4_tarski(sK2,X4),k2_zfmisc_1(sK5,X5)) )
    | ~ spl7_18 ),
    inference(resolution,[],[f52,f131])).

fof(f131,plain,
    ( r2_hidden(sK2,sK5)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f130])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f628,plain,
    ( r2_hidden(k4_tarski(sK2,k3_mcart_1(sK0,sK1,sK2)),k2_zfmisc_1(sK5,k3_zfmisc_1(sK3,sK4,sK5)))
    | ~ spl7_88 ),
    inference(avatar_component_clause,[],[f627])).

fof(f714,plain,
    ( ~ spl7_99
    | ~ spl7_94 ),
    inference(avatar_split_clause,[],[f697,f690,f712])).

fof(f712,plain,
    ( spl7_99
  <=> ~ r2_hidden(k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,sK5))),k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_99])])).

fof(f690,plain,
    ( spl7_94
  <=> r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK2))),k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_94])])).

fof(f697,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,sK5))),k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK2))))
    | ~ spl7_94 ),
    inference(resolution,[],[f691,f43])).

fof(f691,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK2))),k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,sK5))))
    | ~ spl7_94 ),
    inference(avatar_component_clause,[],[f690])).

fof(f707,plain,
    ( ~ spl7_97
    | ~ spl7_94 ),
    inference(avatar_split_clause,[],[f698,f690,f705])).

fof(f705,plain,
    ( spl7_97
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_97])])).

fof(f698,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,sK5))))
    | ~ spl7_94 ),
    inference(resolution,[],[f691,f47])).

fof(f692,plain,
    ( spl7_94
    | ~ spl7_18
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f460,f455,f130,f690])).

fof(f455,plain,
    ( spl7_70
  <=> r2_hidden(k4_tarski(sK2,k4_tarski(sK2,sK2)),k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f460,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,k4_tarski(sK2,sK2))),k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,sK5))))
    | ~ spl7_18
    | ~ spl7_70 ),
    inference(resolution,[],[f456,f161])).

fof(f456,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,sK2)),k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,sK5)))
    | ~ spl7_70 ),
    inference(avatar_component_clause,[],[f455])).

fof(f651,plain,
    ( ~ spl7_93
    | ~ spl7_88 ),
    inference(avatar_split_clause,[],[f634,f627,f649])).

fof(f649,plain,
    ( spl7_93
  <=> ~ r2_hidden(k2_zfmisc_1(sK5,k3_zfmisc_1(sK3,sK4,sK5)),k4_tarski(sK2,k3_mcart_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_93])])).

fof(f634,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK5,k3_zfmisc_1(sK3,sK4,sK5)),k4_tarski(sK2,k3_mcart_1(sK0,sK1,sK2)))
    | ~ spl7_88 ),
    inference(resolution,[],[f628,f43])).

fof(f644,plain,
    ( ~ spl7_91
    | ~ spl7_88 ),
    inference(avatar_split_clause,[],[f635,f627,f642])).

fof(f642,plain,
    ( spl7_91
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK5,k3_zfmisc_1(sK3,sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_91])])).

fof(f635,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK5,k3_zfmisc_1(sK3,sK4,sK5)))
    | ~ spl7_88 ),
    inference(resolution,[],[f628,f47])).

fof(f629,plain,
    ( spl7_88
    | ~ spl7_4
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f612,f130,f78,f627])).

fof(f612,plain,
    ( r2_hidden(k4_tarski(sK2,k3_mcart_1(sK0,sK1,sK2)),k2_zfmisc_1(sK5,k3_zfmisc_1(sK3,sK4,sK5)))
    | ~ spl7_4
    | ~ spl7_18 ),
    inference(resolution,[],[f79,f161])).

fof(f622,plain,
    ( spl7_52
    | ~ spl7_82 ),
    inference(avatar_split_clause,[],[f534,f531,f326])).

fof(f326,plain,
    ( spl7_52
  <=> r2_hidden(k4_tarski(sK2,sK0),k2_zfmisc_1(sK5,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f531,plain,
    ( spl7_82
  <=> r2_hidden(k4_tarski(sK2,k4_tarski(sK2,sK0)),k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).

fof(f534,plain,
    ( r2_hidden(k4_tarski(sK2,sK0),k2_zfmisc_1(sK5,sK3))
    | ~ spl7_82 ),
    inference(resolution,[],[f532,f51])).

fof(f532,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,sK0)),k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,sK3)))
    | ~ spl7_82 ),
    inference(avatar_component_clause,[],[f531])).

fof(f621,plain,
    ( spl7_30
    | ~ spl7_64 ),
    inference(avatar_split_clause,[],[f422,f419,f202])).

fof(f202,plain,
    ( spl7_30
  <=> r2_hidden(k4_tarski(sK0,sK2),k2_zfmisc_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f419,plain,
    ( spl7_64
  <=> r2_hidden(k4_tarski(sK2,k4_tarski(sK0,sK2)),k2_zfmisc_1(sK5,k2_zfmisc_1(sK3,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f422,plain,
    ( r2_hidden(k4_tarski(sK0,sK2),k2_zfmisc_1(sK3,sK5))
    | ~ spl7_64 ),
    inference(resolution,[],[f420,f51])).

fof(f420,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK0,sK2)),k2_zfmisc_1(sK5,k2_zfmisc_1(sK3,sK5)))
    | ~ spl7_64 ),
    inference(avatar_component_clause,[],[f419])).

fof(f620,plain,
    ( spl7_47
    | ~ spl7_76 ),
    inference(avatar_contradiction_clause,[],[f619])).

fof(f619,plain,
    ( $false
    | ~ spl7_47
    | ~ spl7_76 ),
    inference(subsumption_resolution,[],[f295,f494])).

fof(f494,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),k2_zfmisc_1(sK5,sK4))
    | ~ spl7_76 ),
    inference(resolution,[],[f492,f51])).

fof(f492,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,sK1)),k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,sK4)))
    | ~ spl7_76 ),
    inference(avatar_component_clause,[],[f491])).

fof(f491,plain,
    ( spl7_76
  <=> r2_hidden(k4_tarski(sK2,k4_tarski(sK2,sK1)),k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_76])])).

fof(f295,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK1),k2_zfmisc_1(sK5,sK4))
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl7_47
  <=> ~ r2_hidden(k4_tarski(sK2,sK1),k2_zfmisc_1(sK5,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f618,plain,
    ( spl7_12
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f300,f297,f107])).

fof(f107,plain,
    ( spl7_12
  <=> r2_hidden(sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f297,plain,
    ( spl7_46
  <=> r2_hidden(k4_tarski(sK2,sK1),k2_zfmisc_1(sK5,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f300,plain,
    ( r2_hidden(sK1,sK4)
    | ~ spl7_46 ),
    inference(resolution,[],[f298,f51])).

fof(f298,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),k2_zfmisc_1(sK5,sK4))
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f297])).

fof(f610,plain,
    ( spl7_7
    | ~ spl7_30 ),
    inference(avatar_contradiction_clause,[],[f609])).

fof(f609,plain,
    ( $false
    | ~ spl7_7
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f250,f82])).

fof(f250,plain,
    ( r2_hidden(sK0,sK3)
    | ~ spl7_30 ),
    inference(resolution,[],[f203,f50])).

fof(f203,plain,
    ( r2_hidden(k4_tarski(sK0,sK2),k2_zfmisc_1(sK3,sK5))
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f202])).

fof(f608,plain,
    ( spl7_7
    | ~ spl7_52 ),
    inference(avatar_contradiction_clause,[],[f607])).

fof(f607,plain,
    ( $false
    | ~ spl7_7
    | ~ spl7_52 ),
    inference(subsumption_resolution,[],[f82,f329])).

fof(f329,plain,
    ( r2_hidden(sK0,sK3)
    | ~ spl7_52 ),
    inference(resolution,[],[f327,f51])).

fof(f327,plain,
    ( r2_hidden(k4_tarski(sK2,sK0),k2_zfmisc_1(sK5,sK3))
    | ~ spl7_52 ),
    inference(avatar_component_clause,[],[f326])).

fof(f606,plain,
    ( spl7_25
    | ~ spl7_58 ),
    inference(avatar_contradiction_clause,[],[f605])).

fof(f605,plain,
    ( $false
    | ~ spl7_25
    | ~ spl7_58 ),
    inference(subsumption_resolution,[],[f171,f382])).

fof(f382,plain,
    ( r2_hidden(k4_tarski(sK0,sK0),k2_zfmisc_1(sK3,sK3))
    | ~ spl7_58 ),
    inference(resolution,[],[f380,f51])).

fof(f380,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK0,sK0)),k2_zfmisc_1(sK5,k2_zfmisc_1(sK3,sK3)))
    | ~ spl7_58 ),
    inference(avatar_component_clause,[],[f379])).

fof(f379,plain,
    ( spl7_58
  <=> r2_hidden(k4_tarski(sK2,k4_tarski(sK0,sK0)),k2_zfmisc_1(sK5,k2_zfmisc_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f171,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK0),k2_zfmisc_1(sK3,sK3))
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl7_25
  <=> ~ r2_hidden(k4_tarski(sK0,sK0),k2_zfmisc_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f602,plain,
    ( spl7_5
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_18 ),
    inference(avatar_contradiction_clause,[],[f601])).

fof(f601,plain,
    ( $false
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f600,f131])).

fof(f600,plain,
    ( ~ r2_hidden(sK2,sK5)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f594,f108])).

fof(f108,plain,
    ( r2_hidden(sK1,sK4)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f107])).

fof(f594,plain,
    ( ~ r2_hidden(sK1,sK4)
    | ~ r2_hidden(sK2,sK5)
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(resolution,[],[f366,f76])).

fof(f76,plain,
    ( ~ r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl7_5
  <=> ~ r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f366,plain,
    ( ! [X6,X8,X7,X9] :
        ( r2_hidden(k3_mcart_1(sK0,X6,X8),k3_zfmisc_1(sK3,X7,X9))
        | ~ r2_hidden(X6,X7)
        | ~ r2_hidden(X8,X9) )
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f365,f48])).

fof(f365,plain,
    ( ! [X6,X8,X7,X9] :
        ( r2_hidden(k4_tarski(k4_tarski(sK0,X6),X8),k3_zfmisc_1(sK3,X7,X9))
        | ~ r2_hidden(X6,X7)
        | ~ r2_hidden(X8,X9) )
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f362,f49])).

fof(f362,plain,
    ( ! [X6,X8,X7,X9] :
        ( ~ r2_hidden(X6,X7)
        | ~ r2_hidden(X8,X9)
        | r2_hidden(k4_tarski(k4_tarski(sK0,X6),X8),k2_zfmisc_1(k2_zfmisc_1(sK3,X7),X9)) )
    | ~ spl7_6 ),
    inference(resolution,[],[f238,f52])).

fof(f238,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK0,X0),k2_zfmisc_1(sK3,X1))
        | ~ r2_hidden(X0,X1) )
    | ~ spl7_6 ),
    inference(resolution,[],[f85,f52])).

fof(f85,plain,
    ( r2_hidden(sK0,sK3)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl7_6
  <=> r2_hidden(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f555,plain,
    ( ~ spl7_87
    | ~ spl7_82 ),
    inference(avatar_split_clause,[],[f538,f531,f553])).

fof(f553,plain,
    ( spl7_87
  <=> ~ r2_hidden(k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,sK3)),k4_tarski(sK2,k4_tarski(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_87])])).

fof(f538,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,sK3)),k4_tarski(sK2,k4_tarski(sK2,sK0)))
    | ~ spl7_82 ),
    inference(resolution,[],[f532,f43])).

fof(f548,plain,
    ( ~ spl7_85
    | ~ spl7_82 ),
    inference(avatar_split_clause,[],[f539,f531,f546])).

fof(f546,plain,
    ( spl7_85
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_85])])).

fof(f539,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,sK3)))
    | ~ spl7_82 ),
    inference(resolution,[],[f532,f47])).

fof(f533,plain,
    ( spl7_82
    | ~ spl7_18
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f331,f326,f130,f531])).

fof(f331,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,sK0)),k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,sK3)))
    | ~ spl7_18
    | ~ spl7_52 ),
    inference(resolution,[],[f327,f161])).

fof(f515,plain,
    ( ~ spl7_81
    | ~ spl7_76 ),
    inference(avatar_split_clause,[],[f498,f491,f513])).

fof(f513,plain,
    ( spl7_81
  <=> ~ r2_hidden(k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,sK4)),k4_tarski(sK2,k4_tarski(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_81])])).

fof(f498,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,sK4)),k4_tarski(sK2,k4_tarski(sK2,sK1)))
    | ~ spl7_76 ),
    inference(resolution,[],[f492,f43])).

fof(f508,plain,
    ( ~ spl7_79
    | ~ spl7_76 ),
    inference(avatar_split_clause,[],[f499,f491,f506])).

fof(f506,plain,
    ( spl7_79
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_79])])).

fof(f499,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,sK4)))
    | ~ spl7_76 ),
    inference(resolution,[],[f492,f47])).

fof(f493,plain,
    ( spl7_76
    | ~ spl7_18
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f302,f297,f130,f491])).

fof(f302,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,sK1)),k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,sK4)))
    | ~ spl7_18
    | ~ spl7_46 ),
    inference(resolution,[],[f298,f161])).

fof(f479,plain,
    ( ~ spl7_75
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f462,f455,f477])).

fof(f477,plain,
    ( spl7_75
  <=> ~ r2_hidden(k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,sK5)),k4_tarski(sK2,k4_tarski(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).

fof(f462,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,sK5)),k4_tarski(sK2,k4_tarski(sK2,sK2)))
    | ~ spl7_70 ),
    inference(resolution,[],[f456,f43])).

fof(f472,plain,
    ( ~ spl7_73
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f463,f455,f470])).

fof(f470,plain,
    ( spl7_73
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).

fof(f463,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,sK5)))
    | ~ spl7_70 ),
    inference(resolution,[],[f456,f47])).

fof(f457,plain,
    ( spl7_70
    | ~ spl7_18
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f266,f215,f130,f455])).

fof(f215,plain,
    ( spl7_32
  <=> r2_hidden(k4_tarski(sK2,sK2),k2_zfmisc_1(sK5,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f266,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK2,sK2)),k2_zfmisc_1(sK5,k2_zfmisc_1(sK5,sK5)))
    | ~ spl7_18
    | ~ spl7_32 ),
    inference(resolution,[],[f216,f161])).

fof(f216,plain,
    ( r2_hidden(k4_tarski(sK2,sK2),k2_zfmisc_1(sK5,sK5))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f215])).

fof(f443,plain,
    ( ~ spl7_69
    | ~ spl7_64 ),
    inference(avatar_split_clause,[],[f426,f419,f441])).

fof(f441,plain,
    ( spl7_69
  <=> ~ r2_hidden(k2_zfmisc_1(sK5,k2_zfmisc_1(sK3,sK5)),k4_tarski(sK2,k4_tarski(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_69])])).

fof(f426,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK5,k2_zfmisc_1(sK3,sK5)),k4_tarski(sK2,k4_tarski(sK0,sK2)))
    | ~ spl7_64 ),
    inference(resolution,[],[f420,f43])).

fof(f436,plain,
    ( ~ spl7_67
    | ~ spl7_64 ),
    inference(avatar_split_clause,[],[f427,f419,f434])).

fof(f434,plain,
    ( spl7_67
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK5,k2_zfmisc_1(sK3,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).

fof(f427,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK5,k2_zfmisc_1(sK3,sK5)))
    | ~ spl7_64 ),
    inference(resolution,[],[f420,f47])).

fof(f421,plain,
    ( spl7_64
    | ~ spl7_18
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f251,f202,f130,f419])).

fof(f251,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK0,sK2)),k2_zfmisc_1(sK5,k2_zfmisc_1(sK3,sK5)))
    | ~ spl7_18
    | ~ spl7_30 ),
    inference(resolution,[],[f203,f161])).

fof(f403,plain,
    ( ~ spl7_63
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f386,f379,f401])).

fof(f401,plain,
    ( spl7_63
  <=> ~ r2_hidden(k2_zfmisc_1(sK5,k2_zfmisc_1(sK3,sK3)),k4_tarski(sK2,k4_tarski(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f386,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK5,k2_zfmisc_1(sK3,sK3)),k4_tarski(sK2,k4_tarski(sK0,sK0)))
    | ~ spl7_58 ),
    inference(resolution,[],[f380,f43])).

fof(f396,plain,
    ( ~ spl7_61
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f387,f379,f394])).

fof(f394,plain,
    ( spl7_61
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK5,k2_zfmisc_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).

fof(f387,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK5,k2_zfmisc_1(sK3,sK3)))
    | ~ spl7_58 ),
    inference(resolution,[],[f380,f47])).

fof(f381,plain,
    ( spl7_58
    | ~ spl7_18
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f243,f173,f130,f379])).

fof(f173,plain,
    ( spl7_24
  <=> r2_hidden(k4_tarski(sK0,sK0),k2_zfmisc_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f243,plain,
    ( r2_hidden(k4_tarski(sK2,k4_tarski(sK0,sK0)),k2_zfmisc_1(sK5,k2_zfmisc_1(sK3,sK3)))
    | ~ spl7_18
    | ~ spl7_24 ),
    inference(resolution,[],[f174,f161])).

fof(f174,plain,
    ( r2_hidden(k4_tarski(sK0,sK0),k2_zfmisc_1(sK3,sK3))
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f173])).

fof(f350,plain,
    ( ~ spl7_57
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f333,f326,f348])).

fof(f348,plain,
    ( spl7_57
  <=> ~ r2_hidden(k2_zfmisc_1(sK5,sK3),k4_tarski(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).

fof(f333,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK5,sK3),k4_tarski(sK2,sK0))
    | ~ spl7_52 ),
    inference(resolution,[],[f327,f43])).

fof(f343,plain,
    ( ~ spl7_55
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f334,f326,f341])).

fof(f341,plain,
    ( spl7_55
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK5,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f334,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK5,sK3))
    | ~ spl7_52 ),
    inference(resolution,[],[f327,f47])).

fof(f328,plain,
    ( spl7_52
    | ~ spl7_6
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f237,f130,f84,f326])).

fof(f237,plain,
    ( r2_hidden(k4_tarski(sK2,sK0),k2_zfmisc_1(sK5,sK3))
    | ~ spl7_6
    | ~ spl7_18 ),
    inference(resolution,[],[f85,f161])).

fof(f321,plain,
    ( ~ spl7_51
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f304,f297,f319])).

fof(f319,plain,
    ( spl7_51
  <=> ~ r2_hidden(k2_zfmisc_1(sK5,sK4),k4_tarski(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f304,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK5,sK4),k4_tarski(sK2,sK1))
    | ~ spl7_46 ),
    inference(resolution,[],[f298,f43])).

fof(f314,plain,
    ( ~ spl7_49
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f305,f297,f312])).

fof(f312,plain,
    ( spl7_49
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK5,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f305,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK5,sK4))
    | ~ spl7_46 ),
    inference(resolution,[],[f298,f47])).

fof(f299,plain,
    ( spl7_46
    | ~ spl7_12
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f218,f130,f107,f297])).

fof(f218,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),k2_zfmisc_1(sK5,sK4))
    | ~ spl7_12
    | ~ spl7_18 ),
    inference(resolution,[],[f108,f161])).

fof(f292,plain,
    ( ~ spl7_45
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f268,f215,f290])).

fof(f290,plain,
    ( spl7_45
  <=> ~ r2_hidden(k2_zfmisc_1(sK5,sK5),k4_tarski(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f268,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK5,sK5),k4_tarski(sK2,sK2))
    | ~ spl7_32 ),
    inference(resolution,[],[f216,f43])).

fof(f285,plain,
    ( ~ spl7_43
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f253,f202,f283])).

fof(f283,plain,
    ( spl7_43
  <=> ~ r2_hidden(k2_zfmisc_1(sK3,sK5),k4_tarski(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f253,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK3,sK5),k4_tarski(sK0,sK2))
    | ~ spl7_30 ),
    inference(resolution,[],[f203,f43])).

fof(f278,plain,
    ( ~ spl7_41
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f269,f215,f276])).

fof(f276,plain,
    ( spl7_41
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK5,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f269,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK5,sK5))
    | ~ spl7_32 ),
    inference(resolution,[],[f216,f47])).

fof(f263,plain,
    ( ~ spl7_39
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f254,f202,f261])).

fof(f261,plain,
    ( spl7_39
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f254,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK3,sK5))
    | ~ spl7_30 ),
    inference(resolution,[],[f203,f47])).

fof(f236,plain,
    ( spl7_6
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f177,f173,f84])).

fof(f177,plain,
    ( r2_hidden(sK0,sK3)
    | ~ spl7_24 ),
    inference(resolution,[],[f174,f50])).

fof(f235,plain,
    ( ~ spl7_37
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f220,f107,f233])).

fof(f233,plain,
    ( spl7_37
  <=> ~ r2_hidden(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f220,plain,
    ( ~ r2_hidden(sK4,sK1)
    | ~ spl7_12 ),
    inference(resolution,[],[f108,f43])).

fof(f228,plain,
    ( ~ spl7_35
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f221,f107,f226])).

fof(f226,plain,
    ( spl7_35
  <=> ~ v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f221,plain,
    ( ~ v1_xboole_0(sK4)
    | ~ spl7_12 ),
    inference(resolution,[],[f108,f47])).

fof(f217,plain,
    ( spl7_32
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f208,f130,f215])).

fof(f208,plain,
    ( r2_hidden(k4_tarski(sK2,sK2),k2_zfmisc_1(sK5,sK5))
    | ~ spl7_18 ),
    inference(resolution,[],[f161,f131])).

fof(f210,plain,
    ( ~ spl7_5
    | ~ spl7_7
    | ~ spl7_13
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f39,f127,f104,f81,f75])).

fof(f127,plain,
    ( spl7_19
  <=> ~ r2_hidden(sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f39,plain,
    ( ~ r2_hidden(sK2,sK5)
    | ~ r2_hidden(sK1,sK4)
    | ~ r2_hidden(sK0,sK3)
    | ~ r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ~ r2_hidden(sK2,sK5)
      | ~ r2_hidden(sK1,sK4)
      | ~ r2_hidden(sK0,sK3)
      | ~ r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) )
    & ( ( r2_hidden(sK2,sK5)
        & r2_hidden(sK1,sK4)
        & r2_hidden(sK0,sK3) )
      | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f29,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ( ~ r2_hidden(X2,X5)
          | ~ r2_hidden(X1,X4)
          | ~ r2_hidden(X0,X3)
          | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) )
        & ( ( r2_hidden(X2,X5)
            & r2_hidden(X1,X4)
            & r2_hidden(X0,X3) )
          | r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) )
   => ( ( ~ r2_hidden(sK2,sK5)
        | ~ r2_hidden(sK1,sK4)
        | ~ r2_hidden(sK0,sK3)
        | ~ r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) )
      & ( ( r2_hidden(sK2,sK5)
          & r2_hidden(sK1,sK4)
          & r2_hidden(sK0,sK3) )
        | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( ~ r2_hidden(X2,X5)
        | ~ r2_hidden(X1,X4)
        | ~ r2_hidden(X0,X3)
        | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) )
      & ( ( r2_hidden(X2,X5)
          & r2_hidden(X1,X4)
          & r2_hidden(X0,X3) )
        | r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( ~ r2_hidden(X2,X5)
        | ~ r2_hidden(X1,X4)
        | ~ r2_hidden(X0,X3)
        | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) )
      & ( ( r2_hidden(X2,X5)
          & r2_hidden(X1,X4)
          & r2_hidden(X0,X3) )
        | r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
    <~> ( r2_hidden(X2,X5)
        & r2_hidden(X1,X4)
        & r2_hidden(X0,X3) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
      <=> ( r2_hidden(X2,X5)
          & r2_hidden(X1,X4)
          & r2_hidden(X0,X3) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
    <=> ( r2_hidden(X2,X5)
        & r2_hidden(X1,X4)
        & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t73_mcart_1.p',t73_mcart_1)).

fof(f206,plain,
    ( spl7_7
    | ~ spl7_24 ),
    inference(avatar_contradiction_clause,[],[f205])).

fof(f205,plain,
    ( $false
    | ~ spl7_7
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f82,f177])).

fof(f204,plain,
    ( spl7_30
    | ~ spl7_6
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f167,f130,f84,f202])).

fof(f167,plain,
    ( r2_hidden(k4_tarski(sK0,sK2),k2_zfmisc_1(sK3,sK5))
    | ~ spl7_6
    | ~ spl7_18 ),
    inference(resolution,[],[f160,f131])).

fof(f160,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,X3)
        | r2_hidden(k4_tarski(sK0,X2),k2_zfmisc_1(sK3,X3)) )
    | ~ spl7_6 ),
    inference(resolution,[],[f52,f85])).

fof(f197,plain,
    ( ~ spl7_29
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f180,f173,f195])).

fof(f195,plain,
    ( spl7_29
  <=> ~ r2_hidden(k2_zfmisc_1(sK3,sK3),k4_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f180,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK3,sK3),k4_tarski(sK0,sK0))
    | ~ spl7_24 ),
    inference(resolution,[],[f174,f43])).

fof(f190,plain,
    ( ~ spl7_27
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f181,f173,f188])).

fof(f188,plain,
    ( spl7_27
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f181,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK3,sK3))
    | ~ spl7_24 ),
    inference(resolution,[],[f174,f47])).

fof(f175,plain,
    ( spl7_24
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f166,f84,f173])).

fof(f166,plain,
    ( r2_hidden(k4_tarski(sK0,sK0),k2_zfmisc_1(sK3,sK3))
    | ~ spl7_6 ),
    inference(resolution,[],[f160,f85])).

fof(f158,plain,
    ( ~ spl7_23
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f143,f130,f156])).

fof(f156,plain,
    ( spl7_23
  <=> ~ r2_hidden(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f143,plain,
    ( ~ r2_hidden(sK5,sK2)
    | ~ spl7_18 ),
    inference(resolution,[],[f131,f43])).

fof(f151,plain,
    ( ~ spl7_21
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f144,f130,f149])).

fof(f149,plain,
    ( spl7_21
  <=> ~ v1_xboole_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f144,plain,
    ( ~ v1_xboole_0(sK5)
    | ~ spl7_18 ),
    inference(resolution,[],[f131,f47])).

fof(f142,plain,
    ( spl7_18
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f141,f78,f130])).

fof(f141,plain,
    ( r2_hidden(sK2,sK5)
    | ~ spl7_4 ),
    inference(resolution,[],[f139,f79])).

fof(f139,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(k3_mcart_1(X3,X4,X5),k3_zfmisc_1(X0,X1,X2))
      | r2_hidden(X5,X2) ) ),
    inference(superposition,[],[f137,f49])).

fof(f137,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k3_mcart_1(X0,X1,X2),k2_zfmisc_1(X3,X4))
      | r2_hidden(X2,X4) ) ),
    inference(superposition,[],[f51,f48])).

fof(f132,plain,
    ( spl7_4
    | spl7_18 ),
    inference(avatar_split_clause,[],[f38,f130,f78])).

fof(f38,plain,
    ( r2_hidden(sK2,sK5)
    | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f31])).

fof(f125,plain,
    ( ~ spl7_17
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f110,f78,f123])).

fof(f123,plain,
    ( spl7_17
  <=> ~ r2_hidden(k3_zfmisc_1(sK3,sK4,sK5),k3_mcart_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f110,plain,
    ( ~ r2_hidden(k3_zfmisc_1(sK3,sK4,sK5),k3_mcart_1(sK0,sK1,sK2))
    | ~ spl7_4 ),
    inference(resolution,[],[f79,f43])).

fof(f118,plain,
    ( ~ spl7_15
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f111,f78,f116])).

fof(f116,plain,
    ( spl7_15
  <=> ~ v1_xboole_0(k3_zfmisc_1(sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f111,plain,
    ( ~ v1_xboole_0(k3_zfmisc_1(sK3,sK4,sK5))
    | ~ spl7_4 ),
    inference(resolution,[],[f79,f47])).

fof(f109,plain,
    ( spl7_4
    | spl7_12 ),
    inference(avatar_split_clause,[],[f37,f107,f78])).

fof(f37,plain,
    ( r2_hidden(sK1,sK4)
    | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f31])).

fof(f102,plain,
    ( ~ spl7_11
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f87,f84,f100])).

fof(f100,plain,
    ( spl7_11
  <=> ~ r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f87,plain,
    ( ~ r2_hidden(sK3,sK0)
    | ~ spl7_6 ),
    inference(resolution,[],[f85,f43])).

fof(f95,plain,
    ( ~ spl7_9
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f88,f84,f93])).

fof(f93,plain,
    ( spl7_9
  <=> ~ v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f88,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl7_6 ),
    inference(resolution,[],[f85,f47])).

fof(f86,plain,
    ( spl7_4
    | spl7_6 ),
    inference(avatar_split_clause,[],[f36,f84,f78])).

fof(f36,plain,
    ( r2_hidden(sK0,sK3)
    | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f31])).

fof(f67,plain,
    ( spl7_2
    | ~ spl7_0 ),
    inference(avatar_split_clause,[],[f60,f57,f65])).

fof(f65,plain,
    ( spl7_2
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f57,plain,
    ( spl7_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f60,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl7_0 ),
    inference(resolution,[],[f41,f58])).

fof(f58,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f57])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t73_mcart_1.p',t6_boole)).

fof(f59,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f40,f57])).

fof(f40,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t73_mcart_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
