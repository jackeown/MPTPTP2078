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
% DateTime   : Thu Dec  3 12:46:58 EST 2020

% Result     : Theorem 6.30s
% Output     : Refutation 6.30s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 263 expanded)
%              Number of leaves         :   41 ( 121 expanded)
%              Depth                    :    8
%              Number of atoms          :  513 ( 948 expanded)
%              Number of equality atoms :  144 ( 312 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6725,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f88,f92,f102,f106,f117,f121,f125,f141,f145,f149,f157,f163,f208,f244,f287,f302,f619,f1111,f1203,f1632,f3077,f5089,f5351,f5558,f6601,f6724])).

fof(f6724,plain,
    ( spl10_4
    | ~ spl10_20
    | spl10_129
    | ~ spl10_169 ),
    inference(avatar_contradiction_clause,[],[f6723])).

fof(f6723,plain,
    ( $false
    | spl10_4
    | ~ spl10_20
    | spl10_129
    | ~ spl10_169 ),
    inference(subsumption_resolution,[],[f5439,f6701])).

fof(f6701,plain,
    ( ~ r2_hidden(sK9(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))
    | spl10_129
    | ~ spl10_169 ),
    inference(unit_resulting_resolution,[],[f3076,f6600])).

fof(f6600,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK2))
        | sK1 = X0 )
    | ~ spl10_169 ),
    inference(avatar_component_clause,[],[f6599])).

fof(f6599,plain,
    ( spl10_169
  <=> ! [X0] :
        ( sK1 = X0
        | ~ r2_hidden(X0,k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_169])])).

fof(f3076,plain,
    ( sK1 != sK9(sK1,k2_relat_1(sK2))
    | spl10_129 ),
    inference(avatar_component_clause,[],[f3074])).

fof(f3074,plain,
    ( spl10_129
  <=> sK1 = sK9(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_129])])).

fof(f5439,plain,
    ( r2_hidden(sK9(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))
    | spl10_4
    | ~ spl10_20
    | spl10_129 ),
    inference(unit_resulting_resolution,[],[f3076,f87,f207])).

fof(f207,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK9(X0,X1),X1)
        | sK9(X0,X1) = X0
        | k1_tarski(X0) = X1 )
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl10_20
  <=> ! [X1,X0] :
        ( k1_tarski(X0) = X1
        | sK9(X0,X1) = X0
        | r2_hidden(sK9(X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f87,plain,
    ( k1_tarski(sK1) != k2_relat_1(sK2)
    | spl10_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl10_4
  <=> k1_tarski(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f6601,plain,
    ( spl10_169
    | ~ spl10_15
    | ~ spl10_86 ),
    inference(avatar_split_clause,[],[f1206,f1201,f147,f6599])).

fof(f147,plain,
    ( spl10_15
  <=> ! [X5,X0] :
        ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
        | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f1201,plain,
    ( spl10_86
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | sK1 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_86])])).

fof(f1206,plain,
    ( ! [X0] :
        ( sK1 = X0
        | ~ r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl10_15
    | ~ spl10_86 ),
    inference(resolution,[],[f1202,f148])).

fof(f148,plain,
    ( ! [X0,X5] :
        ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
        | ~ r2_hidden(X5,k2_relat_1(X0)) )
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f147])).

fof(f1202,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | sK1 = X1 )
    | ~ spl10_86 ),
    inference(avatar_component_clause,[],[f1201])).

fof(f5558,plain,
    ( spl10_19
    | ~ spl10_7
    | ~ spl10_102 ),
    inference(avatar_split_clause,[],[f4838,f1630,f99,f165])).

fof(f165,plain,
    ( spl10_19
  <=> r2_hidden(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f99,plain,
    ( spl10_7
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f1630,plain,
    ( spl10_102
  <=> ! [X5,X4] :
        ( ~ r2_hidden(X4,X5)
        | r2_hidden(sK1,k2_relat_1(X5))
        | ~ r2_hidden(X4,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_102])])).

fof(f4838,plain,
    ( r2_hidden(sK1,k2_relat_1(sK2))
    | ~ spl10_7
    | ~ spl10_102 ),
    inference(unit_resulting_resolution,[],[f101,f101,f1631])).

fof(f1631,plain,
    ( ! [X4,X5] :
        ( r2_hidden(sK1,k2_relat_1(X5))
        | ~ r2_hidden(X4,X5)
        | ~ r2_hidden(X4,sK2) )
    | ~ spl10_102 ),
    inference(avatar_component_clause,[],[f1630])).

fof(f101,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f5351,plain,
    ( spl10_3
    | ~ spl10_20
    | ~ spl10_79
    | spl10_140 ),
    inference(avatar_contradiction_clause,[],[f5350])).

fof(f5350,plain,
    ( $false
    | spl10_3
    | ~ spl10_20
    | ~ spl10_79
    | spl10_140 ),
    inference(subsumption_resolution,[],[f5341,f5331])).

fof(f5331,plain,
    ( ~ r2_hidden(sK9(sK0,k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl10_79
    | spl10_140 ),
    inference(unit_resulting_resolution,[],[f5088,f1110])).

fof(f1110,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relat_1(sK2))
        | sK0 = X3 )
    | ~ spl10_79 ),
    inference(avatar_component_clause,[],[f1109])).

fof(f1109,plain,
    ( spl10_79
  <=> ! [X3] :
        ( sK0 = X3
        | ~ r2_hidden(X3,k1_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_79])])).

fof(f5088,plain,
    ( sK0 != sK9(sK0,k1_relat_1(sK2))
    | spl10_140 ),
    inference(avatar_component_clause,[],[f5086])).

fof(f5086,plain,
    ( spl10_140
  <=> sK0 = sK9(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_140])])).

fof(f5341,plain,
    ( r2_hidden(sK9(sK0,k1_relat_1(sK2)),k1_relat_1(sK2))
    | spl10_3
    | ~ spl10_20
    | spl10_140 ),
    inference(unit_resulting_resolution,[],[f83,f5088,f207])).

fof(f83,plain,
    ( k1_tarski(sK0) != k1_relat_1(sK2)
    | spl10_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl10_3
  <=> k1_tarski(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f5089,plain,
    ( ~ spl10_140
    | spl10_3
    | ~ spl10_18
    | ~ spl10_25 ),
    inference(avatar_split_clause,[],[f280,f241,f161,f81,f5086])).

fof(f161,plain,
    ( spl10_18
  <=> ! [X1,X0] :
        ( k1_tarski(X0) = X1
        | sK9(X0,X1) != X0
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f241,plain,
    ( spl10_25
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f280,plain,
    ( sK0 != sK9(sK0,k1_relat_1(sK2))
    | spl10_3
    | ~ spl10_18
    | ~ spl10_25 ),
    inference(unit_resulting_resolution,[],[f83,f243,f162])).

fof(f162,plain,
    ( ! [X0,X1] :
        ( sK9(X0,X1) != X0
        | k1_tarski(X0) = X1
        | ~ r2_hidden(X0,X1) )
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f161])).

fof(f243,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl10_25 ),
    inference(avatar_component_clause,[],[f241])).

fof(f3077,plain,
    ( ~ spl10_129
    | spl10_4
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(avatar_split_clause,[],[f210,f165,f161,f85,f3074])).

fof(f210,plain,
    ( sK1 != sK9(sK1,k2_relat_1(sK2))
    | spl10_4
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(unit_resulting_resolution,[],[f87,f167,f162])).

fof(f167,plain,
    ( r2_hidden(sK1,k2_relat_1(sK2))
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f165])).

fof(f1632,plain,
    ( spl10_102
    | ~ spl10_10
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f293,f285,f119,f1630])).

fof(f119,plain,
    ( spl10_10
  <=> ! [X5,X0,X6] :
        ( r2_hidden(X5,k2_relat_1(X0))
        | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f285,plain,
    ( spl10_30
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | k4_tarski(sK0,sK1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f293,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,X5)
        | r2_hidden(sK1,k2_relat_1(X5))
        | ~ r2_hidden(X4,sK2) )
    | ~ spl10_10
    | ~ spl10_30 ),
    inference(superposition,[],[f120,f286])).

fof(f286,plain,
    ( ! [X0] :
        ( k4_tarski(sK0,sK1) = X0
        | ~ r2_hidden(X0,sK2) )
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f285])).

fof(f120,plain,
    ( ! [X6,X0,X5] :
        ( ~ r2_hidden(k4_tarski(X6,X5),X0)
        | r2_hidden(X5,k2_relat_1(X0)) )
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f1203,plain,
    ( spl10_86
    | ~ spl10_2
    | ~ spl10_52 ),
    inference(avatar_split_clause,[],[f630,f617,f76,f1201])).

fof(f76,plain,
    ( spl10_2
  <=> sK2 = k1_tarski(k4_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f617,plain,
    ( spl10_52
  <=> ! [X1,X3,X0,X2] :
        ( ~ r2_hidden(k4_tarski(X2,X3),k1_tarski(k4_tarski(X0,X1)))
        | X1 = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_52])])).

fof(f630,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | sK1 = X1 )
    | ~ spl10_2
    | ~ spl10_52 ),
    inference(superposition,[],[f618,f78])).

fof(f78,plain,
    ( sK2 = k1_tarski(k4_tarski(sK0,sK1))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f618,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(k4_tarski(X2,X3),k1_tarski(k4_tarski(X0,X1)))
        | X1 = X3 )
    | ~ spl10_52 ),
    inference(avatar_component_clause,[],[f617])).

fof(f1111,plain,
    ( spl10_79
    | ~ spl10_14
    | ~ spl10_31 ),
    inference(avatar_split_clause,[],[f308,f300,f143,f1109])).

fof(f143,plain,
    ( spl10_14
  <=> ! [X5,X0] :
        ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
        | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f300,plain,
    ( spl10_31
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | sK0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).

fof(f308,plain,
    ( ! [X3] :
        ( sK0 = X3
        | ~ r2_hidden(X3,k1_relat_1(sK2)) )
    | ~ spl10_14
    | ~ spl10_31 ),
    inference(resolution,[],[f301,f144])).

fof(f144,plain,
    ( ! [X0,X5] :
        ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
        | ~ r2_hidden(X5,k1_relat_1(X0)) )
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f143])).

fof(f301,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | sK0 = X0 )
    | ~ spl10_31 ),
    inference(avatar_component_clause,[],[f300])).

fof(f619,plain,
    ( spl10_52
    | ~ spl10_11
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f176,f139,f123,f617])).

fof(f123,plain,
    ( spl10_11
  <=> ! [X1,X0] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f139,plain,
    ( spl10_13
  <=> ! [X1,X3,X0,X2] :
        ( X1 = X3
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f176,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(k4_tarski(X2,X3),k1_tarski(k4_tarski(X0,X1)))
        | X1 = X3 )
    | ~ spl10_11
    | ~ spl10_13 ),
    inference(superposition,[],[f140,f124])).

fof(f124,plain,
    ( ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f123])).

fof(f140,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 = X3 )
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f139])).

fof(f302,plain,
    ( spl10_31
    | ~ spl10_2
    | ~ spl10_17 ),
    inference(avatar_split_clause,[],[f204,f155,f76,f300])).

fof(f155,plain,
    ( spl10_17
  <=> ! [X1,X3,X0,X2] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k1_tarski(k4_tarski(X2,X3)))
        | X0 = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f204,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | sK0 = X0 )
    | ~ spl10_2
    | ~ spl10_17 ),
    inference(superposition,[],[f156,f78])).

fof(f156,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k1_tarski(k4_tarski(X2,X3)))
        | X0 = X2 )
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f155])).

fof(f287,plain,
    ( spl10_30
    | ~ spl10_2
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f113,f104,f76,f285])).

fof(f104,plain,
    ( spl10_8
  <=> ! [X3,X0] :
        ( X0 = X3
        | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f113,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | k4_tarski(sK0,sK1) = X0 )
    | ~ spl10_2
    | ~ spl10_8 ),
    inference(superposition,[],[f105,f78])).

fof(f105,plain,
    ( ! [X0,X3] :
        ( ~ r2_hidden(X3,k1_tarski(X0))
        | X0 = X3 )
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f104])).

fof(f244,plain,
    ( spl10_25
    | ~ spl10_7
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f131,f115,f99,f241])).

fof(f115,plain,
    ( spl10_9
  <=> ! [X5,X0,X6] :
        ( r2_hidden(X5,k1_relat_1(X0))
        | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f131,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl10_7
    | ~ spl10_9 ),
    inference(unit_resulting_resolution,[],[f101,f116])).

fof(f116,plain,
    ( ! [X6,X0,X5] :
        ( ~ r2_hidden(k4_tarski(X5,X6),X0)
        | r2_hidden(X5,k1_relat_1(X0)) )
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f115])).

fof(f208,plain,(
    spl10_20 ),
    inference(avatar_split_clause,[],[f49,f206])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK9(X0,X1) = X0
      | r2_hidden(sK9(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK9(X0,X1) != X0
            | ~ r2_hidden(sK9(X0,X1),X1) )
          & ( sK9(X0,X1) = X0
            | r2_hidden(sK9(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK9(X0,X1) != X0
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( sK9(X0,X1) = X0
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f163,plain,(
    spl10_18 ),
    inference(avatar_split_clause,[],[f67,f161])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK9(X0,X1) != X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(inner_rewriting,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK9(X0,X1) != X0
      | ~ r2_hidden(sK9(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f157,plain,(
    spl10_17 ),
    inference(avatar_split_clause,[],[f69,f155])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k1_tarski(k4_tarski(X2,X3)))
      | X0 = X2 ) ),
    inference(forward_demodulation,[],[f54,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
        | X1 != X3
        | X0 != X2 )
      & ( ( X1 = X3
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
        | X1 != X3
        | X0 != X2 )
      & ( ( X1 = X3
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <=> ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(f149,plain,(
    spl10_15 ),
    inference(avatar_split_clause,[],[f60,f147])).

fof(f60,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f21,f24,f23,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f145,plain,(
    spl10_14 ),
    inference(avatar_split_clause,[],[f58,f143])).

fof(f58,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f15,f18,f17,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f141,plain,(
    spl10_13 ),
    inference(avatar_split_clause,[],[f52,f139])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f125,plain,(
    spl10_11 ),
    inference(avatar_split_clause,[],[f38,f123])).

fof(f121,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f59,f119])).

fof(f59,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f117,plain,(
    spl10_9 ),
    inference(avatar_split_clause,[],[f57,f115])).

fof(f57,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f106,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f63,f104])).

fof(f63,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f102,plain,
    ( spl10_7
    | ~ spl10_2
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f93,f90,f76,f99])).

fof(f90,plain,
    ( spl10_5
  <=> ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f93,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl10_2
    | ~ spl10_5 ),
    inference(superposition,[],[f91,f78])).

fof(f91,plain,
    ( ! [X3] : r2_hidden(X3,k1_tarski(X3))
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f92,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f62,f90])).

fof(f62,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f88,plain,
    ( ~ spl10_3
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f36,f85,f81])).

fof(f36,plain,
    ( k1_tarski(sK1) != k2_relat_1(sK2)
    | k1_tarski(sK0) != k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( k1_tarski(sK1) != k2_relat_1(sK2)
      | k1_tarski(sK0) != k1_relat_1(sK2) )
    & sK2 = k1_tarski(k4_tarski(sK0,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_tarski(X1) != k2_relat_1(X2)
          | k1_tarski(X0) != k1_relat_1(X2) )
        & k1_tarski(k4_tarski(X0,X1)) = X2
        & v1_relat_1(X2) )
   => ( ( k1_tarski(sK1) != k2_relat_1(sK2)
        | k1_tarski(sK0) != k1_relat_1(sK2) )
      & sK2 = k1_tarski(k4_tarski(sK0,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( k1_tarski(X1) != k2_relat_1(X2)
        | k1_tarski(X0) != k1_relat_1(X2) )
      & k1_tarski(k4_tarski(X0,X1)) = X2
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( k1_tarski(X1) != k2_relat_1(X2)
        | k1_tarski(X0) != k1_relat_1(X2) )
      & k1_tarski(k4_tarski(X0,X1)) = X2
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( k1_tarski(k4_tarski(X0,X1)) = X2
         => ( k1_tarski(X1) = k2_relat_1(X2)
            & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( k1_tarski(k4_tarski(X0,X1)) = X2
       => ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relat_1)).

fof(f79,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f35,f76])).

fof(f35,plain,(
    sK2 = k1_tarski(k4_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:07:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (709)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.51  % (722)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.51  % (708)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.51  % (721)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.51  % (720)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (712)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (711)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (735)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (730)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.52  % (713)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (731)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (718)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (736)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.53  % (710)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (715)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.53  % (729)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.22/0.53  % (724)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.22/0.54  % (739)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.22/0.54  % (726)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.22/0.54  % (733)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.22/0.54  % (739)Refutation not found, incomplete strategy% (739)------------------------------
% 1.22/0.54  % (739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.54  % (739)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.54  
% 1.22/0.54  % (739)Memory used [KB]: 1663
% 1.22/0.54  % (739)Time elapsed: 0.132 s
% 1.22/0.54  % (739)------------------------------
% 1.22/0.54  % (739)------------------------------
% 1.22/0.54  % (724)Refutation not found, incomplete strategy% (724)------------------------------
% 1.22/0.54  % (724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.54  % (707)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.22/0.54  % (724)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.54  % (728)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.22/0.54  % (734)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.22/0.54  
% 1.22/0.54  % (724)Memory used [KB]: 10618
% 1.22/0.54  % (724)Time elapsed: 0.130 s
% 1.22/0.54  % (724)------------------------------
% 1.22/0.54  % (724)------------------------------
% 1.22/0.54  % (719)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.22/0.55  % (737)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.22/0.55  % (717)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.50/0.56  % (714)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.50/0.56  % (727)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.50/0.57  % (732)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.50/0.57  % (723)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 2.17/0.65  % (741)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.17/0.66  % (742)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.29/0.81  % (709)Time limit reached!
% 3.29/0.81  % (709)------------------------------
% 3.29/0.81  % (709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.29/0.81  % (709)Termination reason: Time limit
% 3.29/0.81  % (709)Termination phase: Saturation
% 3.29/0.81  
% 3.29/0.81  % (709)Memory used [KB]: 7291
% 3.29/0.81  % (709)Time elapsed: 0.400 s
% 3.29/0.81  % (709)------------------------------
% 3.29/0.81  % (709)------------------------------
% 3.65/0.87  % (733)Time limit reached!
% 3.65/0.87  % (733)------------------------------
% 3.65/0.87  % (733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.65/0.87  % (733)Termination reason: Time limit
% 3.65/0.87  
% 3.65/0.87  % (733)Memory used [KB]: 14839
% 3.65/0.87  % (733)Time elapsed: 0.430 s
% 3.65/0.87  % (733)------------------------------
% 3.65/0.87  % (733)------------------------------
% 3.65/0.94  % (743)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 4.36/0.95  % (713)Time limit reached!
% 4.36/0.95  % (713)------------------------------
% 4.36/0.95  % (713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.36/0.96  % (722)Time limit reached!
% 4.36/0.96  % (722)------------------------------
% 4.36/0.96  % (722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.36/0.96  % (722)Termination reason: Time limit
% 4.36/0.96  
% 4.36/0.96  % (722)Memory used [KB]: 6908
% 4.36/0.96  % (722)Time elapsed: 0.514 s
% 4.36/0.96  % (722)------------------------------
% 4.36/0.96  % (722)------------------------------
% 4.36/0.96  % (713)Termination reason: Time limit
% 4.36/0.96  
% 4.36/0.96  % (713)Memory used [KB]: 14583
% 4.36/0.96  % (713)Time elapsed: 0.516 s
% 4.36/0.96  % (713)------------------------------
% 4.36/0.96  % (713)------------------------------
% 4.36/0.99  % (744)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 5.45/1.06  % (714)Time limit reached!
% 5.45/1.06  % (714)------------------------------
% 5.45/1.06  % (714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.45/1.08  % (714)Termination reason: Time limit
% 5.45/1.08  
% 5.45/1.08  % (714)Memory used [KB]: 6140
% 5.45/1.08  % (714)Time elapsed: 0.629 s
% 5.45/1.08  % (714)------------------------------
% 5.45/1.08  % (714)------------------------------
% 5.45/1.09  % (745)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 5.87/1.12  % (746)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 6.30/1.21  % (747)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 6.30/1.23  % (741)Refutation found. Thanks to Tanya!
% 6.30/1.23  % SZS status Theorem for theBenchmark
% 6.30/1.23  % SZS output start Proof for theBenchmark
% 6.30/1.23  fof(f6725,plain,(
% 6.30/1.23    $false),
% 6.30/1.23    inference(avatar_sat_refutation,[],[f79,f88,f92,f102,f106,f117,f121,f125,f141,f145,f149,f157,f163,f208,f244,f287,f302,f619,f1111,f1203,f1632,f3077,f5089,f5351,f5558,f6601,f6724])).
% 6.30/1.23  fof(f6724,plain,(
% 6.30/1.23    spl10_4 | ~spl10_20 | spl10_129 | ~spl10_169),
% 6.30/1.23    inference(avatar_contradiction_clause,[],[f6723])).
% 6.30/1.23  fof(f6723,plain,(
% 6.30/1.23    $false | (spl10_4 | ~spl10_20 | spl10_129 | ~spl10_169)),
% 6.30/1.23    inference(subsumption_resolution,[],[f5439,f6701])).
% 6.30/1.23  fof(f6701,plain,(
% 6.30/1.23    ~r2_hidden(sK9(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) | (spl10_129 | ~spl10_169)),
% 6.30/1.23    inference(unit_resulting_resolution,[],[f3076,f6600])).
% 6.30/1.23  fof(f6600,plain,(
% 6.30/1.23    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | sK1 = X0) ) | ~spl10_169),
% 6.30/1.23    inference(avatar_component_clause,[],[f6599])).
% 6.30/1.23  fof(f6599,plain,(
% 6.30/1.23    spl10_169 <=> ! [X0] : (sK1 = X0 | ~r2_hidden(X0,k2_relat_1(sK2)))),
% 6.30/1.23    introduced(avatar_definition,[new_symbols(naming,[spl10_169])])).
% 6.30/1.23  fof(f3076,plain,(
% 6.30/1.23    sK1 != sK9(sK1,k2_relat_1(sK2)) | spl10_129),
% 6.30/1.23    inference(avatar_component_clause,[],[f3074])).
% 6.30/1.23  fof(f3074,plain,(
% 6.30/1.23    spl10_129 <=> sK1 = sK9(sK1,k2_relat_1(sK2))),
% 6.30/1.23    introduced(avatar_definition,[new_symbols(naming,[spl10_129])])).
% 6.30/1.23  fof(f5439,plain,(
% 6.30/1.23    r2_hidden(sK9(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) | (spl10_4 | ~spl10_20 | spl10_129)),
% 6.30/1.23    inference(unit_resulting_resolution,[],[f3076,f87,f207])).
% 6.30/1.23  fof(f207,plain,(
% 6.30/1.23    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X1) | sK9(X0,X1) = X0 | k1_tarski(X0) = X1) ) | ~spl10_20),
% 6.30/1.23    inference(avatar_component_clause,[],[f206])).
% 6.30/1.23  fof(f206,plain,(
% 6.30/1.23    spl10_20 <=> ! [X1,X0] : (k1_tarski(X0) = X1 | sK9(X0,X1) = X0 | r2_hidden(sK9(X0,X1),X1))),
% 6.30/1.23    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).
% 6.30/1.23  fof(f87,plain,(
% 6.30/1.23    k1_tarski(sK1) != k2_relat_1(sK2) | spl10_4),
% 6.30/1.23    inference(avatar_component_clause,[],[f85])).
% 6.30/1.23  fof(f85,plain,(
% 6.30/1.23    spl10_4 <=> k1_tarski(sK1) = k2_relat_1(sK2)),
% 6.30/1.23    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 6.30/1.23  fof(f6601,plain,(
% 6.30/1.23    spl10_169 | ~spl10_15 | ~spl10_86),
% 6.30/1.23    inference(avatar_split_clause,[],[f1206,f1201,f147,f6599])).
% 6.30/1.23  fof(f147,plain,(
% 6.30/1.23    spl10_15 <=> ! [X5,X0] : (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0)))),
% 6.30/1.23    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 6.30/1.23  fof(f1201,plain,(
% 6.30/1.23    spl10_86 <=> ! [X1,X0] : (~r2_hidden(k4_tarski(X0,X1),sK2) | sK1 = X1)),
% 6.30/1.23    introduced(avatar_definition,[new_symbols(naming,[spl10_86])])).
% 6.30/1.23  fof(f1206,plain,(
% 6.30/1.23    ( ! [X0] : (sK1 = X0 | ~r2_hidden(X0,k2_relat_1(sK2))) ) | (~spl10_15 | ~spl10_86)),
% 6.30/1.23    inference(resolution,[],[f1202,f148])).
% 6.30/1.23  fof(f148,plain,(
% 6.30/1.23    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) ) | ~spl10_15),
% 6.30/1.23    inference(avatar_component_clause,[],[f147])).
% 6.30/1.23  fof(f1202,plain,(
% 6.30/1.23    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | sK1 = X1) ) | ~spl10_86),
% 6.30/1.23    inference(avatar_component_clause,[],[f1201])).
% 6.30/1.23  fof(f5558,plain,(
% 6.30/1.23    spl10_19 | ~spl10_7 | ~spl10_102),
% 6.30/1.23    inference(avatar_split_clause,[],[f4838,f1630,f99,f165])).
% 6.30/1.23  fof(f165,plain,(
% 6.30/1.23    spl10_19 <=> r2_hidden(sK1,k2_relat_1(sK2))),
% 6.30/1.23    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 6.30/1.23  fof(f99,plain,(
% 6.30/1.23    spl10_7 <=> r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 6.30/1.23    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 6.30/1.23  fof(f1630,plain,(
% 6.30/1.23    spl10_102 <=> ! [X5,X4] : (~r2_hidden(X4,X5) | r2_hidden(sK1,k2_relat_1(X5)) | ~r2_hidden(X4,sK2))),
% 6.30/1.23    introduced(avatar_definition,[new_symbols(naming,[spl10_102])])).
% 6.30/1.23  fof(f4838,plain,(
% 6.30/1.23    r2_hidden(sK1,k2_relat_1(sK2)) | (~spl10_7 | ~spl10_102)),
% 6.30/1.23    inference(unit_resulting_resolution,[],[f101,f101,f1631])).
% 6.30/1.23  fof(f1631,plain,(
% 6.30/1.23    ( ! [X4,X5] : (r2_hidden(sK1,k2_relat_1(X5)) | ~r2_hidden(X4,X5) | ~r2_hidden(X4,sK2)) ) | ~spl10_102),
% 6.30/1.23    inference(avatar_component_clause,[],[f1630])).
% 6.30/1.23  fof(f101,plain,(
% 6.30/1.23    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl10_7),
% 6.30/1.23    inference(avatar_component_clause,[],[f99])).
% 6.30/1.23  fof(f5351,plain,(
% 6.30/1.23    spl10_3 | ~spl10_20 | ~spl10_79 | spl10_140),
% 6.30/1.23    inference(avatar_contradiction_clause,[],[f5350])).
% 6.30/1.23  fof(f5350,plain,(
% 6.30/1.23    $false | (spl10_3 | ~spl10_20 | ~spl10_79 | spl10_140)),
% 6.30/1.23    inference(subsumption_resolution,[],[f5341,f5331])).
% 6.30/1.23  fof(f5331,plain,(
% 6.30/1.23    ~r2_hidden(sK9(sK0,k1_relat_1(sK2)),k1_relat_1(sK2)) | (~spl10_79 | spl10_140)),
% 6.30/1.23    inference(unit_resulting_resolution,[],[f5088,f1110])).
% 6.30/1.23  fof(f1110,plain,(
% 6.30/1.23    ( ! [X3] : (~r2_hidden(X3,k1_relat_1(sK2)) | sK0 = X3) ) | ~spl10_79),
% 6.30/1.23    inference(avatar_component_clause,[],[f1109])).
% 6.30/1.23  fof(f1109,plain,(
% 6.30/1.23    spl10_79 <=> ! [X3] : (sK0 = X3 | ~r2_hidden(X3,k1_relat_1(sK2)))),
% 6.30/1.23    introduced(avatar_definition,[new_symbols(naming,[spl10_79])])).
% 6.30/1.23  fof(f5088,plain,(
% 6.30/1.23    sK0 != sK9(sK0,k1_relat_1(sK2)) | spl10_140),
% 6.30/1.23    inference(avatar_component_clause,[],[f5086])).
% 6.30/1.23  fof(f5086,plain,(
% 6.30/1.23    spl10_140 <=> sK0 = sK9(sK0,k1_relat_1(sK2))),
% 6.30/1.23    introduced(avatar_definition,[new_symbols(naming,[spl10_140])])).
% 6.30/1.23  fof(f5341,plain,(
% 6.30/1.23    r2_hidden(sK9(sK0,k1_relat_1(sK2)),k1_relat_1(sK2)) | (spl10_3 | ~spl10_20 | spl10_140)),
% 6.30/1.23    inference(unit_resulting_resolution,[],[f83,f5088,f207])).
% 6.30/1.23  fof(f83,plain,(
% 6.30/1.23    k1_tarski(sK0) != k1_relat_1(sK2) | spl10_3),
% 6.30/1.23    inference(avatar_component_clause,[],[f81])).
% 6.30/1.23  fof(f81,plain,(
% 6.30/1.23    spl10_3 <=> k1_tarski(sK0) = k1_relat_1(sK2)),
% 6.30/1.23    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 6.30/1.23  fof(f5089,plain,(
% 6.30/1.23    ~spl10_140 | spl10_3 | ~spl10_18 | ~spl10_25),
% 6.30/1.23    inference(avatar_split_clause,[],[f280,f241,f161,f81,f5086])).
% 6.30/1.23  fof(f161,plain,(
% 6.30/1.23    spl10_18 <=> ! [X1,X0] : (k1_tarski(X0) = X1 | sK9(X0,X1) != X0 | ~r2_hidden(X0,X1))),
% 6.30/1.23    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 6.30/1.23  fof(f241,plain,(
% 6.30/1.23    spl10_25 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 6.30/1.23    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).
% 6.30/1.23  fof(f280,plain,(
% 6.30/1.23    sK0 != sK9(sK0,k1_relat_1(sK2)) | (spl10_3 | ~spl10_18 | ~spl10_25)),
% 6.30/1.23    inference(unit_resulting_resolution,[],[f83,f243,f162])).
% 6.30/1.23  fof(f162,plain,(
% 6.30/1.23    ( ! [X0,X1] : (sK9(X0,X1) != X0 | k1_tarski(X0) = X1 | ~r2_hidden(X0,X1)) ) | ~spl10_18),
% 6.30/1.23    inference(avatar_component_clause,[],[f161])).
% 6.30/1.23  fof(f243,plain,(
% 6.30/1.23    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl10_25),
% 6.30/1.23    inference(avatar_component_clause,[],[f241])).
% 6.30/1.23  fof(f3077,plain,(
% 6.30/1.23    ~spl10_129 | spl10_4 | ~spl10_18 | ~spl10_19),
% 6.30/1.23    inference(avatar_split_clause,[],[f210,f165,f161,f85,f3074])).
% 6.30/1.23  fof(f210,plain,(
% 6.30/1.23    sK1 != sK9(sK1,k2_relat_1(sK2)) | (spl10_4 | ~spl10_18 | ~spl10_19)),
% 6.30/1.23    inference(unit_resulting_resolution,[],[f87,f167,f162])).
% 6.30/1.23  fof(f167,plain,(
% 6.30/1.23    r2_hidden(sK1,k2_relat_1(sK2)) | ~spl10_19),
% 6.30/1.23    inference(avatar_component_clause,[],[f165])).
% 6.30/1.23  fof(f1632,plain,(
% 6.30/1.23    spl10_102 | ~spl10_10 | ~spl10_30),
% 6.30/1.23    inference(avatar_split_clause,[],[f293,f285,f119,f1630])).
% 6.30/1.23  fof(f119,plain,(
% 6.30/1.23    spl10_10 <=> ! [X5,X0,X6] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0))),
% 6.30/1.23    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 6.30/1.23  fof(f285,plain,(
% 6.30/1.23    spl10_30 <=> ! [X0] : (~r2_hidden(X0,sK2) | k4_tarski(sK0,sK1) = X0)),
% 6.30/1.23    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).
% 6.30/1.23  fof(f293,plain,(
% 6.30/1.23    ( ! [X4,X5] : (~r2_hidden(X4,X5) | r2_hidden(sK1,k2_relat_1(X5)) | ~r2_hidden(X4,sK2)) ) | (~spl10_10 | ~spl10_30)),
% 6.30/1.23    inference(superposition,[],[f120,f286])).
% 6.30/1.23  fof(f286,plain,(
% 6.30/1.23    ( ! [X0] : (k4_tarski(sK0,sK1) = X0 | ~r2_hidden(X0,sK2)) ) | ~spl10_30),
% 6.30/1.23    inference(avatar_component_clause,[],[f285])).
% 6.30/1.23  fof(f120,plain,(
% 6.30/1.23    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X6,X5),X0) | r2_hidden(X5,k2_relat_1(X0))) ) | ~spl10_10),
% 6.30/1.23    inference(avatar_component_clause,[],[f119])).
% 6.30/1.23  fof(f1203,plain,(
% 6.30/1.23    spl10_86 | ~spl10_2 | ~spl10_52),
% 6.30/1.23    inference(avatar_split_clause,[],[f630,f617,f76,f1201])).
% 6.30/1.23  fof(f76,plain,(
% 6.30/1.23    spl10_2 <=> sK2 = k1_tarski(k4_tarski(sK0,sK1))),
% 6.30/1.23    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 6.30/1.23  fof(f617,plain,(
% 6.30/1.23    spl10_52 <=> ! [X1,X3,X0,X2] : (~r2_hidden(k4_tarski(X2,X3),k1_tarski(k4_tarski(X0,X1))) | X1 = X3)),
% 6.30/1.23    introduced(avatar_definition,[new_symbols(naming,[spl10_52])])).
% 6.30/1.23  fof(f630,plain,(
% 6.30/1.23    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | sK1 = X1) ) | (~spl10_2 | ~spl10_52)),
% 6.30/1.23    inference(superposition,[],[f618,f78])).
% 6.30/1.23  fof(f78,plain,(
% 6.30/1.23    sK2 = k1_tarski(k4_tarski(sK0,sK1)) | ~spl10_2),
% 6.30/1.23    inference(avatar_component_clause,[],[f76])).
% 6.30/1.23  fof(f618,plain,(
% 6.30/1.23    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),k1_tarski(k4_tarski(X0,X1))) | X1 = X3) ) | ~spl10_52),
% 6.30/1.23    inference(avatar_component_clause,[],[f617])).
% 6.30/1.23  fof(f1111,plain,(
% 6.30/1.23    spl10_79 | ~spl10_14 | ~spl10_31),
% 6.30/1.23    inference(avatar_split_clause,[],[f308,f300,f143,f1109])).
% 6.30/1.23  fof(f143,plain,(
% 6.30/1.23    spl10_14 <=> ! [X5,X0] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0)))),
% 6.30/1.23    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 6.30/1.23  fof(f300,plain,(
% 6.30/1.23    spl10_31 <=> ! [X1,X0] : (~r2_hidden(k4_tarski(X0,X1),sK2) | sK0 = X0)),
% 6.30/1.23    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).
% 6.30/1.23  fof(f308,plain,(
% 6.30/1.23    ( ! [X3] : (sK0 = X3 | ~r2_hidden(X3,k1_relat_1(sK2))) ) | (~spl10_14 | ~spl10_31)),
% 6.30/1.23    inference(resolution,[],[f301,f144])).
% 6.30/1.23  fof(f144,plain,(
% 6.30/1.23    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) ) | ~spl10_14),
% 6.30/1.23    inference(avatar_component_clause,[],[f143])).
% 6.30/1.23  fof(f301,plain,(
% 6.30/1.23    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | sK0 = X0) ) | ~spl10_31),
% 6.30/1.23    inference(avatar_component_clause,[],[f300])).
% 6.30/1.23  fof(f619,plain,(
% 6.30/1.23    spl10_52 | ~spl10_11 | ~spl10_13),
% 6.30/1.23    inference(avatar_split_clause,[],[f176,f139,f123,f617])).
% 6.30/1.23  fof(f123,plain,(
% 6.30/1.23    spl10_11 <=> ! [X1,X0] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))),
% 6.30/1.23    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 6.30/1.23  fof(f139,plain,(
% 6.30/1.23    spl10_13 <=> ! [X1,X3,X0,X2] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))))),
% 6.30/1.23    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 6.30/1.23  fof(f176,plain,(
% 6.30/1.23    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),k1_tarski(k4_tarski(X0,X1))) | X1 = X3) ) | (~spl10_11 | ~spl10_13)),
% 6.30/1.23    inference(superposition,[],[f140,f124])).
% 6.30/1.23  fof(f124,plain,(
% 6.30/1.23    ( ! [X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))) ) | ~spl10_11),
% 6.30/1.23    inference(avatar_component_clause,[],[f123])).
% 6.30/1.23  fof(f140,plain,(
% 6.30/1.23    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 = X3) ) | ~spl10_13),
% 6.30/1.23    inference(avatar_component_clause,[],[f139])).
% 6.30/1.23  fof(f302,plain,(
% 6.30/1.23    spl10_31 | ~spl10_2 | ~spl10_17),
% 6.30/1.23    inference(avatar_split_clause,[],[f204,f155,f76,f300])).
% 6.30/1.23  fof(f155,plain,(
% 6.30/1.23    spl10_17 <=> ! [X1,X3,X0,X2] : (~r2_hidden(k4_tarski(X0,X1),k1_tarski(k4_tarski(X2,X3))) | X0 = X2)),
% 6.30/1.23    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 6.30/1.23  fof(f204,plain,(
% 6.30/1.23    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | sK0 = X0) ) | (~spl10_2 | ~spl10_17)),
% 6.30/1.23    inference(superposition,[],[f156,f78])).
% 6.30/1.23  fof(f156,plain,(
% 6.30/1.23    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k1_tarski(k4_tarski(X2,X3))) | X0 = X2) ) | ~spl10_17),
% 6.30/1.23    inference(avatar_component_clause,[],[f155])).
% 6.30/1.23  fof(f287,plain,(
% 6.30/1.23    spl10_30 | ~spl10_2 | ~spl10_8),
% 6.30/1.23    inference(avatar_split_clause,[],[f113,f104,f76,f285])).
% 6.30/1.23  fof(f104,plain,(
% 6.30/1.23    spl10_8 <=> ! [X3,X0] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0)))),
% 6.30/1.23    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 6.30/1.23  fof(f113,plain,(
% 6.30/1.23    ( ! [X0] : (~r2_hidden(X0,sK2) | k4_tarski(sK0,sK1) = X0) ) | (~spl10_2 | ~spl10_8)),
% 6.30/1.23    inference(superposition,[],[f105,f78])).
% 6.30/1.23  fof(f105,plain,(
% 6.30/1.23    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) ) | ~spl10_8),
% 6.30/1.23    inference(avatar_component_clause,[],[f104])).
% 6.30/1.23  fof(f244,plain,(
% 6.30/1.23    spl10_25 | ~spl10_7 | ~spl10_9),
% 6.30/1.23    inference(avatar_split_clause,[],[f131,f115,f99,f241])).
% 6.30/1.23  fof(f115,plain,(
% 6.30/1.23    spl10_9 <=> ! [X5,X0,X6] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0))),
% 6.30/1.23    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 6.30/1.23  fof(f131,plain,(
% 6.30/1.23    r2_hidden(sK0,k1_relat_1(sK2)) | (~spl10_7 | ~spl10_9)),
% 6.30/1.23    inference(unit_resulting_resolution,[],[f101,f116])).
% 6.30/1.23  fof(f116,plain,(
% 6.30/1.23    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) ) | ~spl10_9),
% 6.30/1.23    inference(avatar_component_clause,[],[f115])).
% 6.30/1.23  fof(f208,plain,(
% 6.30/1.23    spl10_20),
% 6.30/1.23    inference(avatar_split_clause,[],[f49,f206])).
% 6.30/1.23  fof(f49,plain,(
% 6.30/1.23    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK9(X0,X1) = X0 | r2_hidden(sK9(X0,X1),X1)) )),
% 6.30/1.23    inference(cnf_transformation,[],[f29])).
% 6.30/1.23  fof(f29,plain,(
% 6.30/1.23    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK9(X0,X1) != X0 | ~r2_hidden(sK9(X0,X1),X1)) & (sK9(X0,X1) = X0 | r2_hidden(sK9(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 6.30/1.23    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f27,f28])).
% 6.30/1.23  fof(f28,plain,(
% 6.30/1.23    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK9(X0,X1) != X0 | ~r2_hidden(sK9(X0,X1),X1)) & (sK9(X0,X1) = X0 | r2_hidden(sK9(X0,X1),X1))))),
% 6.30/1.23    introduced(choice_axiom,[])).
% 6.30/1.23  fof(f27,plain,(
% 6.30/1.23    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 6.30/1.23    inference(rectify,[],[f26])).
% 6.30/1.23  fof(f26,plain,(
% 6.30/1.23    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 6.30/1.23    inference(nnf_transformation,[],[f1])).
% 6.30/1.23  fof(f1,axiom,(
% 6.30/1.23    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 6.30/1.23    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 6.30/1.23  fof(f163,plain,(
% 6.30/1.23    spl10_18),
% 6.30/1.23    inference(avatar_split_clause,[],[f67,f161])).
% 6.30/1.23  fof(f67,plain,(
% 6.30/1.23    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK9(X0,X1) != X0 | ~r2_hidden(X0,X1)) )),
% 6.30/1.23    inference(inner_rewriting,[],[f50])).
% 6.30/1.23  fof(f50,plain,(
% 6.30/1.23    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK9(X0,X1) != X0 | ~r2_hidden(sK9(X0,X1),X1)) )),
% 6.30/1.23    inference(cnf_transformation,[],[f29])).
% 6.30/1.23  fof(f157,plain,(
% 6.30/1.23    spl10_17),
% 6.30/1.23    inference(avatar_split_clause,[],[f69,f155])).
% 6.30/1.23  fof(f69,plain,(
% 6.30/1.23    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k1_tarski(k4_tarski(X2,X3))) | X0 = X2) )),
% 6.30/1.23    inference(forward_demodulation,[],[f54,f38])).
% 6.30/1.23  fof(f38,plain,(
% 6.30/1.23    ( ! [X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))) )),
% 6.30/1.23    inference(cnf_transformation,[],[f5])).
% 6.30/1.23  fof(f5,axiom,(
% 6.30/1.23    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))),
% 6.30/1.23    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).
% 6.30/1.23  fof(f54,plain,(
% 6.30/1.23    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) )),
% 6.30/1.23    inference(cnf_transformation,[],[f33])).
% 6.30/1.23  fof(f33,plain,(
% 6.30/1.23    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | X1 != X3 | X0 != X2) & ((X1 = X3 & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))))),
% 6.30/1.23    inference(flattening,[],[f32])).
% 6.30/1.23  fof(f32,plain,(
% 6.30/1.23    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | (X1 != X3 | X0 != X2)) & ((X1 = X3 & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))))),
% 6.30/1.23    inference(nnf_transformation,[],[f4])).
% 6.30/1.23  fof(f4,axiom,(
% 6.30/1.23    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <=> (X1 = X3 & X0 = X2))),
% 6.30/1.23    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).
% 6.30/1.23  fof(f149,plain,(
% 6.30/1.23    spl10_15),
% 6.30/1.23    inference(avatar_split_clause,[],[f60,f147])).
% 6.30/1.23  fof(f60,plain,(
% 6.30/1.23    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 6.30/1.23    inference(equality_resolution,[],[f43])).
% 6.30/1.23  fof(f43,plain,(
% 6.30/1.23    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 6.30/1.23    inference(cnf_transformation,[],[f25])).
% 6.30/1.23  fof(f25,plain,(
% 6.30/1.23    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 6.30/1.23    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f21,f24,f23,f22])).
% 6.30/1.23  fof(f22,plain,(
% 6.30/1.23    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 6.30/1.23    introduced(choice_axiom,[])).
% 6.30/1.23  fof(f23,plain,(
% 6.30/1.23    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0) => r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0))),
% 6.30/1.23    introduced(choice_axiom,[])).
% 6.30/1.23  fof(f24,plain,(
% 6.30/1.23    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0))),
% 6.30/1.23    introduced(choice_axiom,[])).
% 6.30/1.23  fof(f21,plain,(
% 6.30/1.23    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 6.30/1.23    inference(rectify,[],[f20])).
% 6.30/1.23  fof(f20,plain,(
% 6.30/1.23    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 6.30/1.23    inference(nnf_transformation,[],[f7])).
% 6.30/1.23  fof(f7,axiom,(
% 6.30/1.23    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 6.30/1.23    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 6.30/1.23  fof(f145,plain,(
% 6.30/1.23    spl10_14),
% 6.30/1.23    inference(avatar_split_clause,[],[f58,f143])).
% 6.30/1.23  fof(f58,plain,(
% 6.30/1.23    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 6.30/1.23    inference(equality_resolution,[],[f39])).
% 6.30/1.23  fof(f39,plain,(
% 6.30/1.23    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 6.30/1.23    inference(cnf_transformation,[],[f19])).
% 6.30/1.23  fof(f19,plain,(
% 6.30/1.23    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 6.30/1.23    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f15,f18,f17,f16])).
% 6.30/1.23  fof(f16,plain,(
% 6.30/1.23    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 6.30/1.23    introduced(choice_axiom,[])).
% 6.30/1.23  fof(f17,plain,(
% 6.30/1.23    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0))),
% 6.30/1.23    introduced(choice_axiom,[])).
% 6.30/1.23  fof(f18,plain,(
% 6.30/1.23    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0))),
% 6.30/1.23    introduced(choice_axiom,[])).
% 6.30/1.23  fof(f15,plain,(
% 6.30/1.23    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 6.30/1.23    inference(rectify,[],[f14])).
% 6.30/1.23  fof(f14,plain,(
% 6.30/1.23    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 6.30/1.23    inference(nnf_transformation,[],[f6])).
% 6.30/1.23  fof(f6,axiom,(
% 6.30/1.23    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 6.30/1.23    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 6.30/1.23  fof(f141,plain,(
% 6.30/1.23    spl10_13),
% 6.30/1.23    inference(avatar_split_clause,[],[f52,f139])).
% 6.30/1.23  fof(f52,plain,(
% 6.30/1.23    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) )),
% 6.30/1.23    inference(cnf_transformation,[],[f31])).
% 6.30/1.23  fof(f31,plain,(
% 6.30/1.23    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 6.30/1.23    inference(flattening,[],[f30])).
% 6.30/1.23  fof(f30,plain,(
% 6.30/1.23    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | (X1 != X3 | ~r2_hidden(X0,X2))) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 6.30/1.23    inference(nnf_transformation,[],[f3])).
% 6.30/1.23  fof(f3,axiom,(
% 6.30/1.23    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 6.30/1.23    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 6.30/1.23  fof(f125,plain,(
% 6.30/1.23    spl10_11),
% 6.30/1.23    inference(avatar_split_clause,[],[f38,f123])).
% 6.30/1.23  fof(f121,plain,(
% 6.30/1.23    spl10_10),
% 6.30/1.23    inference(avatar_split_clause,[],[f59,f119])).
% 6.30/1.23  fof(f59,plain,(
% 6.30/1.23    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 6.30/1.23    inference(equality_resolution,[],[f44])).
% 6.30/1.23  fof(f44,plain,(
% 6.30/1.23    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 6.30/1.23    inference(cnf_transformation,[],[f25])).
% 6.30/1.23  fof(f117,plain,(
% 6.30/1.23    spl10_9),
% 6.30/1.23    inference(avatar_split_clause,[],[f57,f115])).
% 6.30/1.23  fof(f57,plain,(
% 6.30/1.23    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 6.30/1.23    inference(equality_resolution,[],[f40])).
% 6.30/1.23  fof(f40,plain,(
% 6.30/1.23    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 6.30/1.23    inference(cnf_transformation,[],[f19])).
% 6.30/1.23  fof(f106,plain,(
% 6.30/1.23    spl10_8),
% 6.30/1.23    inference(avatar_split_clause,[],[f63,f104])).
% 6.30/1.23  fof(f63,plain,(
% 6.30/1.23    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 6.30/1.23    inference(equality_resolution,[],[f47])).
% 6.30/1.23  fof(f47,plain,(
% 6.30/1.23    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 6.30/1.23    inference(cnf_transformation,[],[f29])).
% 6.30/1.23  fof(f102,plain,(
% 6.30/1.23    spl10_7 | ~spl10_2 | ~spl10_5),
% 6.30/1.23    inference(avatar_split_clause,[],[f93,f90,f76,f99])).
% 6.30/1.23  fof(f90,plain,(
% 6.30/1.23    spl10_5 <=> ! [X3] : r2_hidden(X3,k1_tarski(X3))),
% 6.30/1.23    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 6.30/1.23  fof(f93,plain,(
% 6.30/1.23    r2_hidden(k4_tarski(sK0,sK1),sK2) | (~spl10_2 | ~spl10_5)),
% 6.30/1.23    inference(superposition,[],[f91,f78])).
% 6.30/1.23  fof(f91,plain,(
% 6.30/1.23    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) ) | ~spl10_5),
% 6.30/1.23    inference(avatar_component_clause,[],[f90])).
% 6.30/1.23  fof(f92,plain,(
% 6.30/1.23    spl10_5),
% 6.30/1.23    inference(avatar_split_clause,[],[f62,f90])).
% 6.30/1.23  fof(f62,plain,(
% 6.30/1.23    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 6.30/1.23    inference(equality_resolution,[],[f61])).
% 6.30/1.23  fof(f61,plain,(
% 6.30/1.23    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 6.30/1.23    inference(equality_resolution,[],[f48])).
% 6.30/1.23  fof(f48,plain,(
% 6.30/1.23    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 6.30/1.23    inference(cnf_transformation,[],[f29])).
% 6.30/1.23  fof(f88,plain,(
% 6.30/1.23    ~spl10_3 | ~spl10_4),
% 6.30/1.23    inference(avatar_split_clause,[],[f36,f85,f81])).
% 6.30/1.23  fof(f36,plain,(
% 6.30/1.23    k1_tarski(sK1) != k2_relat_1(sK2) | k1_tarski(sK0) != k1_relat_1(sK2)),
% 6.30/1.23    inference(cnf_transformation,[],[f13])).
% 6.30/1.23  fof(f13,plain,(
% 6.30/1.23    (k1_tarski(sK1) != k2_relat_1(sK2) | k1_tarski(sK0) != k1_relat_1(sK2)) & sK2 = k1_tarski(k4_tarski(sK0,sK1)) & v1_relat_1(sK2)),
% 6.30/1.23    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 6.30/1.23  fof(f12,plain,(
% 6.30/1.23    ? [X0,X1,X2] : ((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2 & v1_relat_1(X2)) => ((k1_tarski(sK1) != k2_relat_1(sK2) | k1_tarski(sK0) != k1_relat_1(sK2)) & sK2 = k1_tarski(k4_tarski(sK0,sK1)) & v1_relat_1(sK2))),
% 6.30/1.23    introduced(choice_axiom,[])).
% 6.30/1.23  fof(f11,plain,(
% 6.30/1.23    ? [X0,X1,X2] : ((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2 & v1_relat_1(X2))),
% 6.30/1.23    inference(flattening,[],[f10])).
% 6.30/1.23  fof(f10,plain,(
% 6.30/1.23    ? [X0,X1,X2] : (((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2) & v1_relat_1(X2))),
% 6.30/1.23    inference(ennf_transformation,[],[f9])).
% 6.30/1.23  fof(f9,negated_conjecture,(
% 6.30/1.23    ~! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2))))),
% 6.30/1.23    inference(negated_conjecture,[],[f8])).
% 6.30/1.23  fof(f8,conjecture,(
% 6.30/1.23    ! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2))))),
% 6.30/1.23    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relat_1)).
% 6.30/1.23  fof(f79,plain,(
% 6.30/1.23    spl10_2),
% 6.30/1.23    inference(avatar_split_clause,[],[f35,f76])).
% 6.30/1.23  fof(f35,plain,(
% 6.30/1.23    sK2 = k1_tarski(k4_tarski(sK0,sK1))),
% 6.30/1.23    inference(cnf_transformation,[],[f13])).
% 6.30/1.23  % SZS output end Proof for theBenchmark
% 6.30/1.23  % (741)------------------------------
% 6.30/1.23  % (741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.30/1.23  % (741)Termination reason: Refutation
% 6.30/1.23  
% 6.30/1.23  % (741)Memory used [KB]: 10618
% 6.30/1.23  % (741)Time elapsed: 0.632 s
% 6.30/1.23  % (741)------------------------------
% 6.30/1.23  % (741)------------------------------
% 6.30/1.23  % (708)Time limit reached!
% 6.30/1.23  % (708)------------------------------
% 6.30/1.23  % (708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.30/1.23  % (708)Termination reason: Time limit
% 6.30/1.23  
% 6.30/1.23  % (708)Memory used [KB]: 7036
% 6.30/1.23  % (708)Time elapsed: 0.820 s
% 6.30/1.23  % (708)------------------------------
% 6.30/1.23  % (708)------------------------------
% 6.30/1.23  % (706)Success in time 0.863 s
%------------------------------------------------------------------------------
