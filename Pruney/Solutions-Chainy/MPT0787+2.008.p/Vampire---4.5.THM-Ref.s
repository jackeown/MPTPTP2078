%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 222 expanded)
%              Number of leaves         :   27 (  96 expanded)
%              Depth                    :   10
%              Number of atoms          :  414 ( 747 expanded)
%              Number of equality atoms :   32 (  54 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f500,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f75,f80,f85,f94,f95,f101,f119,f221,f298,f367,f376,f390,f394,f401,f436,f441,f443,f456,f490,f499])).

fof(f499,plain,
    ( ~ spl11_4
    | ~ spl11_41 ),
    inference(avatar_split_clause,[],[f492,f487,f82])).

fof(f82,plain,
    ( spl11_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f487,plain,
    ( spl11_41
  <=> r2_hidden(sK1,k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_41])])).

fof(f492,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl11_41 ),
    inference(resolution,[],[f489,f63])).

fof(f63,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_wellord1(X0,X3))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,X2)
      | k1_wellord1(X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | X1 != X3
      | ~ r2_hidden(X3,X2)
      | k1_wellord1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

fof(f489,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK1))
    | ~ spl11_41 ),
    inference(avatar_component_clause,[],[f487])).

fof(f490,plain,
    ( spl11_41
    | ~ spl11_6
    | ~ spl11_25 ),
    inference(avatar_split_clause,[],[f484,f256,f91,f487])).

fof(f91,plain,
    ( spl11_6
  <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f256,plain,
    ( spl11_25
  <=> r2_hidden(sK1,k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_25])])).

fof(f484,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK1))
    | ~ spl11_6
    | ~ spl11_25 ),
    inference(resolution,[],[f459,f92])).

fof(f92,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f459,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_wellord1(sK2,sK0),X1)
        | r2_hidden(sK1,X1) )
    | ~ spl11_25 ),
    inference(resolution,[],[f258,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f258,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ spl11_25 ),
    inference(avatar_component_clause,[],[f256])).

fof(f456,plain,
    ( spl11_25
    | ~ spl11_4
    | spl11_21
    | ~ spl11_22 ),
    inference(avatar_split_clause,[],[f453,f236,f232,f82,f256])).

fof(f232,plain,
    ( spl11_21
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).

fof(f236,plain,
    ( spl11_22
  <=> r2_hidden(k4_tarski(sK1,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f453,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | spl11_21
    | ~ spl11_22 ),
    inference(resolution,[],[f238,f380])).

fof(f380,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k4_tarski(sK1,sK0),X2)
        | ~ v1_relat_1(X2)
        | r2_hidden(sK1,k1_wellord1(X2,sK0)) )
    | spl11_21 ),
    inference(extensionality_resolution,[],[f60,f233])).

fof(f233,plain,
    ( sK0 != sK1
    | spl11_21 ),
    inference(avatar_component_clause,[],[f232])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X1),X0)
      | X1 = X3
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | X1 = X3
      | ~ r2_hidden(k4_tarski(X3,X1),X0)
      | r2_hidden(X3,X2)
      | k1_wellord1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f238,plain,
    ( r2_hidden(k4_tarski(sK1,sK0),sK2)
    | ~ spl11_22 ),
    inference(avatar_component_clause,[],[f236])).

fof(f443,plain,
    ( spl11_21
    | spl11_5
    | spl11_22
    | ~ spl11_1
    | ~ spl11_19 ),
    inference(avatar_split_clause,[],[f279,f219,f67,f236,f87,f232])).

fof(f87,plain,
    ( spl11_5
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f67,plain,
    ( spl11_1
  <=> r2_hidden(sK1,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f219,plain,
    ( spl11_19
  <=> ! [X1] :
        ( ~ r2_hidden(X1,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(X1,sK0),sK2)
        | r2_hidden(k4_tarski(sK0,X1),sK2)
        | sK0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f279,plain,
    ( r2_hidden(k4_tarski(sK1,sK0),sK2)
    | r2_hidden(k4_tarski(sK0,sK1),sK2)
    | sK0 = sK1
    | ~ spl11_1
    | ~ spl11_19 ),
    inference(resolution,[],[f220,f69])).

fof(f69,plain,
    ( r2_hidden(sK1,k3_relat_1(sK2))
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f220,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(X1,sK0),sK2)
        | r2_hidden(k4_tarski(sK0,X1),sK2)
        | sK0 = X1 )
    | ~ spl11_19 ),
    inference(avatar_component_clause,[],[f219])).

fof(f441,plain,
    ( sK0 != sK1
    | r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(k4_tarski(sK1,sK1),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f436,plain,
    ( spl11_6
    | ~ spl11_4
    | ~ spl11_35 ),
    inference(avatar_split_clause,[],[f435,f348,f82,f91])).

fof(f348,plain,
    ( spl11_35
  <=> ! [X0] :
        ( r2_hidden(X0,k1_wellord1(sK2,sK1))
        | ~ r2_hidden(k4_tarski(X0,sK0),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_35])])).

fof(f435,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl11_4
    | ~ spl11_35 ),
    inference(duplicate_literal_removal,[],[f431])).

fof(f431,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl11_4
    | ~ spl11_35 ),
    inference(resolution,[],[f415,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK10(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f415,plain,
    ( ! [X1] :
        ( r2_hidden(sK10(k1_wellord1(sK2,sK0),X1),k1_wellord1(sK2,sK1))
        | r1_tarski(k1_wellord1(sK2,sK0),X1) )
    | ~ spl11_4
    | ~ spl11_35 ),
    inference(resolution,[],[f349,f183])).

fof(f183,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK10(k1_wellord1(sK2,X0),X1),X0),sK2)
        | r1_tarski(k1_wellord1(sK2,X0),X1) )
    | ~ spl11_4 ),
    inference(resolution,[],[f141,f84])).

fof(f84,plain,
    ( v1_relat_1(sK2)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK10(k1_wellord1(X0,X1),X2),X1),X0)
      | r1_tarski(k1_wellord1(X0,X1),X2) ) ),
    inference(resolution,[],[f61,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_wellord1(X0,X1))
      | r2_hidden(k4_tarski(X3,X1),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X1),X0)
      | ~ r2_hidden(X3,X2)
      | k1_wellord1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f349,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK0),sK2)
        | r2_hidden(X0,k1_wellord1(sK2,sK1)) )
    | ~ spl11_35 ),
    inference(avatar_component_clause,[],[f348])).

fof(f401,plain,
    ( spl11_35
    | ~ spl11_1
    | ~ spl11_24
    | ~ spl11_28 ),
    inference(avatar_split_clause,[],[f398,f296,f248,f67,f348])).

fof(f248,plain,
    ( spl11_24
  <=> r2_hidden(sK0,k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f296,plain,
    ( spl11_28
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,k1_wellord1(sK2,X1))
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | r2_hidden(X2,k1_wellord1(sK2,X1))
        | ~ r2_hidden(k4_tarski(X2,X0),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).

fof(f398,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,k3_relat_1(sK2))
        | r2_hidden(X0,k1_wellord1(sK2,sK1))
        | ~ r2_hidden(k4_tarski(X0,sK0),sK2) )
    | ~ spl11_24
    | ~ spl11_28 ),
    inference(resolution,[],[f250,f297])).

fof(f297,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k1_wellord1(sK2,X1))
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | r2_hidden(X2,k1_wellord1(sK2,X1))
        | ~ r2_hidden(k4_tarski(X2,X0),sK2) )
    | ~ spl11_28 ),
    inference(avatar_component_clause,[],[f296])).

fof(f250,plain,
    ( r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | ~ spl11_24 ),
    inference(avatar_component_clause,[],[f248])).

fof(f394,plain,
    ( spl11_24
    | ~ spl11_4
    | spl11_21
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f392,f87,f232,f82,f248])).

fof(f392,plain,
    ( sK0 = sK1
    | ~ v1_relat_1(sK2)
    | r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | ~ spl11_5 ),
    inference(resolution,[],[f88,f60])).

fof(f88,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f390,plain,
    ( ~ spl11_7
    | spl11_12
    | ~ spl11_4
    | ~ spl11_1 ),
    inference(avatar_split_clause,[],[f385,f67,f82,f146,f98])).

fof(f98,plain,
    ( spl11_7
  <=> v1_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f146,plain,
    ( spl11_12
  <=> r2_hidden(k4_tarski(sK1,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f385,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK1,sK1),sK2)
    | ~ v1_relat_2(sK2)
    | ~ spl11_1 ),
    inference(resolution,[],[f69,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X1,X1),X0)
      | ~ v1_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(k4_tarski(X1,X1),X0)
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k3_relat_1(X0))
           => r2_hidden(k4_tarski(X1,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_wellord1)).

fof(f376,plain,(
    spl11_36 ),
    inference(avatar_contradiction_clause,[],[f375])).

fof(f375,plain,
    ( $false
    | spl11_36 ),
    inference(resolution,[],[f366,f128])).

fof(f128,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f127])).

fof(f127,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f59,f58])).

fof(f366,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))
    | spl11_36 ),
    inference(avatar_component_clause,[],[f364])).

fof(f364,plain,
    ( spl11_36
  <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_36])])).

fof(f367,plain,
    ( ~ spl11_36
    | spl11_6
    | ~ spl11_21 ),
    inference(avatar_split_clause,[],[f354,f232,f91,f364])).

fof(f354,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))
    | spl11_6
    | ~ spl11_21 ),
    inference(backward_demodulation,[],[f93,f234])).

fof(f234,plain,
    ( sK0 = sK1
    | ~ spl11_21 ),
    inference(avatar_component_clause,[],[f232])).

fof(f93,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | spl11_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f298,plain,
    ( spl11_28
    | ~ spl11_4
    | ~ spl11_3
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f294,f82,f77,f82,f296])).

fof(f77,plain,
    ( spl11_3
  <=> v2_wellord1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f294,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_wellord1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(X0,k1_wellord1(sK2,X1))
        | ~ r2_hidden(k4_tarski(X2,X0),sK2)
        | r2_hidden(X2,k1_wellord1(sK2,X1))
        | ~ r2_hidden(X1,k3_relat_1(sK2)) )
    | ~ spl11_4 ),
    inference(resolution,[],[f64,f126])).

fof(f126,plain,
    ( ! [X0] : r1_tarski(k1_wellord1(sK2,X0),k3_relat_1(sK2))
    | ~ spl11_4 ),
    inference(resolution,[],[f48,f84])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_wellord1)).

fof(f64,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ r1_tarski(k1_wellord1(X1,X2),k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X3,k1_wellord1(X1,X2))
      | ~ r2_hidden(k4_tarski(X4,X3),X1)
      | r2_hidden(X4,k1_wellord1(X1,X2))
      | ~ r2_hidden(X2,k3_relat_1(X1)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v2_wellord1(X1)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X2,k3_relat_1(X1))
      | k1_wellord1(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0 )
      <=> ! [X3] :
            ( ! [X4] :
                ( r2_hidden(X4,X0)
                | ~ r2_hidden(k4_tarski(X4,X3),X1) )
            | ~ r2_hidden(X3,X0) ) )
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0 )
      <=> ! [X3] :
            ( ! [X4] :
                ( r2_hidden(X4,X0)
                | ~ r2_hidden(k4_tarski(X4,X3),X1) )
            | ~ r2_hidden(X3,X0) ) )
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ( r1_tarski(X0,k3_relat_1(X1))
          & v2_wellord1(X1) )
       => ( ~ ( ! [X2] :
                  ~ ( k1_wellord1(X1,X2) = X0
                    & r2_hidden(X2,k3_relat_1(X1)) )
              & k3_relat_1(X1) != X0 )
        <=> ! [X3] :
              ( r2_hidden(X3,X0)
             => ! [X4] :
                  ( r2_hidden(k4_tarski(X4,X3),X1)
                 => r2_hidden(X4,X0) ) ) ) ) ) ),
    inference(rectify,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ( r1_tarski(X0,k3_relat_1(X1))
          & v2_wellord1(X1) )
       => ( ~ ( ! [X2] :
                  ~ ( k1_wellord1(X1,X2) = X0
                    & r2_hidden(X2,k3_relat_1(X1)) )
              & k3_relat_1(X1) != X0 )
        <=> ! [X2] :
              ( r2_hidden(X2,X0)
             => ! [X3] :
                  ( r2_hidden(k4_tarski(X3,X2),X1)
                 => r2_hidden(X3,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_wellord1)).

fof(f221,plain,
    ( ~ spl11_10
    | spl11_19
    | ~ spl11_4
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f211,f72,f82,f219,f116])).

fof(f116,plain,
    ( spl11_10
  <=> v6_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f72,plain,
    ( spl11_2
  <=> r2_hidden(sK0,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f211,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(sK2)
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | sK0 = X1
        | r2_hidden(k4_tarski(sK0,X1),sK2)
        | r2_hidden(k4_tarski(X1,sK0),sK2)
        | ~ v6_relat_2(sK2) )
    | ~ spl11_2 ),
    inference(resolution,[],[f30,f74])).

fof(f74,plain,
    ( r2_hidden(sK0,k3_relat_1(sK2))
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k3_relat_1(X0))
      | X1 = X2
      | r2_hidden(k4_tarski(X1,X2),X0)
      | r2_hidden(k4_tarski(X2,X1),X0)
      | ~ v6_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ~ ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).

fof(f119,plain,
    ( ~ spl11_4
    | spl11_10
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f114,f77,f116,f82])).

fof(f114,plain,
    ( v6_relat_2(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl11_3 ),
    inference(resolution,[],[f39,f79])).

fof(f79,plain,
    ( v2_wellord1(sK2)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).

fof(f101,plain,
    ( ~ spl11_4
    | spl11_7
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f96,f77,f98,f82])).

fof(f96,plain,
    ( v1_relat_2(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl11_3 ),
    inference(resolution,[],[f36,f79])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f95,plain,
    ( spl11_5
    | spl11_6 ),
    inference(avatar_split_clause,[],[f21,f91,f87])).

fof(f21,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) )
         => ( r2_hidden(k4_tarski(X0,X1),X2)
          <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_wellord1)).

fof(f94,plain,
    ( ~ spl11_5
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f22,f91,f87])).

fof(f22,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f85,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f23,f82])).

fof(f23,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f80,plain,(
    spl11_3 ),
    inference(avatar_split_clause,[],[f24,f77])).

fof(f24,plain,(
    v2_wellord1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f75,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f25,f72])).

fof(f25,plain,(
    r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f70,plain,(
    spl11_1 ),
    inference(avatar_split_clause,[],[f26,f67])).

fof(f26,plain,(
    r2_hidden(sK1,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n012.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 18:43:22 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.48  % (6858)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % (6866)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.50  % (6874)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (6847)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (6857)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (6853)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (6861)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (6873)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (6876)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (6849)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (6869)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (6851)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (6868)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (6872)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (6852)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (6850)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (6848)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (6867)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (6860)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (6870)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (6871)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (6875)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (6855)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (6862)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (6864)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (6863)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (6869)Refutation not found, incomplete strategy% (6869)------------------------------
% 0.21/0.55  % (6869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (6854)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (6856)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (6865)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (6869)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (6869)Memory used [KB]: 10874
% 0.21/0.56  % (6869)Time elapsed: 0.140 s
% 0.21/0.56  % (6869)------------------------------
% 0.21/0.56  % (6869)------------------------------
% 0.21/0.56  % (6863)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 1.52/0.56  % (6859)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.52/0.57  % SZS output start Proof for theBenchmark
% 1.52/0.57  fof(f500,plain,(
% 1.52/0.57    $false),
% 1.52/0.57    inference(avatar_sat_refutation,[],[f70,f75,f80,f85,f94,f95,f101,f119,f221,f298,f367,f376,f390,f394,f401,f436,f441,f443,f456,f490,f499])).
% 1.52/0.57  fof(f499,plain,(
% 1.52/0.57    ~spl11_4 | ~spl11_41),
% 1.52/0.57    inference(avatar_split_clause,[],[f492,f487,f82])).
% 1.52/0.57  fof(f82,plain,(
% 1.52/0.57    spl11_4 <=> v1_relat_1(sK2)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 1.52/0.57  fof(f487,plain,(
% 1.52/0.57    spl11_41 <=> r2_hidden(sK1,k1_wellord1(sK2,sK1))),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_41])])).
% 1.52/0.57  fof(f492,plain,(
% 1.52/0.57    ~v1_relat_1(sK2) | ~spl11_41),
% 1.52/0.57    inference(resolution,[],[f489,f63])).
% 1.52/0.57  fof(f63,plain,(
% 1.52/0.57    ( ! [X0,X3] : (~r2_hidden(X3,k1_wellord1(X0,X3)) | ~v1_relat_1(X0)) )),
% 1.52/0.57    inference(equality_resolution,[],[f62])).
% 1.52/0.57  fof(f62,plain,(
% 1.52/0.57    ( ! [X2,X0,X3] : (~v1_relat_1(X0) | ~r2_hidden(X3,X2) | k1_wellord1(X0,X3) != X2) )),
% 1.52/0.57    inference(equality_resolution,[],[f45])).
% 1.52/0.57  fof(f45,plain,(
% 1.52/0.57    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | X1 != X3 | ~r2_hidden(X3,X2) | k1_wellord1(X0,X1) != X2) )),
% 1.52/0.57    inference(cnf_transformation,[],[f16])).
% 1.52/0.57  fof(f16,plain,(
% 1.52/0.57    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 1.52/0.57    inference(ennf_transformation,[],[f2])).
% 1.52/0.57  fof(f2,axiom,(
% 1.52/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).
% 1.52/0.57  fof(f489,plain,(
% 1.52/0.57    r2_hidden(sK1,k1_wellord1(sK2,sK1)) | ~spl11_41),
% 1.52/0.57    inference(avatar_component_clause,[],[f487])).
% 1.52/0.57  fof(f490,plain,(
% 1.52/0.57    spl11_41 | ~spl11_6 | ~spl11_25),
% 1.52/0.57    inference(avatar_split_clause,[],[f484,f256,f91,f487])).
% 1.52/0.57  fof(f91,plain,(
% 1.52/0.57    spl11_6 <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 1.52/0.57  fof(f256,plain,(
% 1.52/0.57    spl11_25 <=> r2_hidden(sK1,k1_wellord1(sK2,sK0))),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_25])])).
% 1.52/0.57  fof(f484,plain,(
% 1.52/0.57    r2_hidden(sK1,k1_wellord1(sK2,sK1)) | (~spl11_6 | ~spl11_25)),
% 1.52/0.57    inference(resolution,[],[f459,f92])).
% 1.52/0.57  fof(f92,plain,(
% 1.52/0.57    r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~spl11_6),
% 1.52/0.57    inference(avatar_component_clause,[],[f91])).
% 1.52/0.57  fof(f459,plain,(
% 1.52/0.57    ( ! [X1] : (~r1_tarski(k1_wellord1(sK2,sK0),X1) | r2_hidden(sK1,X1)) ) | ~spl11_25),
% 1.52/0.57    inference(resolution,[],[f258,f57])).
% 1.52/0.57  fof(f57,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f20])).
% 1.52/0.57  fof(f20,plain,(
% 1.52/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f1])).
% 1.52/0.57  fof(f1,axiom,(
% 1.52/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.52/0.57  fof(f258,plain,(
% 1.52/0.57    r2_hidden(sK1,k1_wellord1(sK2,sK0)) | ~spl11_25),
% 1.52/0.57    inference(avatar_component_clause,[],[f256])).
% 1.52/0.57  fof(f456,plain,(
% 1.52/0.57    spl11_25 | ~spl11_4 | spl11_21 | ~spl11_22),
% 1.52/0.57    inference(avatar_split_clause,[],[f453,f236,f232,f82,f256])).
% 1.52/0.57  fof(f232,plain,(
% 1.52/0.57    spl11_21 <=> sK0 = sK1),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).
% 1.52/0.57  fof(f236,plain,(
% 1.52/0.57    spl11_22 <=> r2_hidden(k4_tarski(sK1,sK0),sK2)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).
% 1.52/0.57  fof(f453,plain,(
% 1.52/0.57    ~v1_relat_1(sK2) | r2_hidden(sK1,k1_wellord1(sK2,sK0)) | (spl11_21 | ~spl11_22)),
% 1.52/0.57    inference(resolution,[],[f238,f380])).
% 1.52/0.57  fof(f380,plain,(
% 1.52/0.57    ( ! [X2] : (~r2_hidden(k4_tarski(sK1,sK0),X2) | ~v1_relat_1(X2) | r2_hidden(sK1,k1_wellord1(X2,sK0))) ) | spl11_21),
% 1.52/0.57    inference(extensionality_resolution,[],[f60,f233])).
% 1.52/0.57  fof(f233,plain,(
% 1.52/0.57    sK0 != sK1 | spl11_21),
% 1.52/0.57    inference(avatar_component_clause,[],[f232])).
% 1.52/0.57  fof(f60,plain,(
% 1.52/0.57    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~v1_relat_1(X0) | r2_hidden(X3,k1_wellord1(X0,X1))) )),
% 1.52/0.57    inference(equality_resolution,[],[f47])).
% 1.52/0.57  fof(f47,plain,(
% 1.52/0.57    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | X1 = X3 | ~r2_hidden(k4_tarski(X3,X1),X0) | r2_hidden(X3,X2) | k1_wellord1(X0,X1) != X2) )),
% 1.52/0.57    inference(cnf_transformation,[],[f16])).
% 1.52/0.57  fof(f238,plain,(
% 1.52/0.57    r2_hidden(k4_tarski(sK1,sK0),sK2) | ~spl11_22),
% 1.52/0.57    inference(avatar_component_clause,[],[f236])).
% 1.52/0.57  fof(f443,plain,(
% 1.52/0.57    spl11_21 | spl11_5 | spl11_22 | ~spl11_1 | ~spl11_19),
% 1.52/0.57    inference(avatar_split_clause,[],[f279,f219,f67,f236,f87,f232])).
% 1.52/0.57  fof(f87,plain,(
% 1.52/0.57    spl11_5 <=> r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 1.52/0.57  fof(f67,plain,(
% 1.52/0.57    spl11_1 <=> r2_hidden(sK1,k3_relat_1(sK2))),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 1.52/0.57  fof(f219,plain,(
% 1.52/0.57    spl11_19 <=> ! [X1] : (~r2_hidden(X1,k3_relat_1(sK2)) | r2_hidden(k4_tarski(X1,sK0),sK2) | r2_hidden(k4_tarski(sK0,X1),sK2) | sK0 = X1)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).
% 1.52/0.57  fof(f279,plain,(
% 1.52/0.57    r2_hidden(k4_tarski(sK1,sK0),sK2) | r2_hidden(k4_tarski(sK0,sK1),sK2) | sK0 = sK1 | (~spl11_1 | ~spl11_19)),
% 1.52/0.57    inference(resolution,[],[f220,f69])).
% 1.52/0.57  fof(f69,plain,(
% 1.52/0.57    r2_hidden(sK1,k3_relat_1(sK2)) | ~spl11_1),
% 1.52/0.57    inference(avatar_component_clause,[],[f67])).
% 1.52/0.57  fof(f220,plain,(
% 1.52/0.57    ( ! [X1] : (~r2_hidden(X1,k3_relat_1(sK2)) | r2_hidden(k4_tarski(X1,sK0),sK2) | r2_hidden(k4_tarski(sK0,X1),sK2) | sK0 = X1) ) | ~spl11_19),
% 1.52/0.57    inference(avatar_component_clause,[],[f219])).
% 1.52/0.57  fof(f441,plain,(
% 1.52/0.57    sK0 != sK1 | r2_hidden(k4_tarski(sK0,sK1),sK2) | ~r2_hidden(k4_tarski(sK1,sK1),sK2)),
% 1.52/0.57    introduced(theory_tautology_sat_conflict,[])).
% 1.52/0.57  fof(f436,plain,(
% 1.52/0.57    spl11_6 | ~spl11_4 | ~spl11_35),
% 1.52/0.57    inference(avatar_split_clause,[],[f435,f348,f82,f91])).
% 1.52/0.57  fof(f348,plain,(
% 1.52/0.57    spl11_35 <=> ! [X0] : (r2_hidden(X0,k1_wellord1(sK2,sK1)) | ~r2_hidden(k4_tarski(X0,sK0),sK2))),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_35])])).
% 1.52/0.57  fof(f435,plain,(
% 1.52/0.57    r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | (~spl11_4 | ~spl11_35)),
% 1.52/0.57    inference(duplicate_literal_removal,[],[f431])).
% 1.52/0.57  fof(f431,plain,(
% 1.52/0.57    r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | (~spl11_4 | ~spl11_35)),
% 1.52/0.57    inference(resolution,[],[f415,f59])).
% 1.52/0.57  fof(f59,plain,(
% 1.52/0.57    ( ! [X0,X1] : (~r2_hidden(sK10(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f20])).
% 1.52/0.57  fof(f415,plain,(
% 1.52/0.57    ( ! [X1] : (r2_hidden(sK10(k1_wellord1(sK2,sK0),X1),k1_wellord1(sK2,sK1)) | r1_tarski(k1_wellord1(sK2,sK0),X1)) ) | (~spl11_4 | ~spl11_35)),
% 1.52/0.57    inference(resolution,[],[f349,f183])).
% 1.52/0.57  fof(f183,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK10(k1_wellord1(sK2,X0),X1),X0),sK2) | r1_tarski(k1_wellord1(sK2,X0),X1)) ) | ~spl11_4),
% 1.52/0.57    inference(resolution,[],[f141,f84])).
% 1.52/0.57  fof(f84,plain,(
% 1.52/0.57    v1_relat_1(sK2) | ~spl11_4),
% 1.52/0.57    inference(avatar_component_clause,[],[f82])).
% 1.52/0.57  fof(f141,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK10(k1_wellord1(X0,X1),X2),X1),X0) | r1_tarski(k1_wellord1(X0,X1),X2)) )),
% 1.52/0.57    inference(resolution,[],[f61,f58])).
% 1.52/0.57  fof(f58,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r2_hidden(sK10(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f20])).
% 1.52/0.57  fof(f61,plain,(
% 1.52/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_wellord1(X0,X1)) | r2_hidden(k4_tarski(X3,X1),X0) | ~v1_relat_1(X0)) )),
% 1.52/0.57    inference(equality_resolution,[],[f46])).
% 1.52/0.57  fof(f46,plain,(
% 1.52/0.57    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,X2) | k1_wellord1(X0,X1) != X2) )),
% 1.52/0.57    inference(cnf_transformation,[],[f16])).
% 1.52/0.57  fof(f349,plain,(
% 1.52/0.57    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK0),sK2) | r2_hidden(X0,k1_wellord1(sK2,sK1))) ) | ~spl11_35),
% 1.52/0.57    inference(avatar_component_clause,[],[f348])).
% 1.52/0.57  fof(f401,plain,(
% 1.52/0.57    spl11_35 | ~spl11_1 | ~spl11_24 | ~spl11_28),
% 1.52/0.57    inference(avatar_split_clause,[],[f398,f296,f248,f67,f348])).
% 1.52/0.57  fof(f248,plain,(
% 1.52/0.57    spl11_24 <=> r2_hidden(sK0,k1_wellord1(sK2,sK1))),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).
% 1.52/0.57  fof(f296,plain,(
% 1.52/0.57    spl11_28 <=> ! [X1,X0,X2] : (~r2_hidden(X0,k1_wellord1(sK2,X1)) | ~r2_hidden(X1,k3_relat_1(sK2)) | r2_hidden(X2,k1_wellord1(sK2,X1)) | ~r2_hidden(k4_tarski(X2,X0),sK2))),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).
% 1.52/0.57  fof(f398,plain,(
% 1.52/0.57    ( ! [X0] : (~r2_hidden(sK1,k3_relat_1(sK2)) | r2_hidden(X0,k1_wellord1(sK2,sK1)) | ~r2_hidden(k4_tarski(X0,sK0),sK2)) ) | (~spl11_24 | ~spl11_28)),
% 1.52/0.57    inference(resolution,[],[f250,f297])).
% 1.52/0.57  fof(f297,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_wellord1(sK2,X1)) | ~r2_hidden(X1,k3_relat_1(sK2)) | r2_hidden(X2,k1_wellord1(sK2,X1)) | ~r2_hidden(k4_tarski(X2,X0),sK2)) ) | ~spl11_28),
% 1.52/0.57    inference(avatar_component_clause,[],[f296])).
% 1.52/0.57  fof(f250,plain,(
% 1.52/0.57    r2_hidden(sK0,k1_wellord1(sK2,sK1)) | ~spl11_24),
% 1.52/0.57    inference(avatar_component_clause,[],[f248])).
% 1.52/0.57  fof(f394,plain,(
% 1.52/0.57    spl11_24 | ~spl11_4 | spl11_21 | ~spl11_5),
% 1.52/0.57    inference(avatar_split_clause,[],[f392,f87,f232,f82,f248])).
% 1.52/0.57  fof(f392,plain,(
% 1.52/0.57    sK0 = sK1 | ~v1_relat_1(sK2) | r2_hidden(sK0,k1_wellord1(sK2,sK1)) | ~spl11_5),
% 1.52/0.57    inference(resolution,[],[f88,f60])).
% 1.52/0.57  fof(f88,plain,(
% 1.52/0.57    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl11_5),
% 1.52/0.57    inference(avatar_component_clause,[],[f87])).
% 1.52/0.57  fof(f390,plain,(
% 1.52/0.57    ~spl11_7 | spl11_12 | ~spl11_4 | ~spl11_1),
% 1.52/0.57    inference(avatar_split_clause,[],[f385,f67,f82,f146,f98])).
% 1.52/0.57  fof(f98,plain,(
% 1.52/0.57    spl11_7 <=> v1_relat_2(sK2)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 1.52/0.57  fof(f146,plain,(
% 1.52/0.57    spl11_12 <=> r2_hidden(k4_tarski(sK1,sK1),sK2)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).
% 1.52/0.57  fof(f385,plain,(
% 1.52/0.57    ~v1_relat_1(sK2) | r2_hidden(k4_tarski(sK1,sK1),sK2) | ~v1_relat_2(sK2) | ~spl11_1),
% 1.52/0.57    inference(resolution,[],[f69,f27])).
% 1.52/0.57  fof(f27,plain,(
% 1.52/0.57    ( ! [X0,X1] : (~r2_hidden(X1,k3_relat_1(X0)) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(X1,X1),X0) | ~v1_relat_2(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f13])).
% 1.52/0.57  fof(f13,plain,(
% 1.52/0.57    ! [X0] : ((v1_relat_2(X0) <=> ! [X1] : (r2_hidden(k4_tarski(X1,X1),X0) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 1.52/0.57    inference(ennf_transformation,[],[f4])).
% 1.52/0.57  fof(f4,axiom,(
% 1.52/0.57    ! [X0] : (v1_relat_1(X0) => (v1_relat_2(X0) <=> ! [X1] : (r2_hidden(X1,k3_relat_1(X0)) => r2_hidden(k4_tarski(X1,X1),X0))))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_wellord1)).
% 1.52/0.57  fof(f376,plain,(
% 1.52/0.57    spl11_36),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f375])).
% 1.52/0.57  fof(f375,plain,(
% 1.52/0.57    $false | spl11_36),
% 1.52/0.57    inference(resolution,[],[f366,f128])).
% 1.52/0.57  fof(f128,plain,(
% 1.52/0.57    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.52/0.57    inference(duplicate_literal_removal,[],[f127])).
% 1.52/0.57  fof(f127,plain,(
% 1.52/0.57    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.52/0.57    inference(resolution,[],[f59,f58])).
% 1.52/0.57  fof(f366,plain,(
% 1.52/0.57    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) | spl11_36),
% 1.52/0.57    inference(avatar_component_clause,[],[f364])).
% 1.52/0.57  fof(f364,plain,(
% 1.52/0.57    spl11_36 <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_36])])).
% 1.52/0.57  fof(f367,plain,(
% 1.52/0.57    ~spl11_36 | spl11_6 | ~spl11_21),
% 1.52/0.57    inference(avatar_split_clause,[],[f354,f232,f91,f364])).
% 1.52/0.57  fof(f354,plain,(
% 1.52/0.57    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) | (spl11_6 | ~spl11_21)),
% 1.52/0.57    inference(backward_demodulation,[],[f93,f234])).
% 1.52/0.57  fof(f234,plain,(
% 1.52/0.57    sK0 = sK1 | ~spl11_21),
% 1.52/0.57    inference(avatar_component_clause,[],[f232])).
% 1.52/0.57  fof(f93,plain,(
% 1.52/0.57    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | spl11_6),
% 1.52/0.57    inference(avatar_component_clause,[],[f91])).
% 1.52/0.57  fof(f298,plain,(
% 1.52/0.57    spl11_28 | ~spl11_4 | ~spl11_3 | ~spl11_4),
% 1.52/0.57    inference(avatar_split_clause,[],[f294,f82,f77,f82,f296])).
% 1.52/0.57  fof(f77,plain,(
% 1.52/0.57    spl11_3 <=> v2_wellord1(sK2)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 1.52/0.57  fof(f294,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (~v2_wellord1(sK2) | ~v1_relat_1(sK2) | ~r2_hidden(X0,k1_wellord1(sK2,X1)) | ~r2_hidden(k4_tarski(X2,X0),sK2) | r2_hidden(X2,k1_wellord1(sK2,X1)) | ~r2_hidden(X1,k3_relat_1(sK2))) ) | ~spl11_4),
% 1.52/0.57    inference(resolution,[],[f64,f126])).
% 1.52/0.57  fof(f126,plain,(
% 1.52/0.57    ( ! [X0] : (r1_tarski(k1_wellord1(sK2,X0),k3_relat_1(sK2))) ) | ~spl11_4),
% 1.52/0.57    inference(resolution,[],[f48,f84])).
% 1.52/0.57  fof(f48,plain,(
% 1.52/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))) )),
% 1.52/0.57    inference(cnf_transformation,[],[f17])).
% 1.52/0.57  fof(f17,plain,(
% 1.52/0.57    ! [X0,X1] : (r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.52/0.57    inference(ennf_transformation,[],[f6])).
% 1.52/0.57  fof(f6,axiom,(
% 1.52/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_wellord1)).
% 1.52/0.57  fof(f64,plain,(
% 1.52/0.57    ( ! [X4,X2,X3,X1] : (~r1_tarski(k1_wellord1(X1,X2),k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1) | ~r2_hidden(X3,k1_wellord1(X1,X2)) | ~r2_hidden(k4_tarski(X4,X3),X1) | r2_hidden(X4,k1_wellord1(X1,X2)) | ~r2_hidden(X2,k3_relat_1(X1))) )),
% 1.52/0.57    inference(equality_resolution,[],[f54])).
% 1.52/0.57  fof(f54,plain,(
% 1.52/0.57    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X1) | ~v2_wellord1(X1) | ~r1_tarski(X0,k3_relat_1(X1)) | ~r2_hidden(X3,X0) | ~r2_hidden(k4_tarski(X4,X3),X1) | r2_hidden(X4,X0) | ~r2_hidden(X2,k3_relat_1(X1)) | k1_wellord1(X1,X2) != X0) )),
% 1.52/0.57    inference(cnf_transformation,[],[f19])).
% 1.52/0.57  fof(f19,plain,(
% 1.52/0.57    ! [X0,X1] : (((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0) <=> ! [X3] : (! [X4] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X0))) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 1.52/0.57    inference(flattening,[],[f18])).
% 1.52/0.57  fof(f18,plain,(
% 1.52/0.57    ! [X0,X1] : ((((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0) <=> ! [X3] : (! [X4] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X0))) | (~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1))) | ~v1_relat_1(X1))),
% 1.52/0.57    inference(ennf_transformation,[],[f10])).
% 1.52/0.57  fof(f10,plain,(
% 1.52/0.57    ! [X0,X1] : (v1_relat_1(X1) => ((r1_tarski(X0,k3_relat_1(X1)) & v2_wellord1(X1)) => (~(! [X2] : ~(k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) & k3_relat_1(X1) != X0) <=> ! [X3] : (r2_hidden(X3,X0) => ! [X4] : (r2_hidden(k4_tarski(X4,X3),X1) => r2_hidden(X4,X0))))))),
% 1.52/0.57    inference(rectify,[],[f7])).
% 1.69/0.58  fof(f7,axiom,(
% 1.69/0.58    ! [X0,X1] : (v1_relat_1(X1) => ((r1_tarski(X0,k3_relat_1(X1)) & v2_wellord1(X1)) => (~(! [X2] : ~(k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) & k3_relat_1(X1) != X0) <=> ! [X2] : (r2_hidden(X2,X0) => ! [X3] : (r2_hidden(k4_tarski(X3,X2),X1) => r2_hidden(X3,X0))))))),
% 1.69/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_wellord1)).
% 1.69/0.58  fof(f221,plain,(
% 1.69/0.58    ~spl11_10 | spl11_19 | ~spl11_4 | ~spl11_2),
% 1.69/0.58    inference(avatar_split_clause,[],[f211,f72,f82,f219,f116])).
% 1.69/0.58  fof(f116,plain,(
% 1.69/0.58    spl11_10 <=> v6_relat_2(sK2)),
% 1.69/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 1.69/0.58  fof(f72,plain,(
% 1.69/0.58    spl11_2 <=> r2_hidden(sK0,k3_relat_1(sK2))),
% 1.69/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.69/0.58  fof(f211,plain,(
% 1.69/0.58    ( ! [X1] : (~v1_relat_1(sK2) | ~r2_hidden(X1,k3_relat_1(sK2)) | sK0 = X1 | r2_hidden(k4_tarski(sK0,X1),sK2) | r2_hidden(k4_tarski(X1,sK0),sK2) | ~v6_relat_2(sK2)) ) | ~spl11_2),
% 1.69/0.58    inference(resolution,[],[f30,f74])).
% 1.69/0.58  fof(f74,plain,(
% 1.69/0.58    r2_hidden(sK0,k3_relat_1(sK2)) | ~spl11_2),
% 1.69/0.58    inference(avatar_component_clause,[],[f72])).
% 1.69/0.58  fof(f30,plain,(
% 1.69/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X1,k3_relat_1(X0)) | ~v1_relat_1(X0) | ~r2_hidden(X2,k3_relat_1(X0)) | X1 = X2 | r2_hidden(k4_tarski(X1,X2),X0) | r2_hidden(k4_tarski(X2,X1),X0) | ~v6_relat_2(X0)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f14])).
% 1.69/0.58  fof(f14,plain,(
% 1.69/0.58    ! [X0] : ((v6_relat_2(X0) <=> ! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 1.69/0.58    inference(ennf_transformation,[],[f5])).
% 1.69/0.58  fof(f5,axiom,(
% 1.69/0.58    ! [X0] : (v1_relat_1(X0) => (v6_relat_2(X0) <=> ! [X1,X2] : ~(~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))))),
% 1.69/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).
% 1.69/0.58  fof(f119,plain,(
% 1.69/0.58    ~spl11_4 | spl11_10 | ~spl11_3),
% 1.69/0.58    inference(avatar_split_clause,[],[f114,f77,f116,f82])).
% 1.69/0.58  fof(f114,plain,(
% 1.69/0.58    v6_relat_2(sK2) | ~v1_relat_1(sK2) | ~spl11_3),
% 1.69/0.58    inference(resolution,[],[f39,f79])).
% 1.69/0.58  fof(f79,plain,(
% 1.69/0.58    v2_wellord1(sK2) | ~spl11_3),
% 1.69/0.58    inference(avatar_component_clause,[],[f77])).
% 1.69/0.58  fof(f39,plain,(
% 1.69/0.58    ( ! [X0] : (~v2_wellord1(X0) | v6_relat_2(X0) | ~v1_relat_1(X0)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f15])).
% 1.69/0.58  fof(f15,plain,(
% 1.69/0.58    ! [X0] : ((v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 1.69/0.58    inference(ennf_transformation,[],[f3])).
% 1.69/0.58  fof(f3,axiom,(
% 1.69/0.58    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))))),
% 1.69/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).
% 1.69/0.58  fof(f101,plain,(
% 1.69/0.58    ~spl11_4 | spl11_7 | ~spl11_3),
% 1.69/0.58    inference(avatar_split_clause,[],[f96,f77,f98,f82])).
% 1.69/0.58  fof(f96,plain,(
% 1.69/0.58    v1_relat_2(sK2) | ~v1_relat_1(sK2) | ~spl11_3),
% 1.69/0.58    inference(resolution,[],[f36,f79])).
% 1.69/0.58  fof(f36,plain,(
% 1.69/0.58    ( ! [X0] : (~v2_wellord1(X0) | v1_relat_2(X0) | ~v1_relat_1(X0)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f15])).
% 1.69/0.58  fof(f95,plain,(
% 1.69/0.58    spl11_5 | spl11_6),
% 1.69/0.58    inference(avatar_split_clause,[],[f21,f91,f87])).
% 1.69/0.58  fof(f21,plain,(
% 1.69/0.58    r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 1.69/0.58    inference(cnf_transformation,[],[f12])).
% 1.69/0.58  fof(f12,plain,(
% 1.69/0.58    ? [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 1.69/0.58    inference(flattening,[],[f11])).
% 1.69/0.58  fof(f11,plain,(
% 1.69/0.58    ? [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2))) & v1_relat_1(X2))),
% 1.69/0.58    inference(ennf_transformation,[],[f9])).
% 1.69/0.58  fof(f9,negated_conjecture,(
% 1.69/0.58    ~! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 1.69/0.58    inference(negated_conjecture,[],[f8])).
% 1.69/0.58  fof(f8,conjecture,(
% 1.69/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 1.69/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_wellord1)).
% 1.69/0.58  fof(f94,plain,(
% 1.69/0.58    ~spl11_5 | ~spl11_6),
% 1.69/0.58    inference(avatar_split_clause,[],[f22,f91,f87])).
% 1.69/0.58  fof(f22,plain,(
% 1.69/0.58    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 1.69/0.58    inference(cnf_transformation,[],[f12])).
% 1.69/0.58  fof(f85,plain,(
% 1.69/0.58    spl11_4),
% 1.69/0.58    inference(avatar_split_clause,[],[f23,f82])).
% 1.69/0.58  fof(f23,plain,(
% 1.69/0.58    v1_relat_1(sK2)),
% 1.69/0.58    inference(cnf_transformation,[],[f12])).
% 1.69/0.58  fof(f80,plain,(
% 1.69/0.58    spl11_3),
% 1.69/0.58    inference(avatar_split_clause,[],[f24,f77])).
% 1.69/0.58  fof(f24,plain,(
% 1.69/0.58    v2_wellord1(sK2)),
% 1.69/0.58    inference(cnf_transformation,[],[f12])).
% 1.69/0.58  fof(f75,plain,(
% 1.69/0.58    spl11_2),
% 1.69/0.58    inference(avatar_split_clause,[],[f25,f72])).
% 1.69/0.58  fof(f25,plain,(
% 1.69/0.58    r2_hidden(sK0,k3_relat_1(sK2))),
% 1.69/0.58    inference(cnf_transformation,[],[f12])).
% 1.69/0.58  fof(f70,plain,(
% 1.69/0.58    spl11_1),
% 1.69/0.58    inference(avatar_split_clause,[],[f26,f67])).
% 1.69/0.58  fof(f26,plain,(
% 1.69/0.58    r2_hidden(sK1,k3_relat_1(sK2))),
% 1.69/0.58    inference(cnf_transformation,[],[f12])).
% 1.69/0.58  % SZS output end Proof for theBenchmark
% 1.69/0.58  % (6863)------------------------------
% 1.69/0.58  % (6863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.58  % (6863)Termination reason: Refutation
% 1.69/0.58  
% 1.69/0.58  % (6863)Memory used [KB]: 11001
% 1.69/0.58  % (6863)Time elapsed: 0.159 s
% 1.69/0.58  % (6863)------------------------------
% 1.69/0.58  % (6863)------------------------------
% 1.69/0.58  % (6846)Success in time 0.224 s
%------------------------------------------------------------------------------
