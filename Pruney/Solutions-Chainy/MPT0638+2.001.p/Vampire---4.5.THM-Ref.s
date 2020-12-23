%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 320 expanded)
%              Number of leaves         :   33 ( 137 expanded)
%              Depth                    :    8
%              Number of atoms          :  741 (1332 expanded)
%              Number of equality atoms :  124 ( 271 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f800,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f64,f68,f72,f76,f80,f84,f96,f100,f104,f108,f119,f123,f136,f152,f156,f162,f181,f189,f218,f233,f287,f308,f352,f380,f508,f533,f774,f795])).

fof(f795,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | spl10_7
    | ~ spl10_21
    | ~ spl10_98 ),
    inference(avatar_contradiction_clause,[],[f794])).

fof(f794,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | spl10_7
    | ~ spl10_21
    | ~ spl10_98 ),
    inference(subsumption_resolution,[],[f793,f83])).

fof(f83,plain,
    ( sK1 != k6_relat_1(k1_relat_1(sK1))
    | spl10_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl10_7
  <=> sK1 = k6_relat_1(k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f793,plain,
    ( sK1 = k6_relat_1(k1_relat_1(sK1))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_21
    | ~ spl10_98 ),
    inference(subsumption_resolution,[],[f792,f59])).

fof(f59,plain,
    ( v1_relat_1(sK1)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl10_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f792,plain,
    ( ~ v1_relat_1(sK1)
    | sK1 = k6_relat_1(k1_relat_1(sK1))
    | ~ spl10_2
    | ~ spl10_21
    | ~ spl10_98 ),
    inference(subsumption_resolution,[],[f790,f63])).

fof(f63,plain,
    ( v1_funct_1(sK1)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl10_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f790,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK1 = k6_relat_1(k1_relat_1(sK1))
    | ~ spl10_21
    | ~ spl10_98 ),
    inference(trivial_inequality_removal,[],[f786])).

fof(f786,plain,
    ( sK9(k1_relat_1(sK1),sK1) != sK9(k1_relat_1(sK1),sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK1 = k6_relat_1(k1_relat_1(sK1))
    | ~ spl10_21
    | ~ spl10_98 ),
    inference(superposition,[],[f155,f773])).

fof(f773,plain,
    ( sK9(k1_relat_1(sK1),sK1) = k1_funct_1(sK1,sK9(k1_relat_1(sK1),sK1))
    | ~ spl10_98 ),
    inference(avatar_component_clause,[],[f772])).

fof(f772,plain,
    ( spl10_98
  <=> sK9(k1_relat_1(sK1),sK1) = k1_funct_1(sK1,sK9(k1_relat_1(sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_98])])).

fof(f155,plain,
    ( ! [X1] :
        ( sK9(k1_relat_1(X1),X1) != k1_funct_1(X1,sK9(k1_relat_1(X1),X1))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | k6_relat_1(k1_relat_1(X1)) = X1 )
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl10_21
  <=> ! [X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | sK9(k1_relat_1(X1),X1) != k1_funct_1(X1,sK9(k1_relat_1(X1),X1))
        | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f774,plain,
    ( spl10_98
    | ~ spl10_1
    | ~ spl10_2
    | spl10_7
    | ~ spl10_15
    | ~ spl10_70 ),
    inference(avatar_split_clause,[],[f559,f531,f117,f82,f62,f58,f772])).

fof(f117,plain,
    ( spl10_15
  <=> ! [X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | r2_hidden(sK9(k1_relat_1(X1),X1),k1_relat_1(X1))
        | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f531,plain,
    ( spl10_70
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(sK1,X0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_70])])).

fof(f559,plain,
    ( sK9(k1_relat_1(sK1),sK1) = k1_funct_1(sK1,sK9(k1_relat_1(sK1),sK1))
    | ~ spl10_1
    | ~ spl10_2
    | spl10_7
    | ~ spl10_15
    | ~ spl10_70 ),
    inference(subsumption_resolution,[],[f558,f83])).

fof(f558,plain,
    ( sK9(k1_relat_1(sK1),sK1) = k1_funct_1(sK1,sK9(k1_relat_1(sK1),sK1))
    | sK1 = k6_relat_1(k1_relat_1(sK1))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_15
    | ~ spl10_70 ),
    inference(subsumption_resolution,[],[f557,f59])).

fof(f557,plain,
    ( sK9(k1_relat_1(sK1),sK1) = k1_funct_1(sK1,sK9(k1_relat_1(sK1),sK1))
    | ~ v1_relat_1(sK1)
    | sK1 = k6_relat_1(k1_relat_1(sK1))
    | ~ spl10_2
    | ~ spl10_15
    | ~ spl10_70 ),
    inference(subsumption_resolution,[],[f550,f63])).

fof(f550,plain,
    ( sK9(k1_relat_1(sK1),sK1) = k1_funct_1(sK1,sK9(k1_relat_1(sK1),sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK1 = k6_relat_1(k1_relat_1(sK1))
    | ~ spl10_15
    | ~ spl10_70 ),
    inference(resolution,[],[f532,f118])).

fof(f118,plain,
    ( ! [X1] :
        ( r2_hidden(sK9(k1_relat_1(X1),X1),k1_relat_1(X1))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | k6_relat_1(k1_relat_1(X1)) = X1 )
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f117])).

fof(f532,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(sK1,X0) = X0 )
    | ~ spl10_70 ),
    inference(avatar_component_clause,[],[f531])).

fof(f533,plain,
    ( spl10_70
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_11
    | ~ spl10_67 ),
    inference(avatar_split_clause,[],[f518,f506,f98,f74,f70,f66,f531])).

fof(f66,plain,
    ( spl10_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f70,plain,
    ( spl10_4
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f74,plain,
    ( spl10_5
  <=> k2_relat_1(sK0) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f98,plain,
    ( spl10_11
  <=> ! [X0,X2] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | r2_hidden(sK7(X0,X2),k1_relat_1(X0))
        | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f506,plain,
    ( spl10_67
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(sK1,X0) = X0
        | ~ r2_hidden(sK7(sK0,X0),k1_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_67])])).

fof(f518,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(sK1,X0) = X0 )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_11
    | ~ spl10_67 ),
    inference(duplicate_literal_removal,[],[f517])).

fof(f517,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(sK1,X0) = X0
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_11
    | ~ spl10_67 ),
    inference(forward_demodulation,[],[f516,f75])).

fof(f75,plain,
    ( k2_relat_1(sK0) = k1_relat_1(sK1)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f516,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,X0) = X0
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ r2_hidden(X0,k2_relat_1(sK0)) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_67 ),
    inference(subsumption_resolution,[],[f515,f67])).

fof(f67,plain,
    ( v1_relat_1(sK0)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f515,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,X0) = X0
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ v1_relat_1(sK0)
        | ~ r2_hidden(X0,k2_relat_1(sK0)) )
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_67 ),
    inference(subsumption_resolution,[],[f513,f71])).

fof(f71,plain,
    ( v1_funct_1(sK0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f513,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,X0) = X0
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0)
        | ~ r2_hidden(X0,k2_relat_1(sK0)) )
    | ~ spl10_11
    | ~ spl10_67 ),
    inference(resolution,[],[f507,f99])).

fof(f99,plain,
    ( ! [X2,X0] :
        ( r2_hidden(sK7(X0,X2),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(X2,k2_relat_1(X0)) )
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f98])).

fof(f507,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK7(sK0,X0),k1_relat_1(sK0))
        | k1_funct_1(sK1,X0) = X0
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl10_67 ),
    inference(avatar_component_clause,[],[f506])).

fof(f508,plain,
    ( spl10_67
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_12
    | ~ spl10_52 ),
    inference(avatar_split_clause,[],[f392,f378,f102,f74,f70,f66,f506])).

fof(f102,plain,
    ( spl10_12
  <=> ! [X0,X2] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_funct_1(X0,sK7(X0,X2)) = X2
        | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f378,plain,
    ( spl10_52
  <=> ! [X10] :
        ( ~ r2_hidden(X10,k1_relat_1(sK0))
        | k1_funct_1(sK0,X10) = k1_funct_1(sK1,k1_funct_1(sK0,X10)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_52])])).

fof(f392,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(sK1,X0) = X0
        | ~ r2_hidden(sK7(sK0,X0),k1_relat_1(sK0)) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_12
    | ~ spl10_52 ),
    inference(forward_demodulation,[],[f391,f75])).

fof(f391,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,X0) = X0
        | ~ r2_hidden(sK7(sK0,X0),k1_relat_1(sK0))
        | ~ r2_hidden(X0,k2_relat_1(sK0)) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_12
    | ~ spl10_52 ),
    inference(subsumption_resolution,[],[f390,f67])).

fof(f390,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,X0) = X0
        | ~ r2_hidden(sK7(sK0,X0),k1_relat_1(sK0))
        | ~ v1_relat_1(sK0)
        | ~ r2_hidden(X0,k2_relat_1(sK0)) )
    | ~ spl10_4
    | ~ spl10_12
    | ~ spl10_52 ),
    inference(subsumption_resolution,[],[f386,f71])).

fof(f386,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,X0) = X0
        | ~ r2_hidden(sK7(sK0,X0),k1_relat_1(sK0))
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0)
        | ~ r2_hidden(X0,k2_relat_1(sK0)) )
    | ~ spl10_12
    | ~ spl10_52 ),
    inference(superposition,[],[f379,f103])).

fof(f103,plain,
    ( ! [X2,X0] :
        ( k1_funct_1(X0,sK7(X0,X2)) = X2
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(X2,k2_relat_1(X0)) )
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f102])).

fof(f379,plain,
    ( ! [X10] :
        ( k1_funct_1(sK0,X10) = k1_funct_1(sK1,k1_funct_1(sK0,X10))
        | ~ r2_hidden(X10,k1_relat_1(sK0)) )
    | ~ spl10_52 ),
    inference(avatar_component_clause,[],[f378])).

fof(f380,plain,
    ( spl10_52
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_13
    | ~ spl10_49 ),
    inference(avatar_split_clause,[],[f366,f350,f106,f70,f66,f378])).

fof(f106,plain,
    ( spl10_13
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(X1,k1_relat_1(X0))
        | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f350,plain,
    ( spl10_49
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK0)
        | ~ r2_hidden(X0,k1_relat_1(sK0))
        | k1_funct_1(sK1,k1_funct_1(sK0,X0)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).

fof(f366,plain,
    ( ! [X10] :
        ( ~ r2_hidden(X10,k1_relat_1(sK0))
        | k1_funct_1(sK0,X10) = k1_funct_1(sK1,k1_funct_1(sK0,X10)) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_13
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f365,f67])).

fof(f365,plain,
    ( ! [X10] :
        ( ~ r2_hidden(X10,k1_relat_1(sK0))
        | k1_funct_1(sK0,X10) = k1_funct_1(sK1,k1_funct_1(sK0,X10))
        | ~ v1_relat_1(sK0) )
    | ~ spl10_4
    | ~ spl10_13
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f363,f71])).

fof(f363,plain,
    ( ! [X10] :
        ( ~ r2_hidden(X10,k1_relat_1(sK0))
        | k1_funct_1(sK0,X10) = k1_funct_1(sK1,k1_funct_1(sK0,X10))
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl10_13
    | ~ spl10_49 ),
    inference(duplicate_literal_removal,[],[f362])).

fof(f362,plain,
    ( ! [X10] :
        ( ~ r2_hidden(X10,k1_relat_1(sK0))
        | k1_funct_1(sK0,X10) = k1_funct_1(sK1,k1_funct_1(sK0,X10))
        | ~ v1_funct_1(sK0)
        | ~ r2_hidden(X10,k1_relat_1(sK0))
        | ~ v1_relat_1(sK0) )
    | ~ spl10_13
    | ~ spl10_49 ),
    inference(resolution,[],[f351,f107])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(X1,k1_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f106])).

fof(f351,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK0)
        | ~ r2_hidden(X0,k1_relat_1(sK0))
        | k1_funct_1(sK1,k1_funct_1(sK0,X0)) = X1 )
    | ~ spl10_49 ),
    inference(avatar_component_clause,[],[f350])).

fof(f352,plain,
    ( spl10_49
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_44 ),
    inference(avatar_split_clause,[],[f315,f306,f150,f121,f350])).

fof(f121,plain,
    ( spl10_16
  <=> ! [X0] :
        ( r2_hidden(k1_funct_1(sK0,X0),k1_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f150,plain,
    ( spl10_20
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | k1_funct_1(sK1,X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f306,plain,
    ( spl10_44
  <=> ! [X3,X2] :
        ( r2_hidden(k4_tarski(k1_funct_1(sK0,X2),X3),sK1)
        | ~ r2_hidden(k4_tarski(X2,X3),sK0)
        | ~ r2_hidden(X2,k1_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).

fof(f315,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK0)
        | ~ r2_hidden(X0,k1_relat_1(sK0))
        | k1_funct_1(sK1,k1_funct_1(sK0,X0)) = X1 )
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_44 ),
    inference(subsumption_resolution,[],[f313,f122])).

fof(f122,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK0,X0),k1_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(sK0)) )
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f121])).

fof(f313,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK0)
        | ~ r2_hidden(X0,k1_relat_1(sK0))
        | ~ r2_hidden(k1_funct_1(sK0,X0),k1_relat_1(sK1))
        | k1_funct_1(sK1,k1_funct_1(sK0,X0)) = X1 )
    | ~ spl10_20
    | ~ spl10_44 ),
    inference(resolution,[],[f307,f151])).

fof(f151,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(sK1,X0) = X1 )
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f150])).

fof(f307,plain,
    ( ! [X2,X3] :
        ( r2_hidden(k4_tarski(k1_funct_1(sK0,X2),X3),sK1)
        | ~ r2_hidden(k4_tarski(X2,X3),sK0)
        | ~ r2_hidden(X2,k1_relat_1(sK0)) )
    | ~ spl10_44 ),
    inference(avatar_component_clause,[],[f306])).

fof(f308,plain,
    ( spl10_44
    | ~ spl10_30
    | ~ spl10_42 ),
    inference(avatar_split_clause,[],[f293,f285,f216,f306])).

fof(f216,plain,
    ( spl10_30
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(sK4(sK0,sK1,X0,X1),X1),sK1)
        | ~ r2_hidden(k4_tarski(X0,X1),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f285,plain,
    ( spl10_42
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK0)
        | ~ r2_hidden(X0,k1_relat_1(sK0))
        | k1_funct_1(sK0,X0) = sK4(sK0,sK1,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f293,plain,
    ( ! [X2,X3] :
        ( r2_hidden(k4_tarski(k1_funct_1(sK0,X2),X3),sK1)
        | ~ r2_hidden(k4_tarski(X2,X3),sK0)
        | ~ r2_hidden(X2,k1_relat_1(sK0)) )
    | ~ spl10_30
    | ~ spl10_42 ),
    inference(duplicate_literal_removal,[],[f292])).

fof(f292,plain,
    ( ! [X2,X3] :
        ( r2_hidden(k4_tarski(k1_funct_1(sK0,X2),X3),sK1)
        | ~ r2_hidden(k4_tarski(X2,X3),sK0)
        | ~ r2_hidden(X2,k1_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(X2,X3),sK0) )
    | ~ spl10_30
    | ~ spl10_42 ),
    inference(superposition,[],[f217,f286])).

fof(f286,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK0,X0) = sK4(sK0,sK1,X0,X1)
        | ~ r2_hidden(X0,k1_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(X0,X1),sK0) )
    | ~ spl10_42 ),
    inference(avatar_component_clause,[],[f285])).

fof(f217,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK4(sK0,sK1,X0,X1),X1),sK1)
        | ~ r2_hidden(k4_tarski(X0,X1),sK0) )
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f216])).

fof(f287,plain,
    ( spl10_42
    | ~ spl10_22
    | ~ spl10_33 ),
    inference(avatar_split_clause,[],[f240,f231,f160,f285])).

fof(f160,plain,
    ( spl10_22
  <=> ! [X3,X2] :
        ( ~ r2_hidden(X2,k1_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(X2,X3),sK0)
        | k1_funct_1(sK0,X2) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f231,plain,
    ( spl10_33
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(X0,sK4(sK0,sK1,X0,X1)),sK0)
        | ~ r2_hidden(k4_tarski(X0,X1),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).

fof(f240,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK0)
        | ~ r2_hidden(X0,k1_relat_1(sK0))
        | k1_funct_1(sK0,X0) = sK4(sK0,sK1,X0,X1) )
    | ~ spl10_22
    | ~ spl10_33 ),
    inference(resolution,[],[f232,f161])).

fof(f161,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK0)
        | ~ r2_hidden(X2,k1_relat_1(sK0))
        | k1_funct_1(sK0,X2) = X3 )
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f160])).

fof(f232,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,sK4(sK0,sK1,X0,X1)),sK0)
        | ~ r2_hidden(k4_tarski(X0,X1),sK0) )
    | ~ spl10_33 ),
    inference(avatar_component_clause,[],[f231])).

fof(f233,plain,
    ( spl10_33
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_6
    | ~ spl10_27 ),
    inference(avatar_split_clause,[],[f209,f187,f78,f66,f58,f231])).

fof(f78,plain,
    ( spl10_6
  <=> sK0 = k5_relat_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f187,plain,
    ( spl10_27
  <=> ! [X1,X3,X0,X4] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k5_relat_1(X0,X1))
        | r2_hidden(k4_tarski(X3,sK4(X0,X1,X3,X4)),X0)
        | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f209,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,sK4(sK0,sK1,X0,X1)),sK0)
        | ~ r2_hidden(k4_tarski(X0,X1),sK0) )
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_6
    | ~ spl10_27 ),
    inference(subsumption_resolution,[],[f208,f59])).

fof(f208,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK1)
        | r2_hidden(k4_tarski(X0,sK4(sK0,sK1,X0,X1)),sK0)
        | ~ r2_hidden(k4_tarski(X0,X1),sK0) )
    | ~ spl10_3
    | ~ spl10_6
    | ~ spl10_27 ),
    inference(subsumption_resolution,[],[f207,f67])).

fof(f207,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK0)
        | ~ v1_relat_1(sK1)
        | r2_hidden(k4_tarski(X0,sK4(sK0,sK1,X0,X1)),sK0)
        | ~ r2_hidden(k4_tarski(X0,X1),sK0) )
    | ~ spl10_6
    | ~ spl10_27 ),
    inference(duplicate_literal_removal,[],[f206])).

fof(f206,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK0)
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(sK0)
        | r2_hidden(k4_tarski(X0,sK4(sK0,sK1,X0,X1)),sK0)
        | ~ r2_hidden(k4_tarski(X0,X1),sK0) )
    | ~ spl10_6
    | ~ spl10_27 ),
    inference(superposition,[],[f188,f79])).

fof(f79,plain,
    ( sK0 = k5_relat_1(sK0,sK1)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f188,plain,
    ( ! [X4,X0,X3,X1] :
        ( ~ v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(X3,sK4(X0,X1,X3,X4)),X0)
        | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) )
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f187])).

fof(f218,plain,
    ( spl10_30
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_6
    | ~ spl10_25 ),
    inference(avatar_split_clause,[],[f205,f179,f78,f66,f58,f216])).

fof(f179,plain,
    ( spl10_25
  <=> ! [X1,X3,X0,X4] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k5_relat_1(X0,X1))
        | r2_hidden(k4_tarski(sK4(X0,X1,X3,X4),X4),X1)
        | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f205,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK4(sK0,sK1,X0,X1),X1),sK1)
        | ~ r2_hidden(k4_tarski(X0,X1),sK0) )
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_6
    | ~ spl10_25 ),
    inference(subsumption_resolution,[],[f204,f59])).

fof(f204,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK1)
        | r2_hidden(k4_tarski(sK4(sK0,sK1,X0,X1),X1),sK1)
        | ~ r2_hidden(k4_tarski(X0,X1),sK0) )
    | ~ spl10_3
    | ~ spl10_6
    | ~ spl10_25 ),
    inference(subsumption_resolution,[],[f203,f67])).

fof(f203,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK0)
        | ~ v1_relat_1(sK1)
        | r2_hidden(k4_tarski(sK4(sK0,sK1,X0,X1),X1),sK1)
        | ~ r2_hidden(k4_tarski(X0,X1),sK0) )
    | ~ spl10_6
    | ~ spl10_25 ),
    inference(duplicate_literal_removal,[],[f202])).

fof(f202,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK0)
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(sK0)
        | r2_hidden(k4_tarski(sK4(sK0,sK1,X0,X1),X1),sK1)
        | ~ r2_hidden(k4_tarski(X0,X1),sK0) )
    | ~ spl10_6
    | ~ spl10_25 ),
    inference(superposition,[],[f180,f79])).

fof(f180,plain,
    ( ! [X4,X0,X3,X1] :
        ( ~ v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(sK4(X0,X1,X3,X4),X4),X1)
        | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) )
    | ~ spl10_25 ),
    inference(avatar_component_clause,[],[f179])).

fof(f189,plain,(
    spl10_27 ),
    inference(avatar_split_clause,[],[f45,f187])).

fof(f45,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X3,sK4(X0,X1,X3,X4)),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X3,sK4(X0,X1,X3,X4)),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(f181,plain,(
    spl10_25 ),
    inference(avatar_split_clause,[],[f44,f179])).

fof(f44,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(sK4(X0,X1,X3,X4),X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK4(X0,X1,X3,X4),X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f162,plain,
    ( spl10_22
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_17 ),
    inference(avatar_split_clause,[],[f148,f134,f70,f66,f160])).

fof(f134,plain,
    ( spl10_17
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(X1,k1_relat_1(X0))
        | ~ r2_hidden(k4_tarski(X1,X2),X0)
        | k1_funct_1(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f148,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k1_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(X2,X3),sK0)
        | k1_funct_1(sK0,X2) = X3 )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f146,f67])).

fof(f146,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(sK0)
        | ~ r2_hidden(X2,k1_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(X2,X3),sK0)
        | k1_funct_1(sK0,X2) = X3 )
    | ~ spl10_4
    | ~ spl10_17 ),
    inference(resolution,[],[f135,f71])).

fof(f135,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(X1,k1_relat_1(X0))
        | ~ r2_hidden(k4_tarski(X1,X2),X0)
        | k1_funct_1(X0,X1) = X2 )
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f134])).

fof(f156,plain,(
    spl10_21 ),
    inference(avatar_split_clause,[],[f55,f154])).

fof(f55,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | sK9(k1_relat_1(X1),X1) != k1_funct_1(X1,sK9(k1_relat_1(X1),X1))
      | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | sK9(X0,X1) != k1_funct_1(X1,sK9(X0,X1))
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(f152,plain,
    ( spl10_20
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_17 ),
    inference(avatar_split_clause,[],[f147,f134,f62,f58,f150])).

fof(f147,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | k1_funct_1(sK1,X0) = X1 )
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f145,f59])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | k1_funct_1(sK1,X0) = X1 )
    | ~ spl10_2
    | ~ spl10_17 ),
    inference(resolution,[],[f135,f63])).

fof(f136,plain,(
    spl10_17 ),
    inference(avatar_split_clause,[],[f37,f134])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(f123,plain,
    ( spl10_16
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f115,f94,f74,f70,f66,f121])).

fof(f94,plain,
    ( spl10_10
  <=> ! [X3,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(X3,k1_relat_1(X0))
        | r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f115,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK0,X0),k1_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(sK0)) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f114,f67])).

fof(f114,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK0,X0),k1_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(sK0))
        | ~ v1_relat_1(sK0) )
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f113,f71])).

fof(f113,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK0,X0),k1_relat_1(sK1))
        | ~ v1_funct_1(sK0)
        | ~ r2_hidden(X0,k1_relat_1(sK0))
        | ~ v1_relat_1(sK0) )
    | ~ spl10_5
    | ~ spl10_10 ),
    inference(superposition,[],[f95,f75])).

fof(f95,plain,
    ( ! [X0,X3] :
        ( r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(X3,k1_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f94])).

fof(f119,plain,(
    spl10_15 ),
    inference(avatar_split_clause,[],[f56,f117])).

fof(f56,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | r2_hidden(sK9(k1_relat_1(X1),X1),k1_relat_1(X1))
      | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | r2_hidden(sK9(X0,X1),X0)
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f108,plain,(
    spl10_13 ),
    inference(avatar_split_clause,[],[f50,f106])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f104,plain,(
    spl10_12 ),
    inference(avatar_split_clause,[],[f48,f102])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK7(X0,X2)) = X2
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK7(X0,X2)) = X2
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f100,plain,(
    spl10_11 ),
    inference(avatar_split_clause,[],[f49,f98])).

fof(f49,plain,(
    ! [X2,X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK7(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK7(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f96,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f47,f94])).

fof(f47,plain,(
    ! [X0,X3] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f84,plain,(
    ~ spl10_7 ),
    inference(avatar_split_clause,[],[f20,f82])).

fof(f20,plain,(
    sK1 != k6_relat_1(k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(X0,X1) = X0
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(X0,X1) = X0
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X0,X1) = X0
                & k2_relat_1(X0) = k1_relat_1(X1) )
             => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k2_relat_1(X0) = k1_relat_1(X1) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).

fof(f80,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f19,f78])).

fof(f19,plain,(
    sK0 = k5_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f76,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f18,f74])).

fof(f18,plain,(
    k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f72,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f22,f70])).

fof(f22,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f68,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f21,f66])).

fof(f21,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f64,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f17,f62])).

fof(f17,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f60,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f16,f58])).

fof(f16,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:40:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (5743)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.45  % (5743)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f800,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f60,f64,f68,f72,f76,f80,f84,f96,f100,f104,f108,f119,f123,f136,f152,f156,f162,f181,f189,f218,f233,f287,f308,f352,f380,f508,f533,f774,f795])).
% 0.21/0.45  fof(f795,plain,(
% 0.21/0.45    ~spl10_1 | ~spl10_2 | spl10_7 | ~spl10_21 | ~spl10_98),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f794])).
% 0.21/0.45  fof(f794,plain,(
% 0.21/0.45    $false | (~spl10_1 | ~spl10_2 | spl10_7 | ~spl10_21 | ~spl10_98)),
% 0.21/0.45    inference(subsumption_resolution,[],[f793,f83])).
% 0.21/0.45  fof(f83,plain,(
% 0.21/0.45    sK1 != k6_relat_1(k1_relat_1(sK1)) | spl10_7),
% 0.21/0.45    inference(avatar_component_clause,[],[f82])).
% 0.21/0.45  fof(f82,plain,(
% 0.21/0.45    spl10_7 <=> sK1 = k6_relat_1(k1_relat_1(sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.21/0.45  fof(f793,plain,(
% 0.21/0.45    sK1 = k6_relat_1(k1_relat_1(sK1)) | (~spl10_1 | ~spl10_2 | ~spl10_21 | ~spl10_98)),
% 0.21/0.45    inference(subsumption_resolution,[],[f792,f59])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    v1_relat_1(sK1) | ~spl10_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f58])).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    spl10_1 <=> v1_relat_1(sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.21/0.45  fof(f792,plain,(
% 0.21/0.45    ~v1_relat_1(sK1) | sK1 = k6_relat_1(k1_relat_1(sK1)) | (~spl10_2 | ~spl10_21 | ~spl10_98)),
% 0.21/0.45    inference(subsumption_resolution,[],[f790,f63])).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    v1_funct_1(sK1) | ~spl10_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f62])).
% 0.21/0.45  fof(f62,plain,(
% 0.21/0.45    spl10_2 <=> v1_funct_1(sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.21/0.45  fof(f790,plain,(
% 0.21/0.45    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | sK1 = k6_relat_1(k1_relat_1(sK1)) | (~spl10_21 | ~spl10_98)),
% 0.21/0.45    inference(trivial_inequality_removal,[],[f786])).
% 0.21/0.45  fof(f786,plain,(
% 0.21/0.45    sK9(k1_relat_1(sK1),sK1) != sK9(k1_relat_1(sK1),sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | sK1 = k6_relat_1(k1_relat_1(sK1)) | (~spl10_21 | ~spl10_98)),
% 0.21/0.45    inference(superposition,[],[f155,f773])).
% 0.21/0.45  fof(f773,plain,(
% 0.21/0.45    sK9(k1_relat_1(sK1),sK1) = k1_funct_1(sK1,sK9(k1_relat_1(sK1),sK1)) | ~spl10_98),
% 0.21/0.45    inference(avatar_component_clause,[],[f772])).
% 0.21/0.45  fof(f772,plain,(
% 0.21/0.45    spl10_98 <=> sK9(k1_relat_1(sK1),sK1) = k1_funct_1(sK1,sK9(k1_relat_1(sK1),sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_98])])).
% 0.21/0.45  fof(f155,plain,(
% 0.21/0.45    ( ! [X1] : (sK9(k1_relat_1(X1),X1) != k1_funct_1(X1,sK9(k1_relat_1(X1),X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k6_relat_1(k1_relat_1(X1)) = X1) ) | ~spl10_21),
% 0.21/0.45    inference(avatar_component_clause,[],[f154])).
% 0.21/0.45  fof(f154,plain,(
% 0.21/0.45    spl10_21 <=> ! [X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | sK9(k1_relat_1(X1),X1) != k1_funct_1(X1,sK9(k1_relat_1(X1),X1)) | k6_relat_1(k1_relat_1(X1)) = X1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).
% 0.21/0.45  fof(f774,plain,(
% 0.21/0.45    spl10_98 | ~spl10_1 | ~spl10_2 | spl10_7 | ~spl10_15 | ~spl10_70),
% 0.21/0.45    inference(avatar_split_clause,[],[f559,f531,f117,f82,f62,f58,f772])).
% 0.21/0.45  fof(f117,plain,(
% 0.21/0.45    spl10_15 <=> ! [X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | r2_hidden(sK9(k1_relat_1(X1),X1),k1_relat_1(X1)) | k6_relat_1(k1_relat_1(X1)) = X1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 0.21/0.45  fof(f531,plain,(
% 0.21/0.45    spl10_70 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,X0) = X0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_70])])).
% 0.21/0.45  fof(f559,plain,(
% 0.21/0.45    sK9(k1_relat_1(sK1),sK1) = k1_funct_1(sK1,sK9(k1_relat_1(sK1),sK1)) | (~spl10_1 | ~spl10_2 | spl10_7 | ~spl10_15 | ~spl10_70)),
% 0.21/0.45    inference(subsumption_resolution,[],[f558,f83])).
% 0.21/0.45  fof(f558,plain,(
% 0.21/0.45    sK9(k1_relat_1(sK1),sK1) = k1_funct_1(sK1,sK9(k1_relat_1(sK1),sK1)) | sK1 = k6_relat_1(k1_relat_1(sK1)) | (~spl10_1 | ~spl10_2 | ~spl10_15 | ~spl10_70)),
% 0.21/0.45    inference(subsumption_resolution,[],[f557,f59])).
% 0.21/0.45  fof(f557,plain,(
% 0.21/0.45    sK9(k1_relat_1(sK1),sK1) = k1_funct_1(sK1,sK9(k1_relat_1(sK1),sK1)) | ~v1_relat_1(sK1) | sK1 = k6_relat_1(k1_relat_1(sK1)) | (~spl10_2 | ~spl10_15 | ~spl10_70)),
% 0.21/0.45    inference(subsumption_resolution,[],[f550,f63])).
% 0.21/0.45  fof(f550,plain,(
% 0.21/0.45    sK9(k1_relat_1(sK1),sK1) = k1_funct_1(sK1,sK9(k1_relat_1(sK1),sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | sK1 = k6_relat_1(k1_relat_1(sK1)) | (~spl10_15 | ~spl10_70)),
% 0.21/0.45    inference(resolution,[],[f532,f118])).
% 0.21/0.45  fof(f118,plain,(
% 0.21/0.45    ( ! [X1] : (r2_hidden(sK9(k1_relat_1(X1),X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k6_relat_1(k1_relat_1(X1)) = X1) ) | ~spl10_15),
% 0.21/0.45    inference(avatar_component_clause,[],[f117])).
% 0.21/0.45  fof(f532,plain,(
% 0.21/0.45    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,X0) = X0) ) | ~spl10_70),
% 0.21/0.45    inference(avatar_component_clause,[],[f531])).
% 0.21/0.45  fof(f533,plain,(
% 0.21/0.45    spl10_70 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_11 | ~spl10_67),
% 0.21/0.45    inference(avatar_split_clause,[],[f518,f506,f98,f74,f70,f66,f531])).
% 0.21/0.45  fof(f66,plain,(
% 0.21/0.45    spl10_3 <=> v1_relat_1(sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.21/0.45  fof(f70,plain,(
% 0.21/0.45    spl10_4 <=> v1_funct_1(sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.21/0.45  fof(f74,plain,(
% 0.21/0.45    spl10_5 <=> k2_relat_1(sK0) = k1_relat_1(sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.21/0.45  fof(f98,plain,(
% 0.21/0.45    spl10_11 <=> ! [X0,X2] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK7(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,k2_relat_1(X0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.21/0.45  fof(f506,plain,(
% 0.21/0.45    spl10_67 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,X0) = X0 | ~r2_hidden(sK7(sK0,X0),k1_relat_1(sK0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_67])])).
% 0.21/0.45  fof(f518,plain,(
% 0.21/0.45    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,X0) = X0) ) | (~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_11 | ~spl10_67)),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f517])).
% 0.21/0.45  fof(f517,plain,(
% 0.21/0.45    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,X0) = X0 | ~r2_hidden(X0,k1_relat_1(sK1))) ) | (~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_11 | ~spl10_67)),
% 0.21/0.45    inference(forward_demodulation,[],[f516,f75])).
% 0.21/0.45  fof(f75,plain,(
% 0.21/0.45    k2_relat_1(sK0) = k1_relat_1(sK1) | ~spl10_5),
% 0.21/0.45    inference(avatar_component_clause,[],[f74])).
% 0.21/0.45  fof(f516,plain,(
% 0.21/0.45    ( ! [X0] : (k1_funct_1(sK1,X0) = X0 | ~r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(X0,k2_relat_1(sK0))) ) | (~spl10_3 | ~spl10_4 | ~spl10_11 | ~spl10_67)),
% 0.21/0.45    inference(subsumption_resolution,[],[f515,f67])).
% 0.21/0.45  fof(f67,plain,(
% 0.21/0.45    v1_relat_1(sK0) | ~spl10_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f66])).
% 0.21/0.45  fof(f515,plain,(
% 0.21/0.45    ( ! [X0] : (k1_funct_1(sK1,X0) = X0 | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK0) | ~r2_hidden(X0,k2_relat_1(sK0))) ) | (~spl10_4 | ~spl10_11 | ~spl10_67)),
% 0.21/0.45    inference(subsumption_resolution,[],[f513,f71])).
% 0.21/0.45  fof(f71,plain,(
% 0.21/0.45    v1_funct_1(sK0) | ~spl10_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f70])).
% 0.21/0.45  fof(f513,plain,(
% 0.21/0.45    ( ! [X0] : (k1_funct_1(sK1,X0) = X0 | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~r2_hidden(X0,k2_relat_1(sK0))) ) | (~spl10_11 | ~spl10_67)),
% 0.21/0.45    inference(resolution,[],[f507,f99])).
% 0.21/0.45  fof(f99,plain,(
% 0.21/0.45    ( ! [X2,X0] : (r2_hidden(sK7(X0,X2),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X2,k2_relat_1(X0))) ) | ~spl10_11),
% 0.21/0.45    inference(avatar_component_clause,[],[f98])).
% 0.21/0.45  fof(f507,plain,(
% 0.21/0.45    ( ! [X0] : (~r2_hidden(sK7(sK0,X0),k1_relat_1(sK0)) | k1_funct_1(sK1,X0) = X0 | ~r2_hidden(X0,k1_relat_1(sK1))) ) | ~spl10_67),
% 0.21/0.45    inference(avatar_component_clause,[],[f506])).
% 0.21/0.45  fof(f508,plain,(
% 0.21/0.45    spl10_67 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_12 | ~spl10_52),
% 0.21/0.45    inference(avatar_split_clause,[],[f392,f378,f102,f74,f70,f66,f506])).
% 0.21/0.45  fof(f102,plain,(
% 0.21/0.45    spl10_12 <=> ! [X0,X2] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK7(X0,X2)) = X2 | ~r2_hidden(X2,k2_relat_1(X0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 0.21/0.45  fof(f378,plain,(
% 0.21/0.45    spl10_52 <=> ! [X10] : (~r2_hidden(X10,k1_relat_1(sK0)) | k1_funct_1(sK0,X10) = k1_funct_1(sK1,k1_funct_1(sK0,X10)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_52])])).
% 0.21/0.45  fof(f392,plain,(
% 0.21/0.45    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,X0) = X0 | ~r2_hidden(sK7(sK0,X0),k1_relat_1(sK0))) ) | (~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_12 | ~spl10_52)),
% 0.21/0.45    inference(forward_demodulation,[],[f391,f75])).
% 0.21/0.45  fof(f391,plain,(
% 0.21/0.45    ( ! [X0] : (k1_funct_1(sK1,X0) = X0 | ~r2_hidden(sK7(sK0,X0),k1_relat_1(sK0)) | ~r2_hidden(X0,k2_relat_1(sK0))) ) | (~spl10_3 | ~spl10_4 | ~spl10_12 | ~spl10_52)),
% 0.21/0.45    inference(subsumption_resolution,[],[f390,f67])).
% 0.21/0.45  fof(f390,plain,(
% 0.21/0.45    ( ! [X0] : (k1_funct_1(sK1,X0) = X0 | ~r2_hidden(sK7(sK0,X0),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | ~r2_hidden(X0,k2_relat_1(sK0))) ) | (~spl10_4 | ~spl10_12 | ~spl10_52)),
% 0.21/0.45    inference(subsumption_resolution,[],[f386,f71])).
% 0.21/0.45  fof(f386,plain,(
% 0.21/0.45    ( ! [X0] : (k1_funct_1(sK1,X0) = X0 | ~r2_hidden(sK7(sK0,X0),k1_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~r2_hidden(X0,k2_relat_1(sK0))) ) | (~spl10_12 | ~spl10_52)),
% 0.21/0.45    inference(superposition,[],[f379,f103])).
% 0.21/0.45  fof(f103,plain,(
% 0.21/0.45    ( ! [X2,X0] : (k1_funct_1(X0,sK7(X0,X2)) = X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X2,k2_relat_1(X0))) ) | ~spl10_12),
% 0.21/0.45    inference(avatar_component_clause,[],[f102])).
% 0.21/0.45  fof(f379,plain,(
% 0.21/0.45    ( ! [X10] : (k1_funct_1(sK0,X10) = k1_funct_1(sK1,k1_funct_1(sK0,X10)) | ~r2_hidden(X10,k1_relat_1(sK0))) ) | ~spl10_52),
% 0.21/0.45    inference(avatar_component_clause,[],[f378])).
% 0.21/0.45  fof(f380,plain,(
% 0.21/0.45    spl10_52 | ~spl10_3 | ~spl10_4 | ~spl10_13 | ~spl10_49),
% 0.21/0.45    inference(avatar_split_clause,[],[f366,f350,f106,f70,f66,f378])).
% 0.21/0.45  fof(f106,plain,(
% 0.21/0.45    spl10_13 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.21/0.45  fof(f350,plain,(
% 0.21/0.45    spl10_49 <=> ! [X1,X0] : (~r2_hidden(k4_tarski(X0,X1),sK0) | ~r2_hidden(X0,k1_relat_1(sK0)) | k1_funct_1(sK1,k1_funct_1(sK0,X0)) = X1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).
% 0.21/0.45  fof(f366,plain,(
% 0.21/0.45    ( ! [X10] : (~r2_hidden(X10,k1_relat_1(sK0)) | k1_funct_1(sK0,X10) = k1_funct_1(sK1,k1_funct_1(sK0,X10))) ) | (~spl10_3 | ~spl10_4 | ~spl10_13 | ~spl10_49)),
% 0.21/0.45    inference(subsumption_resolution,[],[f365,f67])).
% 0.21/0.45  fof(f365,plain,(
% 0.21/0.45    ( ! [X10] : (~r2_hidden(X10,k1_relat_1(sK0)) | k1_funct_1(sK0,X10) = k1_funct_1(sK1,k1_funct_1(sK0,X10)) | ~v1_relat_1(sK0)) ) | (~spl10_4 | ~spl10_13 | ~spl10_49)),
% 0.21/0.45    inference(subsumption_resolution,[],[f363,f71])).
% 0.21/0.45  fof(f363,plain,(
% 0.21/0.45    ( ! [X10] : (~r2_hidden(X10,k1_relat_1(sK0)) | k1_funct_1(sK0,X10) = k1_funct_1(sK1,k1_funct_1(sK0,X10)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)) ) | (~spl10_13 | ~spl10_49)),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f362])).
% 0.21/0.45  fof(f362,plain,(
% 0.21/0.45    ( ! [X10] : (~r2_hidden(X10,k1_relat_1(sK0)) | k1_funct_1(sK0,X10) = k1_funct_1(sK1,k1_funct_1(sK0,X10)) | ~v1_funct_1(sK0) | ~r2_hidden(X10,k1_relat_1(sK0)) | ~v1_relat_1(sK0)) ) | (~spl10_13 | ~spl10_49)),
% 0.21/0.45    inference(resolution,[],[f351,f107])).
% 0.21/0.45  fof(f107,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl10_13),
% 0.21/0.45    inference(avatar_component_clause,[],[f106])).
% 0.21/0.45  fof(f351,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK0) | ~r2_hidden(X0,k1_relat_1(sK0)) | k1_funct_1(sK1,k1_funct_1(sK0,X0)) = X1) ) | ~spl10_49),
% 0.21/0.45    inference(avatar_component_clause,[],[f350])).
% 0.21/0.45  fof(f352,plain,(
% 0.21/0.45    spl10_49 | ~spl10_16 | ~spl10_20 | ~spl10_44),
% 0.21/0.45    inference(avatar_split_clause,[],[f315,f306,f150,f121,f350])).
% 0.21/0.45  fof(f121,plain,(
% 0.21/0.45    spl10_16 <=> ! [X0] : (r2_hidden(k1_funct_1(sK0,X0),k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 0.21/0.45  fof(f150,plain,(
% 0.21/0.45    spl10_20 <=> ! [X1,X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(k4_tarski(X0,X1),sK1) | k1_funct_1(sK1,X0) = X1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).
% 0.21/0.45  fof(f306,plain,(
% 0.21/0.45    spl10_44 <=> ! [X3,X2] : (r2_hidden(k4_tarski(k1_funct_1(sK0,X2),X3),sK1) | ~r2_hidden(k4_tarski(X2,X3),sK0) | ~r2_hidden(X2,k1_relat_1(sK0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).
% 0.21/0.45  fof(f315,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK0) | ~r2_hidden(X0,k1_relat_1(sK0)) | k1_funct_1(sK1,k1_funct_1(sK0,X0)) = X1) ) | (~spl10_16 | ~spl10_20 | ~spl10_44)),
% 0.21/0.45    inference(subsumption_resolution,[],[f313,f122])).
% 0.21/0.45  fof(f122,plain,(
% 0.21/0.45    ( ! [X0] : (r2_hidden(k1_funct_1(sK0,X0),k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK0))) ) | ~spl10_16),
% 0.21/0.45    inference(avatar_component_clause,[],[f121])).
% 0.21/0.45  fof(f313,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK0) | ~r2_hidden(X0,k1_relat_1(sK0)) | ~r2_hidden(k1_funct_1(sK0,X0),k1_relat_1(sK1)) | k1_funct_1(sK1,k1_funct_1(sK0,X0)) = X1) ) | (~spl10_20 | ~spl10_44)),
% 0.21/0.45    inference(resolution,[],[f307,f151])).
% 0.21/0.45  fof(f151,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,X0) = X1) ) | ~spl10_20),
% 0.21/0.45    inference(avatar_component_clause,[],[f150])).
% 0.21/0.45  fof(f307,plain,(
% 0.21/0.45    ( ! [X2,X3] : (r2_hidden(k4_tarski(k1_funct_1(sK0,X2),X3),sK1) | ~r2_hidden(k4_tarski(X2,X3),sK0) | ~r2_hidden(X2,k1_relat_1(sK0))) ) | ~spl10_44),
% 0.21/0.45    inference(avatar_component_clause,[],[f306])).
% 0.21/0.45  fof(f308,plain,(
% 0.21/0.45    spl10_44 | ~spl10_30 | ~spl10_42),
% 0.21/0.45    inference(avatar_split_clause,[],[f293,f285,f216,f306])).
% 0.21/0.45  fof(f216,plain,(
% 0.21/0.45    spl10_30 <=> ! [X1,X0] : (r2_hidden(k4_tarski(sK4(sK0,sK1,X0,X1),X1),sK1) | ~r2_hidden(k4_tarski(X0,X1),sK0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).
% 0.21/0.45  fof(f285,plain,(
% 0.21/0.45    spl10_42 <=> ! [X1,X0] : (~r2_hidden(k4_tarski(X0,X1),sK0) | ~r2_hidden(X0,k1_relat_1(sK0)) | k1_funct_1(sK0,X0) = sK4(sK0,sK1,X0,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).
% 0.21/0.45  fof(f293,plain,(
% 0.21/0.45    ( ! [X2,X3] : (r2_hidden(k4_tarski(k1_funct_1(sK0,X2),X3),sK1) | ~r2_hidden(k4_tarski(X2,X3),sK0) | ~r2_hidden(X2,k1_relat_1(sK0))) ) | (~spl10_30 | ~spl10_42)),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f292])).
% 0.21/0.45  fof(f292,plain,(
% 0.21/0.45    ( ! [X2,X3] : (r2_hidden(k4_tarski(k1_funct_1(sK0,X2),X3),sK1) | ~r2_hidden(k4_tarski(X2,X3),sK0) | ~r2_hidden(X2,k1_relat_1(sK0)) | ~r2_hidden(k4_tarski(X2,X3),sK0)) ) | (~spl10_30 | ~spl10_42)),
% 0.21/0.45    inference(superposition,[],[f217,f286])).
% 0.21/0.45  fof(f286,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_funct_1(sK0,X0) = sK4(sK0,sK1,X0,X1) | ~r2_hidden(X0,k1_relat_1(sK0)) | ~r2_hidden(k4_tarski(X0,X1),sK0)) ) | ~spl10_42),
% 0.21/0.45    inference(avatar_component_clause,[],[f285])).
% 0.21/0.45  fof(f217,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(sK0,sK1,X0,X1),X1),sK1) | ~r2_hidden(k4_tarski(X0,X1),sK0)) ) | ~spl10_30),
% 0.21/0.45    inference(avatar_component_clause,[],[f216])).
% 0.21/0.45  fof(f287,plain,(
% 0.21/0.45    spl10_42 | ~spl10_22 | ~spl10_33),
% 0.21/0.45    inference(avatar_split_clause,[],[f240,f231,f160,f285])).
% 0.21/0.45  fof(f160,plain,(
% 0.21/0.45    spl10_22 <=> ! [X3,X2] : (~r2_hidden(X2,k1_relat_1(sK0)) | ~r2_hidden(k4_tarski(X2,X3),sK0) | k1_funct_1(sK0,X2) = X3)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).
% 0.21/0.45  fof(f231,plain,(
% 0.21/0.45    spl10_33 <=> ! [X1,X0] : (r2_hidden(k4_tarski(X0,sK4(sK0,sK1,X0,X1)),sK0) | ~r2_hidden(k4_tarski(X0,X1),sK0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).
% 0.21/0.45  fof(f240,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK0) | ~r2_hidden(X0,k1_relat_1(sK0)) | k1_funct_1(sK0,X0) = sK4(sK0,sK1,X0,X1)) ) | (~spl10_22 | ~spl10_33)),
% 0.21/0.45    inference(resolution,[],[f232,f161])).
% 0.21/0.45  fof(f161,plain,(
% 0.21/0.45    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK0) | ~r2_hidden(X2,k1_relat_1(sK0)) | k1_funct_1(sK0,X2) = X3) ) | ~spl10_22),
% 0.21/0.45    inference(avatar_component_clause,[],[f160])).
% 0.21/0.45  fof(f232,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,sK4(sK0,sK1,X0,X1)),sK0) | ~r2_hidden(k4_tarski(X0,X1),sK0)) ) | ~spl10_33),
% 0.21/0.45    inference(avatar_component_clause,[],[f231])).
% 0.21/0.45  fof(f233,plain,(
% 0.21/0.45    spl10_33 | ~spl10_1 | ~spl10_3 | ~spl10_6 | ~spl10_27),
% 0.21/0.45    inference(avatar_split_clause,[],[f209,f187,f78,f66,f58,f231])).
% 0.21/0.45  fof(f78,plain,(
% 0.21/0.45    spl10_6 <=> sK0 = k5_relat_1(sK0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.21/0.45  fof(f187,plain,(
% 0.21/0.45    spl10_27 <=> ! [X1,X3,X0,X4] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(k5_relat_1(X0,X1)) | r2_hidden(k4_tarski(X3,sK4(X0,X1,X3,X4)),X0) | ~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).
% 0.21/0.45  fof(f209,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,sK4(sK0,sK1,X0,X1)),sK0) | ~r2_hidden(k4_tarski(X0,X1),sK0)) ) | (~spl10_1 | ~spl10_3 | ~spl10_6 | ~spl10_27)),
% 0.21/0.45    inference(subsumption_resolution,[],[f208,f59])).
% 0.21/0.45  fof(f208,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_relat_1(sK1) | r2_hidden(k4_tarski(X0,sK4(sK0,sK1,X0,X1)),sK0) | ~r2_hidden(k4_tarski(X0,X1),sK0)) ) | (~spl10_3 | ~spl10_6 | ~spl10_27)),
% 0.21/0.45    inference(subsumption_resolution,[],[f207,f67])).
% 0.21/0.45  fof(f207,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_relat_1(sK0) | ~v1_relat_1(sK1) | r2_hidden(k4_tarski(X0,sK4(sK0,sK1,X0,X1)),sK0) | ~r2_hidden(k4_tarski(X0,X1),sK0)) ) | (~spl10_6 | ~spl10_27)),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f206])).
% 0.21/0.45  fof(f206,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_relat_1(sK0) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | r2_hidden(k4_tarski(X0,sK4(sK0,sK1,X0,X1)),sK0) | ~r2_hidden(k4_tarski(X0,X1),sK0)) ) | (~spl10_6 | ~spl10_27)),
% 0.21/0.45    inference(superposition,[],[f188,f79])).
% 0.21/0.45  fof(f79,plain,(
% 0.21/0.45    sK0 = k5_relat_1(sK0,sK1) | ~spl10_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f78])).
% 0.21/0.45  fof(f188,plain,(
% 0.21/0.45    ( ! [X4,X0,X3,X1] : (~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(X3,sK4(X0,X1,X3,X4)),X0) | ~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))) ) | ~spl10_27),
% 0.21/0.45    inference(avatar_component_clause,[],[f187])).
% 0.21/0.45  fof(f218,plain,(
% 0.21/0.45    spl10_30 | ~spl10_1 | ~spl10_3 | ~spl10_6 | ~spl10_25),
% 0.21/0.45    inference(avatar_split_clause,[],[f205,f179,f78,f66,f58,f216])).
% 0.21/0.45  fof(f179,plain,(
% 0.21/0.45    spl10_25 <=> ! [X1,X3,X0,X4] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(k5_relat_1(X0,X1)) | r2_hidden(k4_tarski(sK4(X0,X1,X3,X4),X4),X1) | ~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).
% 0.21/0.45  fof(f205,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(sK0,sK1,X0,X1),X1),sK1) | ~r2_hidden(k4_tarski(X0,X1),sK0)) ) | (~spl10_1 | ~spl10_3 | ~spl10_6 | ~spl10_25)),
% 0.21/0.45    inference(subsumption_resolution,[],[f204,f59])).
% 0.21/0.45  fof(f204,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_relat_1(sK1) | r2_hidden(k4_tarski(sK4(sK0,sK1,X0,X1),X1),sK1) | ~r2_hidden(k4_tarski(X0,X1),sK0)) ) | (~spl10_3 | ~spl10_6 | ~spl10_25)),
% 0.21/0.45    inference(subsumption_resolution,[],[f203,f67])).
% 0.21/0.45  fof(f203,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_relat_1(sK0) | ~v1_relat_1(sK1) | r2_hidden(k4_tarski(sK4(sK0,sK1,X0,X1),X1),sK1) | ~r2_hidden(k4_tarski(X0,X1),sK0)) ) | (~spl10_6 | ~spl10_25)),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f202])).
% 0.21/0.45  fof(f202,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_relat_1(sK0) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | r2_hidden(k4_tarski(sK4(sK0,sK1,X0,X1),X1),sK1) | ~r2_hidden(k4_tarski(X0,X1),sK0)) ) | (~spl10_6 | ~spl10_25)),
% 0.21/0.45    inference(superposition,[],[f180,f79])).
% 0.21/0.45  fof(f180,plain,(
% 0.21/0.45    ( ! [X4,X0,X3,X1] : (~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(sK4(X0,X1,X3,X4),X4),X1) | ~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))) ) | ~spl10_25),
% 0.21/0.45    inference(avatar_component_clause,[],[f179])).
% 0.21/0.45  fof(f189,plain,(
% 0.21/0.45    spl10_27),
% 0.21/0.45    inference(avatar_split_clause,[],[f45,f187])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(k5_relat_1(X0,X1)) | r2_hidden(k4_tarski(X3,sK4(X0,X1,X3,X4)),X0) | ~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))) )),
% 0.21/0.45    inference(equality_resolution,[],[f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(X3,sK4(X0,X1,X3,X4)),X0) | ~r2_hidden(k4_tarski(X3,X4),X2) | k5_relat_1(X0,X1) != X2) )),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).
% 0.21/0.45  fof(f181,plain,(
% 0.21/0.45    spl10_25),
% 0.21/0.45    inference(avatar_split_clause,[],[f44,f179])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(k5_relat_1(X0,X1)) | r2_hidden(k4_tarski(sK4(X0,X1,X3,X4),X4),X1) | ~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))) )),
% 0.21/0.45    inference(equality_resolution,[],[f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(sK4(X0,X1,X3,X4),X4),X1) | ~r2_hidden(k4_tarski(X3,X4),X2) | k5_relat_1(X0,X1) != X2) )),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f162,plain,(
% 0.21/0.45    spl10_22 | ~spl10_3 | ~spl10_4 | ~spl10_17),
% 0.21/0.45    inference(avatar_split_clause,[],[f148,f134,f70,f66,f160])).
% 0.21/0.45  fof(f134,plain,(
% 0.21/0.45    spl10_17 <=> ! [X1,X0,X2] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) = X2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 0.21/0.45  fof(f148,plain,(
% 0.21/0.45    ( ! [X2,X3] : (~r2_hidden(X2,k1_relat_1(sK0)) | ~r2_hidden(k4_tarski(X2,X3),sK0) | k1_funct_1(sK0,X2) = X3) ) | (~spl10_3 | ~spl10_4 | ~spl10_17)),
% 0.21/0.45    inference(subsumption_resolution,[],[f146,f67])).
% 0.21/0.45  fof(f146,plain,(
% 0.21/0.45    ( ! [X2,X3] : (~v1_relat_1(sK0) | ~r2_hidden(X2,k1_relat_1(sK0)) | ~r2_hidden(k4_tarski(X2,X3),sK0) | k1_funct_1(sK0,X2) = X3) ) | (~spl10_4 | ~spl10_17)),
% 0.21/0.45    inference(resolution,[],[f135,f71])).
% 0.21/0.45  fof(f135,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) = X2) ) | ~spl10_17),
% 0.21/0.45    inference(avatar_component_clause,[],[f134])).
% 0.21/0.45  fof(f156,plain,(
% 0.21/0.45    spl10_21),
% 0.21/0.45    inference(avatar_split_clause,[],[f55,f154])).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    ( ! [X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | sK9(k1_relat_1(X1),X1) != k1_funct_1(X1,sK9(k1_relat_1(X1),X1)) | k6_relat_1(k1_relat_1(X1)) = X1) )),
% 0.21/0.45    inference(equality_resolution,[],[f40])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | sK9(X0,X1) != k1_funct_1(X1,sK9(X0,X1)) | k6_relat_1(X0) = X1) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(flattening,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).
% 0.21/0.45  fof(f152,plain,(
% 0.21/0.45    spl10_20 | ~spl10_1 | ~spl10_2 | ~spl10_17),
% 0.21/0.45    inference(avatar_split_clause,[],[f147,f134,f62,f58,f150])).
% 0.21/0.45  fof(f147,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(k4_tarski(X0,X1),sK1) | k1_funct_1(sK1,X0) = X1) ) | (~spl10_1 | ~spl10_2 | ~spl10_17)),
% 0.21/0.45    inference(subsumption_resolution,[],[f145,f59])).
% 0.21/0.45  fof(f145,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_relat_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(k4_tarski(X0,X1),sK1) | k1_funct_1(sK1,X0) = X1) ) | (~spl10_2 | ~spl10_17)),
% 0.21/0.45    inference(resolution,[],[f135,f63])).
% 0.21/0.45  fof(f136,plain,(
% 0.21/0.45    spl10_17),
% 0.21/0.45    inference(avatar_split_clause,[],[f37,f134])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) = X2) )),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(flattening,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).
% 0.21/0.45  fof(f123,plain,(
% 0.21/0.45    spl10_16 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_10),
% 0.21/0.45    inference(avatar_split_clause,[],[f115,f94,f74,f70,f66,f121])).
% 0.21/0.45  fof(f94,plain,(
% 0.21/0.45    spl10_10 <=> ! [X3,X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.21/0.45  fof(f115,plain,(
% 0.21/0.45    ( ! [X0] : (r2_hidden(k1_funct_1(sK0,X0),k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK0))) ) | (~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_10)),
% 0.21/0.45    inference(subsumption_resolution,[],[f114,f67])).
% 0.21/0.45  fof(f114,plain,(
% 0.21/0.45    ( ! [X0] : (r2_hidden(k1_funct_1(sK0,X0),k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK0)) | ~v1_relat_1(sK0)) ) | (~spl10_4 | ~spl10_5 | ~spl10_10)),
% 0.21/0.45    inference(subsumption_resolution,[],[f113,f71])).
% 0.21/0.45  fof(f113,plain,(
% 0.21/0.45    ( ! [X0] : (r2_hidden(k1_funct_1(sK0,X0),k1_relat_1(sK1)) | ~v1_funct_1(sK0) | ~r2_hidden(X0,k1_relat_1(sK0)) | ~v1_relat_1(sK0)) ) | (~spl10_5 | ~spl10_10)),
% 0.21/0.45    inference(superposition,[],[f95,f75])).
% 0.21/0.45  fof(f95,plain,(
% 0.21/0.45    ( ! [X0,X3] : (r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl10_10),
% 0.21/0.45    inference(avatar_component_clause,[],[f94])).
% 0.21/0.45  fof(f119,plain,(
% 0.21/0.45    spl10_15),
% 0.21/0.45    inference(avatar_split_clause,[],[f56,f117])).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    ( ! [X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | r2_hidden(sK9(k1_relat_1(X1),X1),k1_relat_1(X1)) | k6_relat_1(k1_relat_1(X1)) = X1) )),
% 0.21/0.45    inference(equality_resolution,[],[f39])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | r2_hidden(sK9(X0,X1),X0) | k6_relat_1(X0) = X1) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f108,plain,(
% 0.21/0.45    spl10_13),
% 0.21/0.45    inference(avatar_split_clause,[],[f50,f106])).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)) )),
% 0.21/0.45    inference(equality_resolution,[],[f38])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2) )),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f104,plain,(
% 0.21/0.45    spl10_12),
% 0.21/0.45    inference(avatar_split_clause,[],[f48,f102])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    ( ! [X2,X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK7(X0,X2)) = X2 | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.21/0.45    inference(equality_resolution,[],[f33])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK7(X0,X2)) = X2 | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.45    inference(cnf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(flattening,[],[f10])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.21/0.45  fof(f100,plain,(
% 0.21/0.45    spl10_11),
% 0.21/0.45    inference(avatar_split_clause,[],[f49,f98])).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    ( ! [X2,X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK7(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.21/0.45    inference(equality_resolution,[],[f32])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK7(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.45    inference(cnf_transformation,[],[f11])).
% 0.21/0.45  fof(f96,plain,(
% 0.21/0.45    spl10_10),
% 0.21/0.45    inference(avatar_split_clause,[],[f47,f94])).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    ( ! [X0,X3] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0))) )),
% 0.21/0.45    inference(equality_resolution,[],[f46])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X3),X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.45    inference(equality_resolution,[],[f34])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.45    inference(cnf_transformation,[],[f11])).
% 0.21/0.45  fof(f84,plain,(
% 0.21/0.45    ~spl10_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f20,f82])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    sK1 != k6_relat_1(k1_relat_1(sK1))),
% 0.21/0.45    inference(cnf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.45    inference(flattening,[],[f7])).
% 0.21/0.45  fof(f7,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : ((k6_relat_1(k1_relat_1(X1)) != X1 & (k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,negated_conjecture,(
% 0.21/0.45    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 0.21/0.45    inference(negated_conjecture,[],[f5])).
% 0.21/0.45  fof(f5,conjecture,(
% 0.21/0.45    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    spl10_6),
% 0.21/0.45    inference(avatar_split_clause,[],[f19,f78])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    sK0 = k5_relat_1(sK0,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f8])).
% 0.21/0.45  fof(f76,plain,(
% 0.21/0.45    spl10_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f18,f74])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    k2_relat_1(sK0) = k1_relat_1(sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f8])).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    spl10_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f22,f70])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    v1_funct_1(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f8])).
% 0.21/0.45  fof(f68,plain,(
% 0.21/0.45    spl10_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f21,f66])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    v1_relat_1(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f8])).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    spl10_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f17,f62])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    v1_funct_1(sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f8])).
% 0.21/0.45  fof(f60,plain,(
% 0.21/0.45    spl10_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f16,f58])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    v1_relat_1(sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f8])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (5743)------------------------------
% 0.21/0.45  % (5743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (5743)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (5743)Memory used [KB]: 11129
% 0.21/0.45  % (5743)Time elapsed: 0.031 s
% 0.21/0.45  % (5743)------------------------------
% 0.21/0.45  % (5743)------------------------------
% 0.21/0.46  % (5733)Success in time 0.097 s
%------------------------------------------------------------------------------
