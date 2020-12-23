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
% DateTime   : Thu Dec  3 12:52:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 188 expanded)
%              Number of leaves         :   23 (  71 expanded)
%              Depth                    :   13
%              Number of atoms          :  403 ( 626 expanded)
%              Number of equality atoms :   64 ( 102 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f243,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f59,f64,f86,f96,f101,f107,f121,f130,f162,f170,f183,f236,f237,f242])).

fof(f242,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(avatar_contradiction_clause,[],[f241])).

fof(f241,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f240,f94])).

fof(f94,plain,
    ( sK0 = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl5_6
  <=> sK0 = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f240,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | spl5_5
    | ~ spl5_8
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f239,f85])).

fof(f85,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl5_4
  <=> r2_hidden(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f239,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))
    | ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl5_1
    | ~ spl5_2
    | spl5_5
    | ~ spl5_8
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f238,f58])).

fof(f58,plain,
    ( v1_funct_1(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl5_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f238,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))
    | ~ v1_funct_1(sK1)
    | ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl5_1
    | spl5_5
    | ~ spl5_8
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f184,f53])).

fof(f53,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl5_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f184,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ r2_hidden(sK0,k2_relat_1(sK1))
    | spl5_5
    | ~ spl5_8
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(superposition,[],[f91,f178])).

fof(f178,plain,
    ( ! [X2,X1] :
        ( k1_funct_1(k5_relat_1(k2_funct_1(sK1),X2),X1) = k1_funct_1(X2,k1_funct_1(k2_funct_1(sK1),X1))
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ r2_hidden(X1,k2_relat_1(sK1)) )
    | ~ spl5_8
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f177,f149])).

fof(f149,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl5_13
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f177,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK1))
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(k2_funct_1(sK1))
        | k1_funct_1(k5_relat_1(k2_funct_1(sK1),X2),X1) = k1_funct_1(X2,k1_funct_1(k2_funct_1(sK1),X1)) )
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f109,f153])).

fof(f153,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl5_14
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f109,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK1))
        | ~ v1_funct_1(k2_funct_1(sK1))
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(k2_funct_1(sK1))
        | k1_funct_1(k5_relat_1(k2_funct_1(sK1),X2),X1) = k1_funct_1(X2,k1_funct_1(k2_funct_1(sK1),X1)) )
    | ~ spl5_8 ),
    inference(superposition,[],[f35,f106])).

fof(f106,plain,
    ( k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl5_8
  <=> k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X1)
      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(f91,plain,
    ( sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl5_5
  <=> sK0 = k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f237,plain,
    ( k1_funct_1(k2_funct_1(sK1),sK0) != sK4(sK1,sK0)
    | sK0 != k1_funct_1(sK1,sK4(sK1,sK0))
    | sK0 = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f236,plain,
    ( spl5_20
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_11
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f229,f180,f127,f61,f56,f51,f233])).

fof(f233,plain,
    ( spl5_20
  <=> k1_funct_1(k2_funct_1(sK1),sK0) = sK4(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f61,plain,
    ( spl5_3
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f127,plain,
    ( spl5_11
  <=> r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f180,plain,
    ( spl5_16
  <=> sK0 = k1_funct_1(sK1,sK4(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f229,plain,
    ( k1_funct_1(k2_funct_1(sK1),sK0) = sK4(sK1,sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_11
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f132,f182])).

fof(f182,plain,
    ( sK0 = k1_funct_1(sK1,sK4(sK1,sK0))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f180])).

fof(f132,plain,
    ( sK4(sK1,sK0) = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK4(sK1,sK0)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_11 ),
    inference(resolution,[],[f129,f75])).

fof(f75,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f74,f53])).

fof(f74,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 )
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f70,f58])).

fof(f70,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 )
    | ~ spl5_3 ),
    inference(resolution,[],[f63,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

fof(f63,plain,
    ( v2_funct_1(sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f129,plain,
    ( r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f127])).

fof(f183,plain,
    ( spl5_16
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f122,f118,f56,f51,f180])).

fof(f118,plain,
    ( spl5_10
  <=> r2_hidden(k4_tarski(sK4(sK1,sK0),sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f122,plain,
    ( sK0 = k1_funct_1(sK1,sK4(sK1,sK0))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_10 ),
    inference(resolution,[],[f120,f69])).

fof(f69,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK1)
        | k1_funct_1(sK1,X2) = X3 )
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f68,f53])).

fof(f68,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(sK1)
        | k1_funct_1(sK1,X2) = X3
        | ~ r2_hidden(k4_tarski(X2,X3),sK1) )
    | ~ spl5_2 ),
    inference(resolution,[],[f58,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f120,plain,
    ( r2_hidden(k4_tarski(sK4(sK1,sK0),sK0),sK1)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f118])).

fof(f170,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | spl5_14 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | spl5_14 ),
    inference(subsumption_resolution,[],[f168,f53])).

fof(f168,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl5_2
    | spl5_14 ),
    inference(subsumption_resolution,[],[f167,f58])).

fof(f167,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl5_14 ),
    inference(resolution,[],[f154,f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f154,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f152])).

fof(f162,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | spl5_13 ),
    inference(subsumption_resolution,[],[f160,f53])).

fof(f160,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl5_2
    | spl5_13 ),
    inference(subsumption_resolution,[],[f159,f58])).

fof(f159,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl5_13 ),
    inference(resolution,[],[f150,f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f150,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f148])).

fof(f130,plain,
    ( spl5_11
    | ~ spl5_1
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f124,f118,f51,f127])).

fof(f124,plain,
    ( r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1))
    | ~ spl5_1
    | ~ spl5_10 ),
    inference(resolution,[],[f120,f65])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f53,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(f121,plain,
    ( spl5_10
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f102,f98,f118])).

fof(f98,plain,
    ( spl5_7
  <=> sP3(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f102,plain,
    ( r2_hidden(k4_tarski(sK4(sK1,sK0),sK0),sK1)
    | ~ spl5_7 ),
    inference(resolution,[],[f100,f36])).

fof(f36,plain,(
    ! [X2,X0] :
      ( ~ sP3(X2,X0)
      | r2_hidden(k4_tarski(sK4(X0,X2),X2),X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f100,plain,
    ( sP3(sK0,sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f98])).

fof(f107,plain,
    ( spl5_8
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f79,f61,f56,f51,f104])).

fof(f79,plain,
    ( k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f78,f53])).

fof(f78,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f72,f58])).

fof(f72,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))
    | ~ spl5_3 ),
    inference(resolution,[],[f63,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f101,plain,
    ( spl5_7
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f87,f83,f98])).

fof(f87,plain,
    ( sP3(sK0,sK1)
    | ~ spl5_4 ),
    inference(resolution,[],[f85,f47])).

fof(f47,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | sP3(X2,X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f96,plain,
    ( ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f24,f93,f89])).

fof(f24,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))
    | sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k2_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
            & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).

fof(f86,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f28,f83])).

fof(f28,plain,(
    r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f64,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f27,f61])).

fof(f27,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f59,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f26,f56])).

fof(f26,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f54,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f25,f51])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:41:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (2574)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.45  % (2561)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.45  % (2561)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.46  % (2558)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (2566)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f243,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f54,f59,f64,f86,f96,f101,f107,f121,f130,f162,f170,f183,f236,f237,f242])).
% 0.21/0.46  fof(f242,plain,(
% 0.21/0.46    ~spl5_1 | ~spl5_2 | ~spl5_4 | spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_13 | ~spl5_14),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f241])).
% 0.21/0.46  fof(f241,plain,(
% 0.21/0.46    $false | (~spl5_1 | ~spl5_2 | ~spl5_4 | spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_13 | ~spl5_14)),
% 0.21/0.46    inference(subsumption_resolution,[],[f240,f94])).
% 0.21/0.46  fof(f94,plain,(
% 0.21/0.46    sK0 = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) | ~spl5_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f93])).
% 0.21/0.46  fof(f93,plain,(
% 0.21/0.46    spl5_6 <=> sK0 = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.46  fof(f240,plain,(
% 0.21/0.46    sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) | (~spl5_1 | ~spl5_2 | ~spl5_4 | spl5_5 | ~spl5_8 | ~spl5_13 | ~spl5_14)),
% 0.21/0.46    inference(subsumption_resolution,[],[f239,f85])).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    r2_hidden(sK0,k2_relat_1(sK1)) | ~spl5_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f83])).
% 0.21/0.46  fof(f83,plain,(
% 0.21/0.46    spl5_4 <=> r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.46  fof(f239,plain,(
% 0.21/0.46    sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1)) | (~spl5_1 | ~spl5_2 | spl5_5 | ~spl5_8 | ~spl5_13 | ~spl5_14)),
% 0.21/0.46    inference(subsumption_resolution,[],[f238,f58])).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    v1_funct_1(sK1) | ~spl5_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f56])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    spl5_2 <=> v1_funct_1(sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.46  fof(f238,plain,(
% 0.21/0.46    sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) | ~v1_funct_1(sK1) | ~r2_hidden(sK0,k2_relat_1(sK1)) | (~spl5_1 | spl5_5 | ~spl5_8 | ~spl5_13 | ~spl5_14)),
% 0.21/0.46    inference(subsumption_resolution,[],[f184,f53])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    v1_relat_1(sK1) | ~spl5_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f51])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    spl5_1 <=> v1_relat_1(sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.46  fof(f184,plain,(
% 0.21/0.46    sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~r2_hidden(sK0,k2_relat_1(sK1)) | (spl5_5 | ~spl5_8 | ~spl5_13 | ~spl5_14)),
% 0.21/0.46    inference(superposition,[],[f91,f178])).
% 0.21/0.46  fof(f178,plain,(
% 0.21/0.46    ( ! [X2,X1] : (k1_funct_1(k5_relat_1(k2_funct_1(sK1),X2),X1) = k1_funct_1(X2,k1_funct_1(k2_funct_1(sK1),X1)) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X1,k2_relat_1(sK1))) ) | (~spl5_8 | ~spl5_13 | ~spl5_14)),
% 0.21/0.46    inference(subsumption_resolution,[],[f177,f149])).
% 0.21/0.46  fof(f149,plain,(
% 0.21/0.46    v1_relat_1(k2_funct_1(sK1)) | ~spl5_13),
% 0.21/0.46    inference(avatar_component_clause,[],[f148])).
% 0.21/0.46  fof(f148,plain,(
% 0.21/0.46    spl5_13 <=> v1_relat_1(k2_funct_1(sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.46  fof(f177,plain,(
% 0.21/0.46    ( ! [X2,X1] : (~r2_hidden(X1,k2_relat_1(sK1)) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(k2_funct_1(sK1)) | k1_funct_1(k5_relat_1(k2_funct_1(sK1),X2),X1) = k1_funct_1(X2,k1_funct_1(k2_funct_1(sK1),X1))) ) | (~spl5_8 | ~spl5_14)),
% 0.21/0.46    inference(subsumption_resolution,[],[f109,f153])).
% 0.21/0.46  fof(f153,plain,(
% 0.21/0.46    v1_funct_1(k2_funct_1(sK1)) | ~spl5_14),
% 0.21/0.46    inference(avatar_component_clause,[],[f152])).
% 0.21/0.46  fof(f152,plain,(
% 0.21/0.46    spl5_14 <=> v1_funct_1(k2_funct_1(sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.46  fof(f109,plain,(
% 0.21/0.46    ( ! [X2,X1] : (~r2_hidden(X1,k2_relat_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(k2_funct_1(sK1)) | k1_funct_1(k5_relat_1(k2_funct_1(sK1),X2),X1) = k1_funct_1(X2,k1_funct_1(k2_funct_1(sK1),X1))) ) | ~spl5_8),
% 0.21/0.46    inference(superposition,[],[f35,f106])).
% 0.21/0.46  fof(f106,plain,(
% 0.21/0.46    k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) | ~spl5_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f104])).
% 0.21/0.46  fof(f104,plain,(
% 0.21/0.46    spl5_8 <=> k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X1) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(flattening,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).
% 0.21/0.46  fof(f91,plain,(
% 0.21/0.46    sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) | spl5_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f89])).
% 0.21/0.46  fof(f89,plain,(
% 0.21/0.46    spl5_5 <=> sK0 = k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.46  fof(f237,plain,(
% 0.21/0.46    k1_funct_1(k2_funct_1(sK1),sK0) != sK4(sK1,sK0) | sK0 != k1_funct_1(sK1,sK4(sK1,sK0)) | sK0 = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))),
% 0.21/0.46    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.46  fof(f236,plain,(
% 0.21/0.46    spl5_20 | ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_11 | ~spl5_16),
% 0.21/0.46    inference(avatar_split_clause,[],[f229,f180,f127,f61,f56,f51,f233])).
% 0.21/0.46  fof(f233,plain,(
% 0.21/0.46    spl5_20 <=> k1_funct_1(k2_funct_1(sK1),sK0) = sK4(sK1,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    spl5_3 <=> v2_funct_1(sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.46  fof(f127,plain,(
% 0.21/0.46    spl5_11 <=> r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.46  fof(f180,plain,(
% 0.21/0.46    spl5_16 <=> sK0 = k1_funct_1(sK1,sK4(sK1,sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.46  fof(f229,plain,(
% 0.21/0.46    k1_funct_1(k2_funct_1(sK1),sK0) = sK4(sK1,sK0) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_11 | ~spl5_16)),
% 0.21/0.46    inference(forward_demodulation,[],[f132,f182])).
% 0.21/0.46  fof(f182,plain,(
% 0.21/0.46    sK0 = k1_funct_1(sK1,sK4(sK1,sK0)) | ~spl5_16),
% 0.21/0.46    inference(avatar_component_clause,[],[f180])).
% 0.21/0.46  fof(f132,plain,(
% 0.21/0.46    sK4(sK1,sK0) = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK4(sK1,sK0))) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_11)),
% 0.21/0.46    inference(resolution,[],[f129,f75])).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) ) | (~spl5_1 | ~spl5_2 | ~spl5_3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f74,f53])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_relat_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) ) | (~spl5_2 | ~spl5_3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f70,f58])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) ) | ~spl5_3),
% 0.21/0.46    inference(resolution,[],[f63,f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(flattening,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    v2_funct_1(sK1) | ~spl5_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f61])).
% 0.21/0.46  fof(f129,plain,(
% 0.21/0.46    r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1)) | ~spl5_11),
% 0.21/0.46    inference(avatar_component_clause,[],[f127])).
% 0.21/0.46  fof(f183,plain,(
% 0.21/0.46    spl5_16 | ~spl5_1 | ~spl5_2 | ~spl5_10),
% 0.21/0.46    inference(avatar_split_clause,[],[f122,f118,f56,f51,f180])).
% 0.21/0.46  fof(f118,plain,(
% 0.21/0.46    spl5_10 <=> r2_hidden(k4_tarski(sK4(sK1,sK0),sK0),sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.46  fof(f122,plain,(
% 0.21/0.46    sK0 = k1_funct_1(sK1,sK4(sK1,sK0)) | (~spl5_1 | ~spl5_2 | ~spl5_10)),
% 0.21/0.46    inference(resolution,[],[f120,f69])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK1) | k1_funct_1(sK1,X2) = X3) ) | (~spl5_1 | ~spl5_2)),
% 0.21/0.46    inference(subsumption_resolution,[],[f68,f53])).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    ( ! [X2,X3] : (~v1_relat_1(sK1) | k1_funct_1(sK1,X2) = X3 | ~r2_hidden(k4_tarski(X2,X3),sK1)) ) | ~spl5_2),
% 0.21/0.46    inference(resolution,[],[f58,f45])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.46    inference(flattening,[],[f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.46  fof(f120,plain,(
% 0.21/0.46    r2_hidden(k4_tarski(sK4(sK1,sK0),sK0),sK1) | ~spl5_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f118])).
% 0.21/0.46  fof(f170,plain,(
% 0.21/0.46    ~spl5_1 | ~spl5_2 | spl5_14),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f169])).
% 0.21/0.46  fof(f169,plain,(
% 0.21/0.46    $false | (~spl5_1 | ~spl5_2 | spl5_14)),
% 0.21/0.46    inference(subsumption_resolution,[],[f168,f53])).
% 0.21/0.46  fof(f168,plain,(
% 0.21/0.46    ~v1_relat_1(sK1) | (~spl5_2 | spl5_14)),
% 0.21/0.46    inference(subsumption_resolution,[],[f167,f58])).
% 0.21/0.46  fof(f167,plain,(
% 0.21/0.46    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl5_14),
% 0.21/0.46    inference(resolution,[],[f154,f30])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(flattening,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.46  fof(f154,plain,(
% 0.21/0.46    ~v1_funct_1(k2_funct_1(sK1)) | spl5_14),
% 0.21/0.46    inference(avatar_component_clause,[],[f152])).
% 0.21/0.46  fof(f162,plain,(
% 0.21/0.46    ~spl5_1 | ~spl5_2 | spl5_13),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f161])).
% 0.21/0.46  fof(f161,plain,(
% 0.21/0.46    $false | (~spl5_1 | ~spl5_2 | spl5_13)),
% 0.21/0.46    inference(subsumption_resolution,[],[f160,f53])).
% 0.21/0.46  fof(f160,plain,(
% 0.21/0.46    ~v1_relat_1(sK1) | (~spl5_2 | spl5_13)),
% 0.21/0.46    inference(subsumption_resolution,[],[f159,f58])).
% 0.21/0.46  fof(f159,plain,(
% 0.21/0.46    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl5_13),
% 0.21/0.46    inference(resolution,[],[f150,f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f150,plain,(
% 0.21/0.46    ~v1_relat_1(k2_funct_1(sK1)) | spl5_13),
% 0.21/0.46    inference(avatar_component_clause,[],[f148])).
% 0.21/0.46  fof(f130,plain,(
% 0.21/0.46    spl5_11 | ~spl5_1 | ~spl5_10),
% 0.21/0.46    inference(avatar_split_clause,[],[f124,f118,f51,f127])).
% 0.21/0.46  fof(f124,plain,(
% 0.21/0.46    r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1)) | (~spl5_1 | ~spl5_10)),
% 0.21/0.46    inference(resolution,[],[f120,f65])).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | r2_hidden(X0,k1_relat_1(sK1))) ) | ~spl5_1),
% 0.21/0.46    inference(resolution,[],[f53,f42])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.21/0.46    inference(flattening,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).
% 0.21/0.46  fof(f121,plain,(
% 0.21/0.46    spl5_10 | ~spl5_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f102,f98,f118])).
% 0.21/0.46  fof(f98,plain,(
% 0.21/0.46    spl5_7 <=> sP3(sK0,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.46  fof(f102,plain,(
% 0.21/0.46    r2_hidden(k4_tarski(sK4(sK1,sK0),sK0),sK1) | ~spl5_7),
% 0.21/0.46    inference(resolution,[],[f100,f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ( ! [X2,X0] : (~sP3(X2,X0) | r2_hidden(k4_tarski(sK4(X0,X2),X2),X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.21/0.46  fof(f100,plain,(
% 0.21/0.46    sP3(sK0,sK1) | ~spl5_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f98])).
% 0.21/0.46  fof(f107,plain,(
% 0.21/0.46    spl5_8 | ~spl5_1 | ~spl5_2 | ~spl5_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f79,f61,f56,f51,f104])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) | (~spl5_1 | ~spl5_2 | ~spl5_3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f78,f53])).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    ~v1_relat_1(sK1) | k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) | (~spl5_2 | ~spl5_3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f72,f58])).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) | ~spl5_3),
% 0.21/0.46    inference(resolution,[],[f63,f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(flattening,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    spl5_7 | ~spl5_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f87,f83,f98])).
% 0.21/0.46  fof(f87,plain,(
% 0.21/0.46    sP3(sK0,sK1) | ~spl5_4),
% 0.21/0.46    inference(resolution,[],[f85,f47])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | sP3(X2,X0)) )),
% 0.21/0.46    inference(equality_resolution,[],[f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (sP3(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    ~spl5_5 | ~spl5_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f24,f93,f89])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) | sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.46    inference(flattening,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ? [X0,X1] : (((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & (r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 0.21/0.46    inference(negated_conjecture,[],[f8])).
% 0.21/0.46  fof(f8,conjecture,(
% 0.21/0.46    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    spl5_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f28,f83])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    spl5_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f27,f61])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    v2_funct_1(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    spl5_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f26,f56])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    v1_funct_1(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    spl5_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f25,f51])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    v1_relat_1(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (2561)------------------------------
% 0.21/0.46  % (2561)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (2561)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (2561)Memory used [KB]: 10746
% 0.21/0.46  % (2561)Time elapsed: 0.067 s
% 0.21/0.46  % (2561)------------------------------
% 0.21/0.46  % (2561)------------------------------
% 0.21/0.46  % (2556)Success in time 0.109 s
%------------------------------------------------------------------------------
