%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 245 expanded)
%              Number of leaves         :   24 (  97 expanded)
%              Depth                    :   15
%              Number of atoms          :  465 ( 796 expanded)
%              Number of equality atoms :   65 ( 139 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f257,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f64,f69,f82,f91,f99,f113,f122,f137,f141,f195,f211,f221,f226,f248,f256])).

fof(f256,plain,
    ( ~ spl7_1
    | ~ spl7_12
    | ~ spl7_15
    | spl7_16 ),
    inference(avatar_contradiction_clause,[],[f255])).

fof(f255,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_12
    | ~ spl7_15
    | spl7_16 ),
    inference(subsumption_resolution,[],[f254,f219])).

fof(f219,plain,
    ( sP5(sK0,sK1)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl7_15
  <=> sP5(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f254,plain,
    ( ~ sP5(sK0,sK1)
    | ~ spl7_1
    | ~ spl7_12
    | spl7_16 ),
    inference(resolution,[],[f251,f39])).

fof(f39,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK6(X0,X2),X2),X0)
      | ~ sP5(X2,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f251,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK0),sK1)
    | ~ spl7_1
    | ~ spl7_12
    | spl7_16 ),
    inference(resolution,[],[f250,f144])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X1,X0),k4_relat_1(sK1))
        | ~ r2_hidden(k4_tarski(X0,X1),sK1) )
    | ~ spl7_1
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f142,f58])).

fof(f58,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl7_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f142,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK1)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | r2_hidden(k4_tarski(X1,X0),k4_relat_1(sK1)) )
    | ~ spl7_12 ),
    inference(resolution,[],[f135,f51])).

fof(f51,plain,(
    ! [X2,X0,X3] :
      ( ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(k4_tarski(X2,X3),k4_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(k4_tarski(X2,X3),X1)
      | k4_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).

fof(f135,plain,
    ( v1_relat_1(k4_relat_1(sK1))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl7_12
  <=> v1_relat_1(k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f250,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK0,X0),k4_relat_1(sK1))
    | ~ spl7_12
    | spl7_16 ),
    inference(subsumption_resolution,[],[f249,f135])).

fof(f249,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK0,X0),k4_relat_1(sK1))
        | ~ v1_relat_1(k4_relat_1(sK1)) )
    | spl7_16 ),
    inference(resolution,[],[f247,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(f247,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))
    | spl7_16 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl7_16
  <=> r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f248,plain,
    ( ~ spl7_14
    | ~ spl7_16
    | ~ spl7_1
    | ~ spl7_2
    | spl7_5
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f233,f192,f134,f110,f96,f84,f61,f56,f245,f208])).

fof(f208,plain,
    ( spl7_14
  <=> sK0 = k1_funct_1(sK1,sK6(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f61,plain,
    ( spl7_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f84,plain,
    ( spl7_5
  <=> sK0 = k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f96,plain,
    ( spl7_7
  <=> k2_funct_1(sK1) = k4_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f110,plain,
    ( spl7_8
  <=> v1_funct_1(k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f192,plain,
    ( spl7_13
  <=> k1_funct_1(k4_relat_1(sK1),sK0) = sK6(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f233,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))
    | sK0 != k1_funct_1(sK1,sK6(sK1,sK0))
    | ~ spl7_1
    | ~ spl7_2
    | spl7_5
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f232,f135])).

fof(f232,plain,
    ( ~ v1_relat_1(k4_relat_1(sK1))
    | ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))
    | sK0 != k1_funct_1(sK1,sK6(sK1,sK0))
    | ~ spl7_1
    | ~ spl7_2
    | spl7_5
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_13 ),
    inference(forward_demodulation,[],[f231,f98])).

fof(f98,plain,
    ( k2_funct_1(sK1) = k4_relat_1(sK1)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f231,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))
    | sK0 != k1_funct_1(sK1,sK6(sK1,sK0))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl7_1
    | ~ spl7_2
    | spl7_5
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_13 ),
    inference(forward_demodulation,[],[f230,f98])).

fof(f230,plain,
    ( sK0 != k1_funct_1(sK1,sK6(sK1,sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl7_1
    | ~ spl7_2
    | spl7_5
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f229,f112])).

fof(f112,plain,
    ( v1_funct_1(k4_relat_1(sK1))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f110])).

fof(f229,plain,
    ( ~ v1_funct_1(k4_relat_1(sK1))
    | sK0 != k1_funct_1(sK1,sK6(sK1,sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl7_1
    | ~ spl7_2
    | spl7_5
    | ~ spl7_7
    | ~ spl7_13 ),
    inference(forward_demodulation,[],[f228,f98])).

fof(f228,plain,
    ( sK0 != k1_funct_1(sK1,sK6(sK1,sK0))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ r2_hidden(sK0,k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl7_1
    | ~ spl7_2
    | spl7_5
    | ~ spl7_7
    | ~ spl7_13 ),
    inference(forward_demodulation,[],[f227,f194])).

fof(f194,plain,
    ( k1_funct_1(k4_relat_1(sK1),sK0) = sK6(sK1,sK0)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f192])).

fof(f227,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ r2_hidden(sK0,k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl7_1
    | ~ spl7_2
    | spl7_5
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f94,f98])).

fof(f94,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ r2_hidden(sK0,k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl7_1
    | ~ spl7_2
    | spl7_5 ),
    inference(subsumption_resolution,[],[f93,f63])).

fof(f63,plain,
    ( v1_funct_1(sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f93,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl7_1
    | spl7_5 ),
    inference(subsumption_resolution,[],[f92,f58])).

fof(f92,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | spl7_5 ),
    inference(superposition,[],[f86,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(f86,plain,
    ( sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f226,plain,
    ( ~ spl7_4
    | spl7_15 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | ~ spl7_4
    | spl7_15 ),
    inference(subsumption_resolution,[],[f224,f81])).

fof(f81,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl7_4
  <=> r2_hidden(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f224,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | spl7_15 ),
    inference(resolution,[],[f220,f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( sP5(X2,X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( sP5(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f220,plain,
    ( ~ sP5(sK0,sK1)
    | spl7_15 ),
    inference(avatar_component_clause,[],[f218])).

fof(f221,plain,
    ( ~ spl7_15
    | ~ spl7_1
    | ~ spl7_2
    | spl7_14 ),
    inference(avatar_split_clause,[],[f214,f208,f61,f56,f218])).

fof(f214,plain,
    ( ~ sP5(sK0,sK1)
    | ~ spl7_1
    | ~ spl7_2
    | spl7_14 ),
    inference(trivial_inequality_removal,[],[f213])).

fof(f213,plain,
    ( sK0 != sK0
    | ~ sP5(sK0,sK1)
    | ~ spl7_1
    | ~ spl7_2
    | spl7_14 ),
    inference(superposition,[],[f210,f106])).

fof(f106,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK6(sK1,X0)) = X0
        | ~ sP5(X0,sK1) )
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(resolution,[],[f73,f39])).

fof(f73,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK1)
        | k1_funct_1(sK1,X2) = X3 )
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f71,f58])).

fof(f71,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(sK1)
        | k1_funct_1(sK1,X2) = X3
        | ~ r2_hidden(k4_tarski(X2,X3),sK1) )
    | ~ spl7_2 ),
    inference(resolution,[],[f63,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f210,plain,
    ( sK0 != k1_funct_1(sK1,sK6(sK1,sK0))
    | spl7_14 ),
    inference(avatar_component_clause,[],[f208])).

fof(f211,plain,
    ( ~ spl7_14
    | spl7_9
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f204,f192,f119,f208])).

fof(f119,plain,
    ( spl7_9
  <=> sK0 = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f204,plain,
    ( sK0 != k1_funct_1(sK1,sK6(sK1,sK0))
    | spl7_9
    | ~ spl7_13 ),
    inference(superposition,[],[f121,f194])).

fof(f121,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))
    | spl7_9 ),
    inference(avatar_component_clause,[],[f119])).

fof(f195,plain,
    ( spl7_13
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f185,f134,f131,f79,f56,f192])).

fof(f131,plain,
    ( spl7_11
  <=> ! [X3,X2] :
        ( k1_funct_1(k4_relat_1(sK1),X2) = X3
        | ~ r2_hidden(k4_tarski(X2,X3),k4_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f185,plain,
    ( k1_funct_1(k4_relat_1(sK1),sK0) = sK6(sK1,sK0)
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(resolution,[],[f172,f81])).

fof(f172,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k2_relat_1(sK1))
        | k1_funct_1(k4_relat_1(sK1),X2) = sK6(sK1,X2) )
    | ~ spl7_1
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(resolution,[],[f162,f52])).

fof(f162,plain,
    ( ! [X4] :
        ( ~ sP5(X4,sK1)
        | k1_funct_1(k4_relat_1(sK1),X4) = sK6(sK1,X4) )
    | ~ spl7_1
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(resolution,[],[f149,f39])).

fof(f149,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | k1_funct_1(k4_relat_1(sK1),X1) = X0 )
    | ~ spl7_1
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(resolution,[],[f144,f132])).

fof(f132,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),k4_relat_1(sK1))
        | k1_funct_1(k4_relat_1(sK1),X2) = X3 )
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f131])).

fof(f141,plain,
    ( ~ spl7_1
    | spl7_12 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | ~ spl7_1
    | spl7_12 ),
    inference(subsumption_resolution,[],[f139,f58])).

fof(f139,plain,
    ( ~ v1_relat_1(sK1)
    | spl7_12 ),
    inference(resolution,[],[f136,f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f136,plain,
    ( ~ v1_relat_1(k4_relat_1(sK1))
    | spl7_12 ),
    inference(avatar_component_clause,[],[f134])).

fof(f137,plain,
    ( spl7_11
    | ~ spl7_12
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f116,f110,f134,f131])).

fof(f116,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(k4_relat_1(sK1))
        | k1_funct_1(k4_relat_1(sK1),X2) = X3
        | ~ r2_hidden(k4_tarski(X2,X3),k4_relat_1(sK1)) )
    | ~ spl7_8 ),
    inference(resolution,[],[f112,f48])).

fof(f122,plain,
    ( ~ spl7_9
    | spl7_6
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f100,f96,f88,f119])).

fof(f88,plain,
    ( spl7_6
  <=> sK0 = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f100,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))
    | spl7_6
    | ~ spl7_7 ),
    inference(superposition,[],[f90,f98])).

fof(f90,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))
    | spl7_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f113,plain,
    ( spl7_8
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f105,f96,f61,f56,f110])).

fof(f105,plain,
    ( v1_funct_1(k4_relat_1(sK1))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f104,f58])).

% (23473)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f104,plain,
    ( v1_funct_1(k4_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f103,f63])).

fof(f103,plain,
    ( v1_funct_1(k4_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl7_7 ),
    inference(superposition,[],[f36,f98])).

fof(f36,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f99,plain,
    ( spl7_7
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f77,f66,f61,f56,f96])).

fof(f66,plain,
    ( spl7_3
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f77,plain,
    ( k2_funct_1(sK1) = k4_relat_1(sK1)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f76,f58])).

fof(f76,plain,
    ( ~ v1_relat_1(sK1)
    | k2_funct_1(sK1) = k4_relat_1(sK1)
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f75,f63])).

fof(f75,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_funct_1(sK1) = k4_relat_1(sK1)
    | ~ spl7_3 ),
    inference(resolution,[],[f68,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f68,plain,
    ( v2_funct_1(sK1)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f91,plain,
    ( ~ spl7_5
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f25,f88,f84])).

fof(f25,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))
    | sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k2_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
            & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).

fof(f82,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f29,f79])).

fof(f29,plain,(
    r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f69,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f28,f66])).

fof(f28,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f64,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f27,f61])).

fof(f27,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f59,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f26,f56])).

fof(f26,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 21:10:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (23487)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.47  % (23475)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.47  % (23479)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (23475)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (23492)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (23492)Refutation not found, incomplete strategy% (23492)------------------------------
% 0.22/0.48  % (23492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (23492)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (23492)Memory used [KB]: 10618
% 0.22/0.48  % (23492)Time elapsed: 0.061 s
% 0.22/0.48  % (23492)------------------------------
% 0.22/0.48  % (23492)------------------------------
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f257,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f59,f64,f69,f82,f91,f99,f113,f122,f137,f141,f195,f211,f221,f226,f248,f256])).
% 0.22/0.49  fof(f256,plain,(
% 0.22/0.49    ~spl7_1 | ~spl7_12 | ~spl7_15 | spl7_16),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f255])).
% 0.22/0.49  fof(f255,plain,(
% 0.22/0.49    $false | (~spl7_1 | ~spl7_12 | ~spl7_15 | spl7_16)),
% 0.22/0.49    inference(subsumption_resolution,[],[f254,f219])).
% 0.22/0.49  fof(f219,plain,(
% 0.22/0.49    sP5(sK0,sK1) | ~spl7_15),
% 0.22/0.49    inference(avatar_component_clause,[],[f218])).
% 0.22/0.49  fof(f218,plain,(
% 0.22/0.49    spl7_15 <=> sP5(sK0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.22/0.49  fof(f254,plain,(
% 0.22/0.49    ~sP5(sK0,sK1) | (~spl7_1 | ~spl7_12 | spl7_16)),
% 0.22/0.49    inference(resolution,[],[f251,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK6(X0,X2),X2),X0) | ~sP5(X2,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.22/0.49  fof(f251,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK0),sK1)) ) | (~spl7_1 | ~spl7_12 | spl7_16)),
% 0.22/0.49    inference(resolution,[],[f250,f144])).
% 0.22/0.49  fof(f144,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,X0),k4_relat_1(sK1)) | ~r2_hidden(k4_tarski(X0,X1),sK1)) ) | (~spl7_1 | ~spl7_12)),
% 0.22/0.49    inference(subsumption_resolution,[],[f142,f58])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    v1_relat_1(sK1) | ~spl7_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f56])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    spl7_1 <=> v1_relat_1(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.49  fof(f142,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_relat_1(sK1) | ~r2_hidden(k4_tarski(X0,X1),sK1) | r2_hidden(k4_tarski(X1,X0),k4_relat_1(sK1))) ) | ~spl7_12),
% 0.22/0.49    inference(resolution,[],[f135,f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X2,X0,X3] : (~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),k4_relat_1(X0))) )),
% 0.22/0.49    inference(equality_resolution,[],[f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1) | k4_relat_1(X0) != X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).
% 0.22/0.49  fof(f135,plain,(
% 0.22/0.49    v1_relat_1(k4_relat_1(sK1)) | ~spl7_12),
% 0.22/0.49    inference(avatar_component_clause,[],[f134])).
% 0.22/0.49  fof(f134,plain,(
% 0.22/0.49    spl7_12 <=> v1_relat_1(k4_relat_1(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.22/0.49  fof(f250,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(k4_tarski(sK0,X0),k4_relat_1(sK1))) ) | (~spl7_12 | spl7_16)),
% 0.22/0.49    inference(subsumption_resolution,[],[f249,f135])).
% 0.22/0.49  fof(f249,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(k4_tarski(sK0,X0),k4_relat_1(sK1)) | ~v1_relat_1(k4_relat_1(sK1))) ) | spl7_16),
% 0.22/0.49    inference(resolution,[],[f247,f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.22/0.49    inference(flattening,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).
% 0.22/0.49  fof(f247,plain,(
% 0.22/0.49    ~r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) | spl7_16),
% 0.22/0.49    inference(avatar_component_clause,[],[f245])).
% 0.22/0.49  fof(f245,plain,(
% 0.22/0.49    spl7_16 <=> r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.22/0.49  fof(f248,plain,(
% 0.22/0.49    ~spl7_14 | ~spl7_16 | ~spl7_1 | ~spl7_2 | spl7_5 | ~spl7_7 | ~spl7_8 | ~spl7_12 | ~spl7_13),
% 0.22/0.49    inference(avatar_split_clause,[],[f233,f192,f134,f110,f96,f84,f61,f56,f245,f208])).
% 0.22/0.49  fof(f208,plain,(
% 0.22/0.49    spl7_14 <=> sK0 = k1_funct_1(sK1,sK6(sK1,sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    spl7_2 <=> v1_funct_1(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    spl7_5 <=> sK0 = k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    spl7_7 <=> k2_funct_1(sK1) = k4_relat_1(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    spl7_8 <=> v1_funct_1(k4_relat_1(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.49  fof(f192,plain,(
% 0.22/0.49    spl7_13 <=> k1_funct_1(k4_relat_1(sK1),sK0) = sK6(sK1,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.22/0.49  fof(f233,plain,(
% 0.22/0.49    ~r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) | sK0 != k1_funct_1(sK1,sK6(sK1,sK0)) | (~spl7_1 | ~spl7_2 | spl7_5 | ~spl7_7 | ~spl7_8 | ~spl7_12 | ~spl7_13)),
% 0.22/0.49    inference(subsumption_resolution,[],[f232,f135])).
% 0.22/0.49  fof(f232,plain,(
% 0.22/0.49    ~v1_relat_1(k4_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) | sK0 != k1_funct_1(sK1,sK6(sK1,sK0)) | (~spl7_1 | ~spl7_2 | spl7_5 | ~spl7_7 | ~spl7_8 | ~spl7_13)),
% 0.22/0.49    inference(forward_demodulation,[],[f231,f98])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    k2_funct_1(sK1) = k4_relat_1(sK1) | ~spl7_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f96])).
% 0.22/0.49  fof(f231,plain,(
% 0.22/0.49    ~r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) | sK0 != k1_funct_1(sK1,sK6(sK1,sK0)) | ~v1_relat_1(k2_funct_1(sK1)) | (~spl7_1 | ~spl7_2 | spl7_5 | ~spl7_7 | ~spl7_8 | ~spl7_13)),
% 0.22/0.49    inference(forward_demodulation,[],[f230,f98])).
% 0.22/0.49  fof(f230,plain,(
% 0.22/0.49    sK0 != k1_funct_1(sK1,sK6(sK1,sK0)) | ~r2_hidden(sK0,k1_relat_1(k2_funct_1(sK1))) | ~v1_relat_1(k2_funct_1(sK1)) | (~spl7_1 | ~spl7_2 | spl7_5 | ~spl7_7 | ~spl7_8 | ~spl7_13)),
% 0.22/0.49    inference(subsumption_resolution,[],[f229,f112])).
% 0.22/0.49  fof(f112,plain,(
% 0.22/0.49    v1_funct_1(k4_relat_1(sK1)) | ~spl7_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f110])).
% 0.22/0.49  fof(f229,plain,(
% 0.22/0.49    ~v1_funct_1(k4_relat_1(sK1)) | sK0 != k1_funct_1(sK1,sK6(sK1,sK0)) | ~r2_hidden(sK0,k1_relat_1(k2_funct_1(sK1))) | ~v1_relat_1(k2_funct_1(sK1)) | (~spl7_1 | ~spl7_2 | spl7_5 | ~spl7_7 | ~spl7_13)),
% 0.22/0.49    inference(forward_demodulation,[],[f228,f98])).
% 0.22/0.49  fof(f228,plain,(
% 0.22/0.49    sK0 != k1_funct_1(sK1,sK6(sK1,sK0)) | ~v1_funct_1(k2_funct_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(k2_funct_1(sK1))) | ~v1_relat_1(k2_funct_1(sK1)) | (~spl7_1 | ~spl7_2 | spl7_5 | ~spl7_7 | ~spl7_13)),
% 0.22/0.49    inference(forward_demodulation,[],[f227,f194])).
% 0.22/0.49  fof(f194,plain,(
% 0.22/0.49    k1_funct_1(k4_relat_1(sK1),sK0) = sK6(sK1,sK0) | ~spl7_13),
% 0.22/0.49    inference(avatar_component_clause,[],[f192])).
% 0.22/0.49  fof(f227,plain,(
% 0.22/0.49    sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) | ~v1_funct_1(k2_funct_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(k2_funct_1(sK1))) | ~v1_relat_1(k2_funct_1(sK1)) | (~spl7_1 | ~spl7_2 | spl7_5 | ~spl7_7)),
% 0.22/0.49    inference(forward_demodulation,[],[f94,f98])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) | ~v1_funct_1(k2_funct_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(k2_funct_1(sK1))) | ~v1_relat_1(k2_funct_1(sK1)) | (~spl7_1 | ~spl7_2 | spl7_5)),
% 0.22/0.49    inference(subsumption_resolution,[],[f93,f63])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    v1_funct_1(sK1) | ~spl7_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f61])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1) | ~r2_hidden(sK0,k1_relat_1(k2_funct_1(sK1))) | ~v1_relat_1(k2_funct_1(sK1)) | (~spl7_1 | spl7_5)),
% 0.22/0.49    inference(subsumption_resolution,[],[f92,f58])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~r2_hidden(sK0,k1_relat_1(k2_funct_1(sK1))) | ~v1_relat_1(k2_funct_1(sK1)) | spl7_5),
% 0.22/0.49    inference(superposition,[],[f86,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) | spl7_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f84])).
% 0.22/0.49  fof(f226,plain,(
% 0.22/0.49    ~spl7_4 | spl7_15),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f225])).
% 0.22/0.49  fof(f225,plain,(
% 0.22/0.49    $false | (~spl7_4 | spl7_15)),
% 0.22/0.49    inference(subsumption_resolution,[],[f224,f81])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    r2_hidden(sK0,k2_relat_1(sK1)) | ~spl7_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f79])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    spl7_4 <=> r2_hidden(sK0,k2_relat_1(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.49  fof(f224,plain,(
% 0.22/0.49    ~r2_hidden(sK0,k2_relat_1(sK1)) | spl7_15),
% 0.22/0.49    inference(resolution,[],[f220,f52])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ( ! [X2,X0] : (sP5(X2,X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.22/0.49    inference(equality_resolution,[],[f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (sP5(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f220,plain,(
% 0.22/0.49    ~sP5(sK0,sK1) | spl7_15),
% 0.22/0.49    inference(avatar_component_clause,[],[f218])).
% 0.22/0.49  fof(f221,plain,(
% 0.22/0.49    ~spl7_15 | ~spl7_1 | ~spl7_2 | spl7_14),
% 0.22/0.49    inference(avatar_split_clause,[],[f214,f208,f61,f56,f218])).
% 0.22/0.49  fof(f214,plain,(
% 0.22/0.49    ~sP5(sK0,sK1) | (~spl7_1 | ~spl7_2 | spl7_14)),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f213])).
% 0.22/0.49  fof(f213,plain,(
% 0.22/0.49    sK0 != sK0 | ~sP5(sK0,sK1) | (~spl7_1 | ~spl7_2 | spl7_14)),
% 0.22/0.49    inference(superposition,[],[f210,f106])).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    ( ! [X0] : (k1_funct_1(sK1,sK6(sK1,X0)) = X0 | ~sP5(X0,sK1)) ) | (~spl7_1 | ~spl7_2)),
% 0.22/0.49    inference(resolution,[],[f73,f39])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK1) | k1_funct_1(sK1,X2) = X3) ) | (~spl7_1 | ~spl7_2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f71,f58])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    ( ! [X2,X3] : (~v1_relat_1(sK1) | k1_funct_1(sK1,X2) = X3 | ~r2_hidden(k4_tarski(X2,X3),sK1)) ) | ~spl7_2),
% 0.22/0.49    inference(resolution,[],[f63,f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.49    inference(flattening,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.22/0.49  fof(f210,plain,(
% 0.22/0.49    sK0 != k1_funct_1(sK1,sK6(sK1,sK0)) | spl7_14),
% 0.22/0.49    inference(avatar_component_clause,[],[f208])).
% 0.22/0.49  fof(f211,plain,(
% 0.22/0.49    ~spl7_14 | spl7_9 | ~spl7_13),
% 0.22/0.49    inference(avatar_split_clause,[],[f204,f192,f119,f208])).
% 0.22/0.49  fof(f119,plain,(
% 0.22/0.49    spl7_9 <=> sK0 = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.49  fof(f204,plain,(
% 0.22/0.49    sK0 != k1_funct_1(sK1,sK6(sK1,sK0)) | (spl7_9 | ~spl7_13)),
% 0.22/0.49    inference(superposition,[],[f121,f194])).
% 0.22/0.49  fof(f121,plain,(
% 0.22/0.49    sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) | spl7_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f119])).
% 0.22/0.49  fof(f195,plain,(
% 0.22/0.49    spl7_13 | ~spl7_1 | ~spl7_4 | ~spl7_11 | ~spl7_12),
% 0.22/0.49    inference(avatar_split_clause,[],[f185,f134,f131,f79,f56,f192])).
% 0.22/0.49  fof(f131,plain,(
% 0.22/0.49    spl7_11 <=> ! [X3,X2] : (k1_funct_1(k4_relat_1(sK1),X2) = X3 | ~r2_hidden(k4_tarski(X2,X3),k4_relat_1(sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.22/0.49  fof(f185,plain,(
% 0.22/0.49    k1_funct_1(k4_relat_1(sK1),sK0) = sK6(sK1,sK0) | (~spl7_1 | ~spl7_4 | ~spl7_11 | ~spl7_12)),
% 0.22/0.49    inference(resolution,[],[f172,f81])).
% 0.22/0.49  fof(f172,plain,(
% 0.22/0.49    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(sK1)) | k1_funct_1(k4_relat_1(sK1),X2) = sK6(sK1,X2)) ) | (~spl7_1 | ~spl7_11 | ~spl7_12)),
% 0.22/0.49    inference(resolution,[],[f162,f52])).
% 0.22/0.49  fof(f162,plain,(
% 0.22/0.49    ( ! [X4] : (~sP5(X4,sK1) | k1_funct_1(k4_relat_1(sK1),X4) = sK6(sK1,X4)) ) | (~spl7_1 | ~spl7_11 | ~spl7_12)),
% 0.22/0.49    inference(resolution,[],[f149,f39])).
% 0.22/0.49  fof(f149,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | k1_funct_1(k4_relat_1(sK1),X1) = X0) ) | (~spl7_1 | ~spl7_11 | ~spl7_12)),
% 0.22/0.49    inference(resolution,[],[f144,f132])).
% 0.22/0.49  fof(f132,plain,(
% 0.22/0.49    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),k4_relat_1(sK1)) | k1_funct_1(k4_relat_1(sK1),X2) = X3) ) | ~spl7_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f131])).
% 0.22/0.49  fof(f141,plain,(
% 0.22/0.49    ~spl7_1 | spl7_12),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f140])).
% 0.22/0.49  fof(f140,plain,(
% 0.22/0.49    $false | (~spl7_1 | spl7_12)),
% 0.22/0.49    inference(subsumption_resolution,[],[f139,f58])).
% 0.22/0.49  fof(f139,plain,(
% 0.22/0.49    ~v1_relat_1(sK1) | spl7_12),
% 0.22/0.49    inference(resolution,[],[f136,f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.22/0.49  fof(f136,plain,(
% 0.22/0.49    ~v1_relat_1(k4_relat_1(sK1)) | spl7_12),
% 0.22/0.49    inference(avatar_component_clause,[],[f134])).
% 0.22/0.49  fof(f137,plain,(
% 0.22/0.49    spl7_11 | ~spl7_12 | ~spl7_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f116,f110,f134,f131])).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    ( ! [X2,X3] : (~v1_relat_1(k4_relat_1(sK1)) | k1_funct_1(k4_relat_1(sK1),X2) = X3 | ~r2_hidden(k4_tarski(X2,X3),k4_relat_1(sK1))) ) | ~spl7_8),
% 0.22/0.49    inference(resolution,[],[f112,f48])).
% 0.22/0.49  fof(f122,plain,(
% 0.22/0.49    ~spl7_9 | spl7_6 | ~spl7_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f100,f96,f88,f119])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    spl7_6 <=> sK0 = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) | (spl7_6 | ~spl7_7)),
% 0.22/0.49    inference(superposition,[],[f90,f98])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) | spl7_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f88])).
% 0.22/0.49  fof(f113,plain,(
% 0.22/0.49    spl7_8 | ~spl7_1 | ~spl7_2 | ~spl7_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f105,f96,f61,f56,f110])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    v1_funct_1(k4_relat_1(sK1)) | (~spl7_1 | ~spl7_2 | ~spl7_7)),
% 0.22/0.49    inference(subsumption_resolution,[],[f104,f58])).
% 0.22/0.49  % (23473)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    v1_funct_1(k4_relat_1(sK1)) | ~v1_relat_1(sK1) | (~spl7_2 | ~spl7_7)),
% 0.22/0.49    inference(subsumption_resolution,[],[f103,f63])).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    v1_funct_1(k4_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl7_7),
% 0.22/0.49    inference(superposition,[],[f36,f98])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    spl7_7 | ~spl7_1 | ~spl7_2 | ~spl7_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f77,f66,f61,f56,f96])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    spl7_3 <=> v2_funct_1(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    k2_funct_1(sK1) = k4_relat_1(sK1) | (~spl7_1 | ~spl7_2 | ~spl7_3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f76,f58])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    ~v1_relat_1(sK1) | k2_funct_1(sK1) = k4_relat_1(sK1) | (~spl7_2 | ~spl7_3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f75,f63])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k2_funct_1(sK1) = k4_relat_1(sK1) | ~spl7_3),
% 0.22/0.49    inference(resolution,[],[f68,f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    v2_funct_1(sK1) | ~spl7_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f66])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    ~spl7_5 | ~spl7_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f25,f88,f84])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) | sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X0,X1] : (((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & (r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 0.22/0.49    inference(negated_conjecture,[],[f9])).
% 0.22/0.49  fof(f9,conjecture,(
% 0.22/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    spl7_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f29,f79])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    r2_hidden(sK0,k2_relat_1(sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    spl7_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f28,f66])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    v2_funct_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    spl7_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f27,f61])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    v1_funct_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    spl7_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f26,f56])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    v1_relat_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (23475)------------------------------
% 0.22/0.49  % (23475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (23475)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (23475)Memory used [KB]: 10746
% 0.22/0.49  % (23475)Time elapsed: 0.060 s
% 0.22/0.49  % (23475)------------------------------
% 0.22/0.49  % (23475)------------------------------
% 0.22/0.49  % (23473)Refutation not found, incomplete strategy% (23473)------------------------------
% 0.22/0.49  % (23473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (23473)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (23473)Memory used [KB]: 10618
% 0.22/0.49  % (23473)Time elapsed: 0.073 s
% 0.22/0.49  % (23473)------------------------------
% 0.22/0.49  % (23473)------------------------------
% 0.22/0.49  % (23471)Success in time 0.129 s
%------------------------------------------------------------------------------
