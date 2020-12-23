%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 177 expanded)
%              Number of leaves         :   25 (  78 expanded)
%              Depth                    :    7
%              Number of atoms          :  337 ( 592 expanded)
%              Number of equality atoms :   45 (  81 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f183,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f46,f51,f55,f59,f63,f67,f71,f79,f83,f95,f107,f121,f127,f152,f162,f176,f182])).

fof(f182,plain,
    ( spl3_1
    | ~ spl3_19
    | ~ spl3_27 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | spl3_1
    | ~ spl3_19
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f178,f35])).

fof(f35,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k8_relat_1(sK1,sK2),sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl3_1
  <=> k1_funct_1(sK2,sK0) = k1_funct_1(k8_relat_1(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f178,plain,
    ( k1_funct_1(sK2,sK0) = k1_funct_1(k8_relat_1(sK1,sK2),sK0)
    | ~ spl3_19
    | ~ spl3_27 ),
    inference(superposition,[],[f126,f175])).

fof(f175,plain,
    ( ! [X0] : k1_funct_1(k6_relat_1(X0),k1_funct_1(sK2,sK0)) = k1_funct_1(k8_relat_1(X0,sK2),sK0)
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl3_27
  <=> ! [X0] : k1_funct_1(k6_relat_1(X0),k1_funct_1(sK2,sK0)) = k1_funct_1(k8_relat_1(X0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f126,plain,
    ( k1_funct_1(sK2,sK0) = k1_funct_1(k6_relat_1(sK1),k1_funct_1(sK2,sK0))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl3_19
  <=> k1_funct_1(sK2,sK0) = k1_funct_1(k6_relat_1(sK1),k1_funct_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f176,plain,
    ( spl3_27
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_14
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f172,f160,f93,f57,f53,f174])).

fof(f53,plain,
    ( spl3_5
  <=> ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f57,plain,
    ( spl3_6
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f93,plain,
    ( spl3_14
  <=> ! [X0] : k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f160,plain,
    ( spl3_25
  <=> ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k1_funct_1(k5_relat_1(sK2,X0),sK0) = k1_funct_1(X0,k1_funct_1(sK2,sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f172,plain,
    ( ! [X0] : k1_funct_1(k6_relat_1(X0),k1_funct_1(sK2,sK0)) = k1_funct_1(k8_relat_1(X0,sK2),sK0)
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_14
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f171,f94])).

fof(f94,plain,
    ( ! [X0] : k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f93])).

fof(f171,plain,
    ( ! [X0] : k1_funct_1(k5_relat_1(sK2,k6_relat_1(X0)),sK0) = k1_funct_1(k6_relat_1(X0),k1_funct_1(sK2,sK0))
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f164,f58])).

fof(f58,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k6_relat_1(X0))
        | k1_funct_1(k5_relat_1(sK2,k6_relat_1(X0)),sK0) = k1_funct_1(k6_relat_1(X0),k1_funct_1(sK2,sK0)) )
    | ~ spl3_5
    | ~ spl3_25 ),
    inference(resolution,[],[f161,f54])).

fof(f54,plain,
    ( ! [X0] : v1_funct_1(k6_relat_1(X0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f161,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k1_funct_1(k5_relat_1(sK2,X0),sK0) = k1_funct_1(X0,k1_funct_1(sK2,sK0)) )
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f160])).

fof(f162,plain,
    ( spl3_25
    | ~ spl3_16
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f158,f150,f104,f160])).

fof(f104,plain,
    ( spl3_16
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f150,plain,
    ( spl3_23
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | k1_funct_1(k5_relat_1(sK2,X1),X0) = k1_funct_1(X1,k1_funct_1(sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k1_funct_1(k5_relat_1(sK2,X0),sK0) = k1_funct_1(X0,k1_funct_1(sK2,sK0)) )
    | ~ spl3_16
    | ~ spl3_23 ),
    inference(resolution,[],[f151,f106])).

fof(f106,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f104])).

fof(f151,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | k1_funct_1(k5_relat_1(sK2,X1),X0) = k1_funct_1(X1,k1_funct_1(sK2,X0)) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f150])).

fof(f152,plain,
    ( spl3_23
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f148,f69,f48,f43,f150])).

fof(f43,plain,
    ( spl3_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f48,plain,
    ( spl3_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f69,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
        | ~ r2_hidden(X0,k1_relat_1(X1))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f148,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | k1_funct_1(k5_relat_1(sK2,X1),X0) = k1_funct_1(X1,k1_funct_1(sK2,X0)) )
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f146,f50])).

fof(f50,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f146,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | k1_funct_1(k5_relat_1(sK2,X1),X0) = k1_funct_1(X1,k1_funct_1(sK2,X0))
        | ~ v1_relat_1(sK2) )
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(resolution,[],[f70,f45])).

fof(f45,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f70,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X1)
        | ~ r2_hidden(X0,k1_relat_1(X1))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
        | ~ v1_relat_1(X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f127,plain,
    ( spl3_19
    | ~ spl3_8
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f122,f118,f65,f124])).

fof(f65,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k1_funct_1(k6_relat_1(X1),X0) = X0
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f118,plain,
    ( spl3_18
  <=> r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f122,plain,
    ( k1_funct_1(sK2,sK0) = k1_funct_1(k6_relat_1(sK1),k1_funct_1(sK2,sK0))
    | ~ spl3_8
    | ~ spl3_18 ),
    inference(resolution,[],[f120,f66])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | k1_funct_1(k6_relat_1(X1),X0) = X0 )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f120,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f118])).

fof(f121,plain,
    ( spl3_18
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f116,f77,f48,f43,f38,f118])).

fof(f38,plain,
    ( spl3_2
  <=> r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f77,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] :
        ( r2_hidden(k1_funct_1(X2,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f116,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f115,f50])).

fof(f115,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f114,f45])).

fof(f114,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(resolution,[],[f78,f40])).

fof(f40,plain,
    ( r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f78,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
        | r2_hidden(k1_funct_1(X2,X0),X1)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f77])).

fof(f107,plain,
    ( spl3_16
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f102,f81,f48,f43,f38,f104])).

fof(f81,plain,
    ( spl3_12
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f102,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f101,f50])).

fof(f101,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f100,f45])).

fof(f100,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(resolution,[],[f82,f40])).

fof(f82,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
        | r2_hidden(X0,k1_relat_1(X2))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f81])).

fof(f95,plain,
    ( spl3_14
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f90,f61,f48,f93])).

fof(f61,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f90,plain,
    ( ! [X0] : k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0))
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(resolution,[],[f62,f50])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f83,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f29,f81])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).

fof(f79,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f30,f77])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X2,X0),X1)
      | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f71,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f28,f69])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(f67,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f27,f65])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).

fof(f63,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f26,f61])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f59,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f24,f57])).

fof(f24,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f55,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f25,f53])).

fof(f25,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f51,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f20,f48])).

fof(f20,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k8_relat_1(sK1,sK2),sK0)
    & r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(X2,X0) != k1_funct_1(k8_relat_1(X1,X2),X0)
        & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(sK2,sK0) != k1_funct_1(k8_relat_1(sK1,sK2),sK0)
      & r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k8_relat_1(X1,X2),X0)
      & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k8_relat_1(X1,X2),X0)
      & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
         => k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
       => k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_1)).

fof(f46,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f21,f43])).

fof(f21,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f22,f38])).

fof(f22,plain,(
    r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f17])).

fof(f36,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f23,f33])).

fof(f23,plain,(
    k1_funct_1(sK2,sK0) != k1_funct_1(k8_relat_1(sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:32:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.44  % (4086)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.44  % (4084)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.44  % (4085)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.44  % (4087)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.44  % (4085)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f183,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f36,f41,f46,f51,f55,f59,f63,f67,f71,f79,f83,f95,f107,f121,f127,f152,f162,f176,f182])).
% 0.22/0.44  fof(f182,plain,(
% 0.22/0.44    spl3_1 | ~spl3_19 | ~spl3_27),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f181])).
% 0.22/0.44  fof(f181,plain,(
% 0.22/0.44    $false | (spl3_1 | ~spl3_19 | ~spl3_27)),
% 0.22/0.44    inference(subsumption_resolution,[],[f178,f35])).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    k1_funct_1(sK2,sK0) != k1_funct_1(k8_relat_1(sK1,sK2),sK0) | spl3_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f33])).
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    spl3_1 <=> k1_funct_1(sK2,sK0) = k1_funct_1(k8_relat_1(sK1,sK2),sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.44  fof(f178,plain,(
% 0.22/0.44    k1_funct_1(sK2,sK0) = k1_funct_1(k8_relat_1(sK1,sK2),sK0) | (~spl3_19 | ~spl3_27)),
% 0.22/0.44    inference(superposition,[],[f126,f175])).
% 0.22/0.44  fof(f175,plain,(
% 0.22/0.44    ( ! [X0] : (k1_funct_1(k6_relat_1(X0),k1_funct_1(sK2,sK0)) = k1_funct_1(k8_relat_1(X0,sK2),sK0)) ) | ~spl3_27),
% 0.22/0.44    inference(avatar_component_clause,[],[f174])).
% 0.22/0.44  fof(f174,plain,(
% 0.22/0.44    spl3_27 <=> ! [X0] : k1_funct_1(k6_relat_1(X0),k1_funct_1(sK2,sK0)) = k1_funct_1(k8_relat_1(X0,sK2),sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.22/0.44  fof(f126,plain,(
% 0.22/0.44    k1_funct_1(sK2,sK0) = k1_funct_1(k6_relat_1(sK1),k1_funct_1(sK2,sK0)) | ~spl3_19),
% 0.22/0.44    inference(avatar_component_clause,[],[f124])).
% 0.22/0.44  fof(f124,plain,(
% 0.22/0.44    spl3_19 <=> k1_funct_1(sK2,sK0) = k1_funct_1(k6_relat_1(sK1),k1_funct_1(sK2,sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.44  fof(f176,plain,(
% 0.22/0.44    spl3_27 | ~spl3_5 | ~spl3_6 | ~spl3_14 | ~spl3_25),
% 0.22/0.44    inference(avatar_split_clause,[],[f172,f160,f93,f57,f53,f174])).
% 0.22/0.44  fof(f53,plain,(
% 0.22/0.44    spl3_5 <=> ! [X0] : v1_funct_1(k6_relat_1(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.44  fof(f57,plain,(
% 0.22/0.44    spl3_6 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.44  fof(f93,plain,(
% 0.22/0.44    spl3_14 <=> ! [X0] : k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.44  fof(f160,plain,(
% 0.22/0.44    spl3_25 <=> ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_funct_1(k5_relat_1(sK2,X0),sK0) = k1_funct_1(X0,k1_funct_1(sK2,sK0)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.22/0.44  fof(f172,plain,(
% 0.22/0.44    ( ! [X0] : (k1_funct_1(k6_relat_1(X0),k1_funct_1(sK2,sK0)) = k1_funct_1(k8_relat_1(X0,sK2),sK0)) ) | (~spl3_5 | ~spl3_6 | ~spl3_14 | ~spl3_25)),
% 0.22/0.44    inference(forward_demodulation,[],[f171,f94])).
% 0.22/0.44  fof(f94,plain,(
% 0.22/0.44    ( ! [X0] : (k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0))) ) | ~spl3_14),
% 0.22/0.44    inference(avatar_component_clause,[],[f93])).
% 0.22/0.44  fof(f171,plain,(
% 0.22/0.44    ( ! [X0] : (k1_funct_1(k5_relat_1(sK2,k6_relat_1(X0)),sK0) = k1_funct_1(k6_relat_1(X0),k1_funct_1(sK2,sK0))) ) | (~spl3_5 | ~spl3_6 | ~spl3_25)),
% 0.22/0.44    inference(subsumption_resolution,[],[f164,f58])).
% 0.22/0.44  fof(f58,plain,(
% 0.22/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl3_6),
% 0.22/0.44    inference(avatar_component_clause,[],[f57])).
% 0.22/0.44  fof(f164,plain,(
% 0.22/0.44    ( ! [X0] : (~v1_relat_1(k6_relat_1(X0)) | k1_funct_1(k5_relat_1(sK2,k6_relat_1(X0)),sK0) = k1_funct_1(k6_relat_1(X0),k1_funct_1(sK2,sK0))) ) | (~spl3_5 | ~spl3_25)),
% 0.22/0.44    inference(resolution,[],[f161,f54])).
% 0.22/0.44  fof(f54,plain,(
% 0.22/0.44    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) ) | ~spl3_5),
% 0.22/0.44    inference(avatar_component_clause,[],[f53])).
% 0.22/0.44  fof(f161,plain,(
% 0.22/0.44    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_funct_1(k5_relat_1(sK2,X0),sK0) = k1_funct_1(X0,k1_funct_1(sK2,sK0))) ) | ~spl3_25),
% 0.22/0.44    inference(avatar_component_clause,[],[f160])).
% 0.22/0.44  fof(f162,plain,(
% 0.22/0.44    spl3_25 | ~spl3_16 | ~spl3_23),
% 0.22/0.44    inference(avatar_split_clause,[],[f158,f150,f104,f160])).
% 0.22/0.44  fof(f104,plain,(
% 0.22/0.44    spl3_16 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.44  fof(f150,plain,(
% 0.22/0.44    spl3_23 <=> ! [X1,X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k1_funct_1(k5_relat_1(sK2,X1),X0) = k1_funct_1(X1,k1_funct_1(sK2,X0)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.44  fof(f158,plain,(
% 0.22/0.44    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_funct_1(k5_relat_1(sK2,X0),sK0) = k1_funct_1(X0,k1_funct_1(sK2,sK0))) ) | (~spl3_16 | ~spl3_23)),
% 0.22/0.44    inference(resolution,[],[f151,f106])).
% 0.22/0.44  fof(f106,plain,(
% 0.22/0.44    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl3_16),
% 0.22/0.44    inference(avatar_component_clause,[],[f104])).
% 0.22/0.44  fof(f151,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k1_funct_1(k5_relat_1(sK2,X1),X0) = k1_funct_1(X1,k1_funct_1(sK2,X0))) ) | ~spl3_23),
% 0.22/0.44    inference(avatar_component_clause,[],[f150])).
% 0.22/0.44  fof(f152,plain,(
% 0.22/0.44    spl3_23 | ~spl3_3 | ~spl3_4 | ~spl3_9),
% 0.22/0.44    inference(avatar_split_clause,[],[f148,f69,f48,f43,f150])).
% 0.22/0.44  fof(f43,plain,(
% 0.22/0.44    spl3_3 <=> v1_funct_1(sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.44  fof(f48,plain,(
% 0.22/0.44    spl3_4 <=> v1_relat_1(sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.44  fof(f69,plain,(
% 0.22/0.44    spl3_9 <=> ! [X1,X0,X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.44  fof(f148,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k1_funct_1(k5_relat_1(sK2,X1),X0) = k1_funct_1(X1,k1_funct_1(sK2,X0))) ) | (~spl3_3 | ~spl3_4 | ~spl3_9)),
% 0.22/0.44    inference(subsumption_resolution,[],[f146,f50])).
% 0.22/0.44  fof(f50,plain,(
% 0.22/0.44    v1_relat_1(sK2) | ~spl3_4),
% 0.22/0.44    inference(avatar_component_clause,[],[f48])).
% 0.22/0.44  fof(f146,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k1_funct_1(k5_relat_1(sK2,X1),X0) = k1_funct_1(X1,k1_funct_1(sK2,X0)) | ~v1_relat_1(sK2)) ) | (~spl3_3 | ~spl3_9)),
% 0.22/0.44    inference(resolution,[],[f70,f45])).
% 0.22/0.44  fof(f45,plain,(
% 0.22/0.44    v1_funct_1(sK2) | ~spl3_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f43])).
% 0.22/0.44  fof(f70,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~v1_relat_1(X1)) ) | ~spl3_9),
% 0.22/0.44    inference(avatar_component_clause,[],[f69])).
% 0.22/0.44  fof(f127,plain,(
% 0.22/0.44    spl3_19 | ~spl3_8 | ~spl3_18),
% 0.22/0.44    inference(avatar_split_clause,[],[f122,f118,f65,f124])).
% 0.22/0.44  fof(f65,plain,(
% 0.22/0.44    spl3_8 <=> ! [X1,X0] : (k1_funct_1(k6_relat_1(X1),X0) = X0 | ~r2_hidden(X0,X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.44  fof(f118,plain,(
% 0.22/0.44    spl3_18 <=> r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.44  fof(f122,plain,(
% 0.22/0.44    k1_funct_1(sK2,sK0) = k1_funct_1(k6_relat_1(sK1),k1_funct_1(sK2,sK0)) | (~spl3_8 | ~spl3_18)),
% 0.22/0.44    inference(resolution,[],[f120,f66])).
% 0.22/0.44  fof(f66,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_funct_1(k6_relat_1(X1),X0) = X0) ) | ~spl3_8),
% 0.22/0.44    inference(avatar_component_clause,[],[f65])).
% 0.22/0.44  fof(f120,plain,(
% 0.22/0.44    r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~spl3_18),
% 0.22/0.44    inference(avatar_component_clause,[],[f118])).
% 0.22/0.44  fof(f121,plain,(
% 0.22/0.44    spl3_18 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_11),
% 0.22/0.44    inference(avatar_split_clause,[],[f116,f77,f48,f43,f38,f118])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    spl3_2 <=> r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.44  fof(f77,plain,(
% 0.22/0.44    spl3_11 <=> ! [X1,X0,X2] : (r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.44  fof(f116,plain,(
% 0.22/0.44    r2_hidden(k1_funct_1(sK2,sK0),sK1) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_11)),
% 0.22/0.44    inference(subsumption_resolution,[],[f115,f50])).
% 0.22/0.44  fof(f115,plain,(
% 0.22/0.44    r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~v1_relat_1(sK2) | (~spl3_2 | ~spl3_3 | ~spl3_11)),
% 0.22/0.44    inference(subsumption_resolution,[],[f114,f45])).
% 0.22/0.44  fof(f114,plain,(
% 0.22/0.44    r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_2 | ~spl3_11)),
% 0.22/0.44    inference(resolution,[],[f78,f40])).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) | ~spl3_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f38])).
% 0.22/0.44  fof(f78,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | r2_hidden(k1_funct_1(X2,X0),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | ~spl3_11),
% 0.22/0.44    inference(avatar_component_clause,[],[f77])).
% 0.22/0.44  fof(f107,plain,(
% 0.22/0.44    spl3_16 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_12),
% 0.22/0.44    inference(avatar_split_clause,[],[f102,f81,f48,f43,f38,f104])).
% 0.22/0.44  fof(f81,plain,(
% 0.22/0.44    spl3_12 <=> ! [X1,X0,X2] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.44  fof(f102,plain,(
% 0.22/0.44    r2_hidden(sK0,k1_relat_1(sK2)) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_12)),
% 0.22/0.44    inference(subsumption_resolution,[],[f101,f50])).
% 0.22/0.44  fof(f101,plain,(
% 0.22/0.44    r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl3_2 | ~spl3_3 | ~spl3_12)),
% 0.22/0.44    inference(subsumption_resolution,[],[f100,f45])).
% 0.22/0.44  fof(f100,plain,(
% 0.22/0.44    r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_2 | ~spl3_12)),
% 0.22/0.44    inference(resolution,[],[f82,f40])).
% 0.22/0.44  fof(f82,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | ~spl3_12),
% 0.22/0.44    inference(avatar_component_clause,[],[f81])).
% 0.22/0.44  fof(f95,plain,(
% 0.22/0.44    spl3_14 | ~spl3_4 | ~spl3_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f90,f61,f48,f93])).
% 0.22/0.44  fof(f61,plain,(
% 0.22/0.44    spl3_7 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.44  fof(f90,plain,(
% 0.22/0.44    ( ! [X0] : (k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0))) ) | (~spl3_4 | ~spl3_7)),
% 0.22/0.44    inference(resolution,[],[f62,f50])).
% 0.22/0.44  fof(f62,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) ) | ~spl3_7),
% 0.22/0.44    inference(avatar_component_clause,[],[f61])).
% 0.22/0.44  fof(f83,plain,(
% 0.22/0.44    spl3_12),
% 0.22/0.44    inference(avatar_split_clause,[],[f29,f81])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | ~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.44    inference(flattening,[],[f18])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | (~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.44    inference(nnf_transformation,[],[f15])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.44    inference(flattening,[],[f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.44    inference(ennf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).
% 0.22/0.44  fof(f79,plain,(
% 0.22/0.44    spl3_11),
% 0.22/0.44    inference(avatar_split_clause,[],[f30,f77])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  fof(f71,plain,(
% 0.22/0.44    spl3_9),
% 0.22/0.44    inference(avatar_split_clause,[],[f28,f69])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(flattening,[],[f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.44    inference(ennf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).
% 0.22/0.44  fof(f67,plain,(
% 0.22/0.44    spl3_8),
% 0.22/0.44    inference(avatar_split_clause,[],[f27,f65])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k1_funct_1(k6_relat_1(X1),X0) = X0 | ~r2_hidden(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ! [X0,X1] : (k1_funct_1(k6_relat_1(X1),X0) = X0 | ~r2_hidden(X0,X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0,X1] : (r2_hidden(X0,X1) => k1_funct_1(k6_relat_1(X1),X0) = X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).
% 0.22/0.44  fof(f63,plain,(
% 0.22/0.44    spl3_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f26,f61])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.22/0.44  fof(f59,plain,(
% 0.22/0.44    spl3_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f24,f57])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.44  fof(f55,plain,(
% 0.22/0.44    spl3_5),
% 0.22/0.44    inference(avatar_split_clause,[],[f25,f53])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f2])).
% 0.22/0.44  fof(f51,plain,(
% 0.22/0.44    spl3_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f20,f48])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    v1_relat_1(sK2)),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    k1_funct_1(sK2,sK0) != k1_funct_1(k8_relat_1(sK1,sK2),sK0) & r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k8_relat_1(X1,X2),X0) & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(sK2,sK0) != k1_funct_1(k8_relat_1(sK1,sK2),sK0) & r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k8_relat_1(X1,X2),X0) & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.44    inference(flattening,[],[f8])).
% 0.22/0.44  fof(f8,plain,(
% 0.22/0.44    ? [X0,X1,X2] : ((k1_funct_1(X2,X0) != k1_funct_1(k8_relat_1(X1,X2),X0) & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.44    inference(ennf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) => k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0)))),
% 0.22/0.44    inference(negated_conjecture,[],[f6])).
% 0.22/0.44  fof(f6,conjecture,(
% 0.22/0.44    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) => k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_1)).
% 0.22/0.44  fof(f46,plain,(
% 0.22/0.44    spl3_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f21,f43])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    v1_funct_1(sK2)),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    spl3_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f22,f38])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    ~spl3_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f23,f33])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    k1_funct_1(sK2,sK0) != k1_funct_1(k8_relat_1(sK1,sK2),sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (4085)------------------------------
% 0.22/0.44  % (4085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (4085)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (4085)Memory used [KB]: 10618
% 0.22/0.44  % (4085)Time elapsed: 0.007 s
% 0.22/0.44  % (4085)------------------------------
% 0.22/0.44  % (4085)------------------------------
% 0.22/0.45  % (4079)Success in time 0.074 s
%------------------------------------------------------------------------------
