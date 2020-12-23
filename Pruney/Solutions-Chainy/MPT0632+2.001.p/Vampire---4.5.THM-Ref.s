%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 181 expanded)
%              Number of leaves         :   19 (  85 expanded)
%              Depth                    :    8
%              Number of atoms          :  300 ( 615 expanded)
%              Number of equality atoms :   77 ( 195 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f477,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f54,f59,f64,f68,f100,f121,f127,f136,f295,f309,f332,f359,f392,f396,f476])).

fof(f476,plain,
    ( spl5_5
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f468,f134,f119,f61,f56])).

fof(f56,plain,
    ( spl5_5
  <=> sK2 = k1_funct_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f61,plain,
    ( spl5_6
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f119,plain,
    ( spl5_14
  <=> ! [X2] :
        ( r2_hidden(k4_tarski(X2,X2),sK1)
        | ~ r2_hidden(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f134,plain,
    ( spl5_16
  <=> ! [X1,X0] :
        ( k1_funct_1(sK1,X0) = X1
        | ~ r2_hidden(k4_tarski(X0,X1),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f468,plain,
    ( sK2 = k1_funct_1(sK1,sK2)
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(resolution,[],[f439,f63])).

fof(f63,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f439,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(sK1,X0) = X0 )
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(resolution,[],[f120,f135])).

fof(f135,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | k1_funct_1(sK1,X0) = X1 )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f134])).

fof(f120,plain,
    ( ! [X2] :
        ( r2_hidden(k4_tarski(X2,X2),sK1)
        | ~ r2_hidden(X2,sK0) )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f119])).

fof(f396,plain,
    ( spl5_35
    | ~ spl5_7
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f338,f292,f66,f277])).

fof(f277,plain,
    ( spl5_35
  <=> sK3(sK0,sK1) = k1_funct_1(sK1,sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f66,plain,
    ( spl5_7
  <=> ! [X2] :
        ( ~ r2_hidden(X2,sK0)
        | k1_funct_1(sK1,X2) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f292,plain,
    ( spl5_38
  <=> r2_hidden(sK3(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f338,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK1,sK3(sK0,sK1))
    | ~ spl5_7
    | ~ spl5_38 ),
    inference(resolution,[],[f293,f67])).

fof(f67,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK0)
        | k1_funct_1(sK1,X2) = X2 )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f293,plain,
    ( r2_hidden(sK3(sK0,sK1),sK0)
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f292])).

fof(f392,plain,
    ( spl5_3
    | spl5_41
    | ~ spl5_35
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f389,f307,f277,f315,f47])).

fof(f47,plain,
    ( spl5_3
  <=> sK1 = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f315,plain,
    ( spl5_41
  <=> sK3(sK0,sK1) = sK4(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f307,plain,
    ( spl5_40
  <=> ! [X5] :
        ( sK3(X5,sK1) = sK4(X5,sK1)
        | k1_funct_1(sK1,sK3(X5,sK1)) = sK4(X5,sK1)
        | sK1 = k6_relat_1(X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f389,plain,
    ( sK3(sK0,sK1) = sK4(sK0,sK1)
    | sK1 = k6_relat_1(sK0)
    | ~ spl5_35
    | ~ spl5_40 ),
    inference(duplicate_literal_removal,[],[f387])).

fof(f387,plain,
    ( sK3(sK0,sK1) = sK4(sK0,sK1)
    | sK3(sK0,sK1) = sK4(sK0,sK1)
    | sK1 = k6_relat_1(sK0)
    | ~ spl5_35
    | ~ spl5_40 ),
    inference(superposition,[],[f279,f308])).

fof(f308,plain,
    ( ! [X5] :
        ( k1_funct_1(sK1,sK3(X5,sK1)) = sK4(X5,sK1)
        | sK3(X5,sK1) = sK4(X5,sK1)
        | sK1 = k6_relat_1(X5) )
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f307])).

fof(f279,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK1,sK3(sK0,sK1))
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f277])).

fof(f359,plain,
    ( spl5_3
    | ~ spl5_37
    | ~ spl5_2
    | ~ spl5_38
    | ~ spl5_41 ),
    inference(avatar_split_clause,[],[f358,f315,f292,f42,f288,f47])).

fof(f288,plain,
    ( spl5_37
  <=> r2_hidden(k4_tarski(sK3(sK0,sK1),sK3(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f42,plain,
    ( spl5_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f358,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(k4_tarski(sK3(sK0,sK1),sK3(sK0,sK1)),sK1)
    | sK1 = k6_relat_1(sK0)
    | ~ spl5_41 ),
    inference(trivial_inequality_removal,[],[f357])).

fof(f357,plain,
    ( sK3(sK0,sK1) != sK3(sK0,sK1)
    | ~ r2_hidden(sK3(sK0,sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(k4_tarski(sK3(sK0,sK1),sK3(sK0,sK1)),sK1)
    | sK1 = k6_relat_1(sK0)
    | ~ spl5_41 ),
    inference(superposition,[],[f22,f317])).

fof(f317,plain,
    ( sK3(sK0,sK1) = sK4(sK0,sK1)
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f315])).

fof(f22,plain,(
    ! [X0,X1] :
      ( sK3(X0,X1) != sK4(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X0)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

fof(f332,plain,
    ( spl5_3
    | ~ spl5_2
    | spl5_38
    | ~ spl5_12
    | spl5_38 ),
    inference(avatar_split_clause,[],[f328,f292,f98,f292,f42,f47])).

fof(f98,plain,
    ( spl5_12
  <=> ! [X1,X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f328,plain,
    ( r2_hidden(sK3(sK0,sK1),sK0)
    | ~ v1_relat_1(sK1)
    | sK1 = k6_relat_1(sK0)
    | ~ spl5_12
    | spl5_38 ),
    inference(resolution,[],[f311,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
      | r2_hidden(sK3(X0,X1),X0)
      | ~ v1_relat_1(X1)
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f311,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK3(sK0,sK1),X0),sK1)
    | ~ spl5_12
    | spl5_38 ),
    inference(resolution,[],[f294,f99])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f98])).

fof(f294,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),sK0)
    | spl5_38 ),
    inference(avatar_component_clause,[],[f292])).

fof(f309,plain,
    ( ~ spl5_2
    | spl5_40
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f300,f134,f307,f42])).

fof(f300,plain,
    ( ! [X5] :
        ( sK3(X5,sK1) = sK4(X5,sK1)
        | ~ v1_relat_1(sK1)
        | sK1 = k6_relat_1(X5)
        | k1_funct_1(sK1,sK3(X5,sK1)) = sK4(X5,sK1) )
    | ~ spl5_16 ),
    inference(resolution,[],[f24,f135])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
      | sK3(X0,X1) = sK4(X0,X1)
      | ~ v1_relat_1(X1)
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f295,plain,
    ( ~ spl5_2
    | ~ spl5_1
    | spl5_37
    | ~ spl5_38
    | ~ spl5_4
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f286,f277,f51,f292,f288,f37,f42])).

fof(f37,plain,
    ( spl5_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f51,plain,
    ( spl5_4
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f286,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),sK0)
    | r2_hidden(k4_tarski(sK3(sK0,sK1),sK3(sK0,sK1)),sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl5_4
    | ~ spl5_35 ),
    inference(forward_demodulation,[],[f285,f53])).

fof(f53,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f285,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,sK1),sK3(sK0,sK1)),sK1)
    | ~ v1_funct_1(sK1)
    | ~ r2_hidden(sK3(sK0,sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl5_35 ),
    inference(superposition,[],[f35,f279])).

fof(f35,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | k1_funct_1(X2,X0) != X1
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f11])).

% (4093)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f136,plain,
    ( spl5_16
    | ~ spl5_2
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f131,f37,f42,f134])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK1)
        | k1_funct_1(sK1,X0) = X1
        | ~ r2_hidden(k4_tarski(X0,X1),sK1) )
    | ~ spl5_1 ),
    inference(resolution,[],[f29,f39])).

fof(f39,plain,
    ( v1_funct_1(sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f127,plain,
    ( spl5_4
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f115,f47,f51])).

fof(f115,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl5_3 ),
    inference(superposition,[],[f20,f49])).

fof(f49,plain,
    ( sK1 = k6_relat_1(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f20,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f121,plain,
    ( ~ spl5_2
    | spl5_14
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f113,f47,f119,f42])).

fof(f113,plain,
    ( ! [X2] :
        ( r2_hidden(k4_tarski(X2,X2),sK1)
        | ~ r2_hidden(X2,sK0)
        | ~ v1_relat_1(sK1) )
    | ~ spl5_3 ),
    inference(superposition,[],[f32,f49])).

fof(f32,plain,(
    ! [X0,X3] :
      ( r2_hidden(k4_tarski(X3,X3),k6_relat_1(X0))
      | ~ r2_hidden(X3,X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(k4_tarski(X3,X3),X1)
      | k6_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,X0)
      | X2 != X3
      | r2_hidden(k4_tarski(X2,X3),X1)
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f100,plain,
    ( ~ spl5_2
    | ~ spl5_1
    | spl5_12
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f95,f51,f98,f37,f42])).

fof(f95,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK0)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1) )
    | ~ spl5_4 ),
    inference(superposition,[],[f28,f53])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f68,plain,
    ( spl5_3
    | spl5_7 ),
    inference(avatar_split_clause,[],[f12,f66,f47])).

fof(f12,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | k1_funct_1(sK1,X2) = X2
      | sK1 = k6_relat_1(sK0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <~> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <~> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k6_relat_1(X0) = X1
        <=> ( ! [X2] :
                ( r2_hidden(X2,X0)
               => k1_funct_1(X1,X2) = X2 )
            & k1_relat_1(X1) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(f64,plain,
    ( ~ spl5_3
    | spl5_6
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f13,f51,f61,f47])).

fof(f13,plain,
    ( sK0 != k1_relat_1(sK1)
    | r2_hidden(sK2,sK0)
    | sK1 != k6_relat_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f59,plain,
    ( ~ spl5_3
    | ~ spl5_5
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f14,f51,f56,f47])).

fof(f14,plain,
    ( sK0 != k1_relat_1(sK1)
    | sK2 != k1_funct_1(sK1,sK2)
    | sK1 != k6_relat_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f54,plain,
    ( spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f15,f51,f47])).

fof(f15,plain,
    ( sK0 = k1_relat_1(sK1)
    | sK1 = k6_relat_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f45,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f16,f42])).

fof(f16,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f40,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f17,f37])).

fof(f17,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:16:49 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.44  % (4113)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.45  % (4104)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.47  % (4094)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.47  % (4101)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.47  % (4096)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.48  % (4096)Refutation not found, incomplete strategy% (4096)------------------------------
% 0.20/0.48  % (4096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (4096)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (4096)Memory used [KB]: 1663
% 0.20/0.48  % (4096)Time elapsed: 0.073 s
% 0.20/0.48  % (4096)------------------------------
% 0.20/0.48  % (4096)------------------------------
% 0.20/0.49  % (4110)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.49  % (4111)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.49  % (4104)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f477,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f40,f45,f54,f59,f64,f68,f100,f121,f127,f136,f295,f309,f332,f359,f392,f396,f476])).
% 0.20/0.49  fof(f476,plain,(
% 0.20/0.49    spl5_5 | ~spl5_6 | ~spl5_14 | ~spl5_16),
% 0.20/0.49    inference(avatar_split_clause,[],[f468,f134,f119,f61,f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    spl5_5 <=> sK2 = k1_funct_1(sK1,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    spl5_6 <=> r2_hidden(sK2,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.49  fof(f119,plain,(
% 0.20/0.49    spl5_14 <=> ! [X2] : (r2_hidden(k4_tarski(X2,X2),sK1) | ~r2_hidden(X2,sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.49  fof(f134,plain,(
% 0.20/0.49    spl5_16 <=> ! [X1,X0] : (k1_funct_1(sK1,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.49  fof(f468,plain,(
% 0.20/0.49    sK2 = k1_funct_1(sK1,sK2) | (~spl5_6 | ~spl5_14 | ~spl5_16)),
% 0.20/0.49    inference(resolution,[],[f439,f63])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    r2_hidden(sK2,sK0) | ~spl5_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f61])).
% 0.20/0.49  fof(f439,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(sK1,X0) = X0) ) | (~spl5_14 | ~spl5_16)),
% 0.20/0.49    inference(resolution,[],[f120,f135])).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | k1_funct_1(sK1,X0) = X1) ) | ~spl5_16),
% 0.20/0.49    inference(avatar_component_clause,[],[f134])).
% 0.20/0.49  fof(f120,plain,(
% 0.20/0.49    ( ! [X2] : (r2_hidden(k4_tarski(X2,X2),sK1) | ~r2_hidden(X2,sK0)) ) | ~spl5_14),
% 0.20/0.49    inference(avatar_component_clause,[],[f119])).
% 0.20/0.49  fof(f396,plain,(
% 0.20/0.49    spl5_35 | ~spl5_7 | ~spl5_38),
% 0.20/0.49    inference(avatar_split_clause,[],[f338,f292,f66,f277])).
% 0.20/0.49  fof(f277,plain,(
% 0.20/0.49    spl5_35 <=> sK3(sK0,sK1) = k1_funct_1(sK1,sK3(sK0,sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    spl5_7 <=> ! [X2] : (~r2_hidden(X2,sK0) | k1_funct_1(sK1,X2) = X2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.49  fof(f292,plain,(
% 0.20/0.49    spl5_38 <=> r2_hidden(sK3(sK0,sK1),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 0.20/0.49  fof(f338,plain,(
% 0.20/0.49    sK3(sK0,sK1) = k1_funct_1(sK1,sK3(sK0,sK1)) | (~spl5_7 | ~spl5_38)),
% 0.20/0.49    inference(resolution,[],[f293,f67])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    ( ! [X2] : (~r2_hidden(X2,sK0) | k1_funct_1(sK1,X2) = X2) ) | ~spl5_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f66])).
% 0.20/0.49  fof(f293,plain,(
% 0.20/0.49    r2_hidden(sK3(sK0,sK1),sK0) | ~spl5_38),
% 0.20/0.49    inference(avatar_component_clause,[],[f292])).
% 0.20/0.49  fof(f392,plain,(
% 0.20/0.49    spl5_3 | spl5_41 | ~spl5_35 | ~spl5_40),
% 0.20/0.49    inference(avatar_split_clause,[],[f389,f307,f277,f315,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    spl5_3 <=> sK1 = k6_relat_1(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.49  fof(f315,plain,(
% 0.20/0.49    spl5_41 <=> sK3(sK0,sK1) = sK4(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 0.20/0.49  fof(f307,plain,(
% 0.20/0.49    spl5_40 <=> ! [X5] : (sK3(X5,sK1) = sK4(X5,sK1) | k1_funct_1(sK1,sK3(X5,sK1)) = sK4(X5,sK1) | sK1 = k6_relat_1(X5))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 0.20/0.49  fof(f389,plain,(
% 0.20/0.49    sK3(sK0,sK1) = sK4(sK0,sK1) | sK1 = k6_relat_1(sK0) | (~spl5_35 | ~spl5_40)),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f387])).
% 0.20/0.49  fof(f387,plain,(
% 0.20/0.49    sK3(sK0,sK1) = sK4(sK0,sK1) | sK3(sK0,sK1) = sK4(sK0,sK1) | sK1 = k6_relat_1(sK0) | (~spl5_35 | ~spl5_40)),
% 0.20/0.49    inference(superposition,[],[f279,f308])).
% 0.20/0.49  fof(f308,plain,(
% 0.20/0.49    ( ! [X5] : (k1_funct_1(sK1,sK3(X5,sK1)) = sK4(X5,sK1) | sK3(X5,sK1) = sK4(X5,sK1) | sK1 = k6_relat_1(X5)) ) | ~spl5_40),
% 0.20/0.49    inference(avatar_component_clause,[],[f307])).
% 0.20/0.49  fof(f279,plain,(
% 0.20/0.49    sK3(sK0,sK1) = k1_funct_1(sK1,sK3(sK0,sK1)) | ~spl5_35),
% 0.20/0.49    inference(avatar_component_clause,[],[f277])).
% 0.20/0.49  fof(f359,plain,(
% 0.20/0.49    spl5_3 | ~spl5_37 | ~spl5_2 | ~spl5_38 | ~spl5_41),
% 0.20/0.49    inference(avatar_split_clause,[],[f358,f315,f292,f42,f288,f47])).
% 0.20/0.49  fof(f288,plain,(
% 0.20/0.49    spl5_37 <=> r2_hidden(k4_tarski(sK3(sK0,sK1),sK3(sK0,sK1)),sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    spl5_2 <=> v1_relat_1(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.49  fof(f358,plain,(
% 0.20/0.49    ~r2_hidden(sK3(sK0,sK1),sK0) | ~v1_relat_1(sK1) | ~r2_hidden(k4_tarski(sK3(sK0,sK1),sK3(sK0,sK1)),sK1) | sK1 = k6_relat_1(sK0) | ~spl5_41),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f357])).
% 0.20/0.49  fof(f357,plain,(
% 0.20/0.49    sK3(sK0,sK1) != sK3(sK0,sK1) | ~r2_hidden(sK3(sK0,sK1),sK0) | ~v1_relat_1(sK1) | ~r2_hidden(k4_tarski(sK3(sK0,sK1),sK3(sK0,sK1)),sK1) | sK1 = k6_relat_1(sK0) | ~spl5_41),
% 0.20/0.49    inference(superposition,[],[f22,f317])).
% 0.20/0.49  fof(f317,plain,(
% 0.20/0.49    sK3(sK0,sK1) = sK4(sK0,sK1) | ~spl5_41),
% 0.20/0.49    inference(avatar_component_clause,[],[f315])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ( ! [X0,X1] : (sK3(X0,X1) != sK4(X0,X1) | ~r2_hidden(sK3(X0,X1),X0) | ~v1_relat_1(X1) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) | k6_relat_1(X0) = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => (k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).
% 0.20/0.49  fof(f332,plain,(
% 0.20/0.49    spl5_3 | ~spl5_2 | spl5_38 | ~spl5_12 | spl5_38),
% 0.20/0.49    inference(avatar_split_clause,[],[f328,f292,f98,f292,f42,f47])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    spl5_12 <=> ! [X1,X0] : (r2_hidden(X0,sK0) | ~r2_hidden(k4_tarski(X0,X1),sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.49  fof(f328,plain,(
% 0.20/0.49    r2_hidden(sK3(sK0,sK1),sK0) | ~v1_relat_1(sK1) | sK1 = k6_relat_1(sK0) | (~spl5_12 | spl5_38)),
% 0.20/0.49    inference(resolution,[],[f311,f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) | r2_hidden(sK3(X0,X1),X0) | ~v1_relat_1(X1) | k6_relat_1(X0) = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f311,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(k4_tarski(sK3(sK0,sK1),X0),sK1)) ) | (~spl5_12 | spl5_38)),
% 0.20/0.49    inference(resolution,[],[f294,f99])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(X0,sK0) | ~r2_hidden(k4_tarski(X0,X1),sK1)) ) | ~spl5_12),
% 0.20/0.49    inference(avatar_component_clause,[],[f98])).
% 0.20/0.49  fof(f294,plain,(
% 0.20/0.49    ~r2_hidden(sK3(sK0,sK1),sK0) | spl5_38),
% 0.20/0.49    inference(avatar_component_clause,[],[f292])).
% 0.20/0.49  fof(f309,plain,(
% 0.20/0.49    ~spl5_2 | spl5_40 | ~spl5_16),
% 0.20/0.49    inference(avatar_split_clause,[],[f300,f134,f307,f42])).
% 0.20/0.49  fof(f300,plain,(
% 0.20/0.49    ( ! [X5] : (sK3(X5,sK1) = sK4(X5,sK1) | ~v1_relat_1(sK1) | sK1 = k6_relat_1(X5) | k1_funct_1(sK1,sK3(X5,sK1)) = sK4(X5,sK1)) ) | ~spl5_16),
% 0.20/0.49    inference(resolution,[],[f24,f135])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) | sK3(X0,X1) = sK4(X0,X1) | ~v1_relat_1(X1) | k6_relat_1(X0) = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f295,plain,(
% 0.20/0.49    ~spl5_2 | ~spl5_1 | spl5_37 | ~spl5_38 | ~spl5_4 | ~spl5_35),
% 0.20/0.49    inference(avatar_split_clause,[],[f286,f277,f51,f292,f288,f37,f42])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    spl5_1 <=> v1_funct_1(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    spl5_4 <=> sK0 = k1_relat_1(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.49  fof(f286,plain,(
% 0.20/0.49    ~r2_hidden(sK3(sK0,sK1),sK0) | r2_hidden(k4_tarski(sK3(sK0,sK1),sK3(sK0,sK1)),sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl5_4 | ~spl5_35)),
% 0.20/0.49    inference(forward_demodulation,[],[f285,f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    sK0 = k1_relat_1(sK1) | ~spl5_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f51])).
% 0.20/0.49  fof(f285,plain,(
% 0.20/0.49    r2_hidden(k4_tarski(sK3(sK0,sK1),sK3(sK0,sK1)),sK1) | ~v1_funct_1(sK1) | ~r2_hidden(sK3(sK0,sK1),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~spl5_35),
% 0.20/0.49    inference(superposition,[],[f35,f279])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.20/0.49    inference(equality_resolution,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | k1_funct_1(X2,X0) != X1 | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  % (4093)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.49    inference(flattening,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.20/0.49  fof(f136,plain,(
% 0.20/0.49    spl5_16 | ~spl5_2 | ~spl5_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f131,f37,f42,f134])).
% 0.20/0.49  fof(f131,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(sK1) | k1_funct_1(sK1,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),sK1)) ) | ~spl5_1),
% 0.20/0.49    inference(resolution,[],[f29,f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    v1_funct_1(sK1) | ~spl5_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f37])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    spl5_4 | ~spl5_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f115,f47,f51])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    sK0 = k1_relat_1(sK1) | ~spl5_3),
% 0.20/0.49    inference(superposition,[],[f20,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    sK1 = k6_relat_1(sK0) | ~spl5_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f47])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    ~spl5_2 | spl5_14 | ~spl5_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f113,f47,f119,f42])).
% 0.20/0.49  fof(f113,plain,(
% 0.20/0.49    ( ! [X2] : (r2_hidden(k4_tarski(X2,X2),sK1) | ~r2_hidden(X2,sK0) | ~v1_relat_1(sK1)) ) | ~spl5_3),
% 0.20/0.49    inference(superposition,[],[f32,f49])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X0,X3] : (r2_hidden(k4_tarski(X3,X3),k6_relat_1(X0)) | ~r2_hidden(X3,X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.49    inference(equality_resolution,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X0,X3,X1] : (~v1_relat_1(X1) | ~r2_hidden(X3,X0) | r2_hidden(k4_tarski(X3,X3),X1) | k6_relat_1(X0) != X1) )),
% 0.20/0.49    inference(equality_resolution,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X1) | ~r2_hidden(X2,X0) | X2 != X3 | r2_hidden(k4_tarski(X2,X3),X1) | k6_relat_1(X0) != X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    ~spl5_2 | ~spl5_1 | spl5_12 | ~spl5_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f95,f51,f98,f37,f42])).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(X0,sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(k4_tarski(X0,X1),sK1)) ) | ~spl5_4),
% 0.20/0.49    inference(superposition,[],[f28,f53])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    spl5_3 | spl5_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f12,f66,f47])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ( ! [X2] : (~r2_hidden(X2,sK0) | k1_funct_1(sK1,X2) = X2 | sK1 = k6_relat_1(sK0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,plain,(
% 0.20/0.49    ? [X0,X1] : ((k6_relat_1(X0) = X1 <~> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f7])).
% 0.20/0.49  fof(f7,plain,(
% 0.20/0.49    ? [X0,X1] : ((k6_relat_1(X0) = X1 <~> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.20/0.49    inference(negated_conjecture,[],[f5])).
% 0.20/0.49  fof(f5,conjecture,(
% 0.20/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ~spl5_3 | spl5_6 | ~spl5_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f13,f51,f61,f47])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    sK0 != k1_relat_1(sK1) | r2_hidden(sK2,sK0) | sK1 != k6_relat_1(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ~spl5_3 | ~spl5_5 | ~spl5_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f14,f51,f56,f47])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    sK0 != k1_relat_1(sK1) | sK2 != k1_funct_1(sK1,sK2) | sK1 != k6_relat_1(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    spl5_3 | spl5_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f15,f51,f47])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    sK0 = k1_relat_1(sK1) | sK1 = k6_relat_1(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    spl5_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f16,f42])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    v1_relat_1(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    spl5_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f17,f37])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    v1_funct_1(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (4104)------------------------------
% 0.20/0.49  % (4104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (4104)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (4104)Memory used [KB]: 6396
% 0.20/0.49  % (4104)Time elapsed: 0.077 s
% 0.20/0.49  % (4104)------------------------------
% 0.20/0.49  % (4104)------------------------------
% 0.20/0.49  % (4086)Success in time 0.149 s
%------------------------------------------------------------------------------
