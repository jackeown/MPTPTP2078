%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 189 expanded)
%              Number of leaves         :   16 (  65 expanded)
%              Depth                    :   10
%              Number of atoms          :  291 ( 593 expanded)
%              Number of equality atoms :   19 (  33 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f331,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f65,f76,f81,f95,f119,f156,f249,f286,f311,f330])).

fof(f330,plain,
    ( ~ spl12_1
    | ~ spl12_2
    | spl12_6
    | ~ spl12_22 ),
    inference(avatar_contradiction_clause,[],[f329])).

fof(f329,plain,
    ( $false
    | ~ spl12_1
    | ~ spl12_2
    | spl12_6
    | ~ spl12_22 ),
    inference(subsumption_resolution,[],[f328,f94])).

fof(f94,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1)))
    | spl12_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl12_6
  <=> r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f328,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_22 ),
    inference(subsumption_resolution,[],[f327,f67])).

fof(f67,plain,
    ( ! [X2] : v1_relat_1(k7_relat_1(sK2,X2))
    | ~ spl12_1 ),
    inference(resolution,[],[f60,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f60,plain,
    ( v1_relat_1(sK2)
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl12_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f327,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_22 ),
    inference(subsumption_resolution,[],[f326,f71])).

fof(f71,plain,
    ( ! [X1] : v1_funct_1(k7_relat_1(sK2,X1))
    | ~ spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f69,f60])).

fof(f69,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(sK2)
        | v1_funct_1(k7_relat_1(sK2,X1)) )
    | ~ spl12_2 ),
    inference(resolution,[],[f64,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f64,plain,
    ( v1_funct_1(sK2)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl12_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f326,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl12_22 ),
    inference(resolution,[],[f310,f51])).

fof(f51,plain,(
    ! [X2,X0] :
      ( ~ sP4(X2,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP4(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f310,plain,
    ( sP4(k1_funct_1(sK2,sK0),k7_relat_1(sK2,sK1))
    | ~ spl12_22 ),
    inference(avatar_component_clause,[],[f309])).

fof(f309,plain,
    ( spl12_22
  <=> sP4(k1_funct_1(sK2,sK0),k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_22])])).

fof(f311,plain,
    ( spl12_22
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_19
    | ~ spl12_21 ),
    inference(avatar_split_clause,[],[f299,f284,f247,f63,f59,f309])).

fof(f247,plain,
    ( spl12_19
  <=> r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_19])])).

fof(f284,plain,
    ( spl12_21
  <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_21])])).

fof(f299,plain,
    ( sP4(k1_funct_1(sK2,sK0),k7_relat_1(sK2,sK1))
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_19
    | ~ spl12_21 ),
    inference(forward_demodulation,[],[f294,f271])).

fof(f271,plain,
    ( k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_19 ),
    inference(subsumption_resolution,[],[f270,f67])).

fof(f270,plain,
    ( k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_19 ),
    inference(subsumption_resolution,[],[f266,f71])).

fof(f266,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,sK1))
    | k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ spl12_19 ),
    inference(resolution,[],[f248,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f248,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k7_relat_1(sK2,sK1))
    | ~ spl12_19 ),
    inference(avatar_component_clause,[],[f247])).

fof(f294,plain,
    ( sP4(k1_funct_1(k7_relat_1(sK2,sK1),sK0),k7_relat_1(sK2,sK1))
    | ~ spl12_21 ),
    inference(resolution,[],[f285,f52])).

fof(f52,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | sP4(k1_funct_1(X0,X3),X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | sP4(X2,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f285,plain,
    ( r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl12_21 ),
    inference(avatar_component_clause,[],[f284])).

fof(f286,plain,
    ( spl12_21
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_19 ),
    inference(avatar_split_clause,[],[f269,f247,f63,f59,f284])).

fof(f269,plain,
    ( r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_19 ),
    inference(subsumption_resolution,[],[f268,f67])).

fof(f268,plain,
    ( r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_19 ),
    inference(subsumption_resolution,[],[f265,f71])).

fof(f265,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,sK1))
    | r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ spl12_19 ),
    inference(resolution,[],[f248,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f249,plain,
    ( spl12_19
    | ~ spl12_1
    | ~ spl12_11 ),
    inference(avatar_split_clause,[],[f175,f154,f59,f247])).

fof(f154,plain,
    ( spl12_11
  <=> sP8(k1_funct_1(sK2,sK0),sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).

fof(f175,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k7_relat_1(sK2,sK1))
    | ~ spl12_1
    | ~ spl12_11 ),
    inference(subsumption_resolution,[],[f174,f60])).

% (23466)Refutation not found, incomplete strategy% (23466)------------------------------
% (23466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23466)Termination reason: Refutation not found, incomplete strategy

% (23466)Memory used [KB]: 10618
% (23466)Time elapsed: 0.073 s
% (23466)------------------------------
% (23466)------------------------------
fof(f174,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k7_relat_1(sK2,sK1))
    | ~ spl12_1
    | ~ spl12_11 ),
    inference(subsumption_resolution,[],[f173,f67])).

fof(f173,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k7_relat_1(sK2,sK1))
    | ~ spl12_11 ),
    inference(resolution,[],[f155,f54])).

fof(f54,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ sP8(X4,X3,X1,X0)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | ~ sP8(X4,X3,X1,X0)
      | r2_hidden(k4_tarski(X3,X4),X2)
      | k7_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

fof(f155,plain,
    ( sP8(k1_funct_1(sK2,sK0),sK0,sK1,sK2)
    | ~ spl12_11 ),
    inference(avatar_component_clause,[],[f154])).

fof(f156,plain,
    ( spl12_11
    | ~ spl12_3
    | ~ spl12_8 ),
    inference(avatar_split_clause,[],[f133,f117,f74,f154])).

fof(f74,plain,
    ( spl12_3
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f117,plain,
    ( spl12_8
  <=> r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f133,plain,
    ( sP8(k1_funct_1(sK2,sK0),sK0,sK1,sK2)
    | ~ spl12_3
    | ~ spl12_8 ),
    inference(resolution,[],[f77,f118])).

fof(f118,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f117])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(sK0,X0),X1)
        | sP8(X0,sK0,sK1,X1) )
    | ~ spl12_3 ),
    inference(resolution,[],[f75,f34])).

fof(f34,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | sP8(X4,X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f75,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f119,plain,
    ( spl12_8
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f87,f79,f63,f59,f117])).

fof(f79,plain,
    ( spl12_4
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f87,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f86,f60])).

fof(f86,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f83,f64])).

fof(f83,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ spl12_4 ),
    inference(resolution,[],[f80,f55])).

fof(f55,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | k1_funct_1(X2,X0) != X1
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f80,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f95,plain,(
    ~ spl12_6 ),
    inference(avatar_split_clause,[],[f23,f93])).

fof(f23,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))
      & r2_hidden(X0,X1)
      & r2_hidden(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))
      & r2_hidden(X0,X1)
      & r2_hidden(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r2_hidden(X0,X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
         => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X0,X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
       => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_1)).

fof(f81,plain,(
    spl12_4 ),
    inference(avatar_split_clause,[],[f21,f79])).

fof(f21,plain,(
    r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f76,plain,(
    spl12_3 ),
    inference(avatar_split_clause,[],[f22,f74])).

fof(f22,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f65,plain,(
    spl12_2 ),
    inference(avatar_split_clause,[],[f20,f63])).

fof(f20,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f61,plain,(
    spl12_1 ),
    inference(avatar_split_clause,[],[f19,f59])).

fof(f19,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n020.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 12:12:52 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.20/0.40  % (23470)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.42  % (23479)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.46  % (23467)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.46  % (23465)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.46  % (23480)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.47  % (23473)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.47  % (23465)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (23477)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (23468)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (23485)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (23475)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.47  % (23485)Refutation not found, incomplete strategy% (23485)------------------------------
% 0.20/0.47  % (23485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (23485)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (23485)Memory used [KB]: 10618
% 0.20/0.47  % (23485)Time elapsed: 0.081 s
% 0.20/0.47  % (23485)------------------------------
% 0.20/0.47  % (23485)------------------------------
% 0.20/0.47  % (23472)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (23466)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f331,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f61,f65,f76,f81,f95,f119,f156,f249,f286,f311,f330])).
% 0.20/0.48  fof(f330,plain,(
% 0.20/0.48    ~spl12_1 | ~spl12_2 | spl12_6 | ~spl12_22),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f329])).
% 0.20/0.48  fof(f329,plain,(
% 0.20/0.48    $false | (~spl12_1 | ~spl12_2 | spl12_6 | ~spl12_22)),
% 0.20/0.48    inference(subsumption_resolution,[],[f328,f94])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    ~r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1))) | spl12_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f93])).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    spl12_6 <=> r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).
% 0.20/0.48  fof(f328,plain,(
% 0.20/0.48    r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1))) | (~spl12_1 | ~spl12_2 | ~spl12_22)),
% 0.20/0.48    inference(subsumption_resolution,[],[f327,f67])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    ( ! [X2] : (v1_relat_1(k7_relat_1(sK2,X2))) ) | ~spl12_1),
% 0.20/0.48    inference(resolution,[],[f60,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    v1_relat_1(sK2) | ~spl12_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f59])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    spl12_1 <=> v1_relat_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 0.20/0.48  fof(f327,plain,(
% 0.20/0.48    ~v1_relat_1(k7_relat_1(sK2,sK1)) | r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1))) | (~spl12_1 | ~spl12_2 | ~spl12_22)),
% 0.20/0.48    inference(subsumption_resolution,[],[f326,f71])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    ( ! [X1] : (v1_funct_1(k7_relat_1(sK2,X1))) ) | (~spl12_1 | ~spl12_2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f69,f60])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    ( ! [X1] : (~v1_relat_1(sK2) | v1_funct_1(k7_relat_1(sK2,X1))) ) | ~spl12_2),
% 0.20/0.48    inference(resolution,[],[f64,f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k7_relat_1(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    v1_funct_1(sK2) | ~spl12_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f63])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    spl12_2 <=> v1_funct_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 0.20/0.48  fof(f326,plain,(
% 0.20/0.48    ~v1_funct_1(k7_relat_1(sK2,sK1)) | ~v1_relat_1(k7_relat_1(sK2,sK1)) | r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1))) | ~spl12_22),
% 0.20/0.48    inference(resolution,[],[f310,f51])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ( ! [X2,X0] : (~sP4(X2,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 0.20/0.48    inference(equality_resolution,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~sP4(X2,X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.20/0.48  fof(f310,plain,(
% 0.20/0.48    sP4(k1_funct_1(sK2,sK0),k7_relat_1(sK2,sK1)) | ~spl12_22),
% 0.20/0.48    inference(avatar_component_clause,[],[f309])).
% 0.20/0.48  fof(f309,plain,(
% 0.20/0.48    spl12_22 <=> sP4(k1_funct_1(sK2,sK0),k7_relat_1(sK2,sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_22])])).
% 0.20/0.48  fof(f311,plain,(
% 0.20/0.48    spl12_22 | ~spl12_1 | ~spl12_2 | ~spl12_19 | ~spl12_21),
% 0.20/0.48    inference(avatar_split_clause,[],[f299,f284,f247,f63,f59,f309])).
% 0.20/0.48  fof(f247,plain,(
% 0.20/0.48    spl12_19 <=> r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k7_relat_1(sK2,sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_19])])).
% 0.20/0.48  fof(f284,plain,(
% 0.20/0.48    spl12_21 <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_21])])).
% 0.20/0.48  fof(f299,plain,(
% 0.20/0.48    sP4(k1_funct_1(sK2,sK0),k7_relat_1(sK2,sK1)) | (~spl12_1 | ~spl12_2 | ~spl12_19 | ~spl12_21)),
% 0.20/0.48    inference(forward_demodulation,[],[f294,f271])).
% 0.20/0.48  fof(f271,plain,(
% 0.20/0.48    k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0) | (~spl12_1 | ~spl12_2 | ~spl12_19)),
% 0.20/0.48    inference(subsumption_resolution,[],[f270,f67])).
% 0.20/0.48  fof(f270,plain,(
% 0.20/0.48    k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0) | ~v1_relat_1(k7_relat_1(sK2,sK1)) | (~spl12_1 | ~spl12_2 | ~spl12_19)),
% 0.20/0.48    inference(subsumption_resolution,[],[f266,f71])).
% 0.20/0.48  fof(f266,plain,(
% 0.20/0.48    ~v1_funct_1(k7_relat_1(sK2,sK1)) | k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0) | ~v1_relat_1(k7_relat_1(sK2,sK1)) | ~spl12_19),
% 0.20/0.48    inference(resolution,[],[f248,f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(flattening,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.20/0.48  fof(f248,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k7_relat_1(sK2,sK1)) | ~spl12_19),
% 0.20/0.48    inference(avatar_component_clause,[],[f247])).
% 0.20/0.48  fof(f294,plain,(
% 0.20/0.48    sP4(k1_funct_1(k7_relat_1(sK2,sK1),sK0),k7_relat_1(sK2,sK1)) | ~spl12_21),
% 0.20/0.48    inference(resolution,[],[f285,f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X0,X3] : (~r2_hidden(X3,k1_relat_1(X0)) | sP4(k1_funct_1(X0,X3),X0)) )),
% 0.20/0.48    inference(equality_resolution,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ( ! [X2,X0,X3] : (~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | sP4(X2,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f285,plain,(
% 0.20/0.48    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) | ~spl12_21),
% 0.20/0.48    inference(avatar_component_clause,[],[f284])).
% 0.20/0.48  fof(f286,plain,(
% 0.20/0.48    spl12_21 | ~spl12_1 | ~spl12_2 | ~spl12_19),
% 0.20/0.48    inference(avatar_split_clause,[],[f269,f247,f63,f59,f284])).
% 0.20/0.48  fof(f269,plain,(
% 0.20/0.48    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) | (~spl12_1 | ~spl12_2 | ~spl12_19)),
% 0.20/0.48    inference(subsumption_resolution,[],[f268,f67])).
% 0.20/0.48  fof(f268,plain,(
% 0.20/0.48    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) | ~v1_relat_1(k7_relat_1(sK2,sK1)) | (~spl12_1 | ~spl12_2 | ~spl12_19)),
% 0.20/0.48    inference(subsumption_resolution,[],[f265,f71])).
% 0.20/0.48  fof(f265,plain,(
% 0.20/0.48    ~v1_funct_1(k7_relat_1(sK2,sK1)) | r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) | ~v1_relat_1(k7_relat_1(sK2,sK1)) | ~spl12_19),
% 0.20/0.48    inference(resolution,[],[f248,f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f249,plain,(
% 0.20/0.48    spl12_19 | ~spl12_1 | ~spl12_11),
% 0.20/0.48    inference(avatar_split_clause,[],[f175,f154,f59,f247])).
% 0.20/0.48  fof(f154,plain,(
% 0.20/0.48    spl12_11 <=> sP8(k1_funct_1(sK2,sK0),sK0,sK1,sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).
% 0.20/0.48  fof(f175,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k7_relat_1(sK2,sK1)) | (~spl12_1 | ~spl12_11)),
% 0.20/0.48    inference(subsumption_resolution,[],[f174,f60])).
% 0.20/0.48  % (23466)Refutation not found, incomplete strategy% (23466)------------------------------
% 0.20/0.48  % (23466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (23466)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (23466)Memory used [KB]: 10618
% 0.20/0.48  % (23466)Time elapsed: 0.073 s
% 0.20/0.48  % (23466)------------------------------
% 0.20/0.48  % (23466)------------------------------
% 0.20/0.48  fof(f174,plain,(
% 0.20/0.48    ~v1_relat_1(sK2) | r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k7_relat_1(sK2,sK1)) | (~spl12_1 | ~spl12_11)),
% 0.20/0.48    inference(subsumption_resolution,[],[f173,f67])).
% 0.20/0.48  fof(f173,plain,(
% 0.20/0.48    ~v1_relat_1(k7_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k7_relat_1(sK2,sK1)) | ~spl12_11),
% 0.20/0.48    inference(resolution,[],[f155,f54])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    ( ! [X4,X0,X3,X1] : (~sP8(X4,X3,X1,X0) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1))) )),
% 0.20/0.48    inference(equality_resolution,[],[f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X2) | ~sP8(X4,X3,X1,X0) | r2_hidden(k4_tarski(X3,X4),X2) | k7_relat_1(X0,X1) != X2) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0] : (! [X1,X2] : ((k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (v1_relat_1(X2) => (k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).
% 0.20/0.48  fof(f155,plain,(
% 0.20/0.48    sP8(k1_funct_1(sK2,sK0),sK0,sK1,sK2) | ~spl12_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f154])).
% 0.20/0.48  fof(f156,plain,(
% 0.20/0.48    spl12_11 | ~spl12_3 | ~spl12_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f133,f117,f74,f154])).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    spl12_3 <=> r2_hidden(sK0,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 0.20/0.48  fof(f117,plain,(
% 0.20/0.48    spl12_8 <=> r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).
% 0.20/0.48  fof(f133,plain,(
% 0.20/0.48    sP8(k1_funct_1(sK2,sK0),sK0,sK1,sK2) | (~spl12_3 | ~spl12_8)),
% 0.20/0.48    inference(resolution,[],[f77,f118])).
% 0.20/0.48  fof(f118,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) | ~spl12_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f117])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK0,X0),X1) | sP8(X0,sK0,sK1,X1)) ) | ~spl12_3),
% 0.20/0.48    inference(resolution,[],[f75,f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X4,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X0) | sP8(X4,X3,X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    r2_hidden(sK0,sK1) | ~spl12_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f74])).
% 0.20/0.48  fof(f119,plain,(
% 0.20/0.48    spl12_8 | ~spl12_1 | ~spl12_2 | ~spl12_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f87,f79,f63,f59,f117])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    spl12_4 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) | (~spl12_1 | ~spl12_2 | ~spl12_4)),
% 0.20/0.48    inference(subsumption_resolution,[],[f86,f60])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    ~v1_relat_1(sK2) | r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) | (~spl12_2 | ~spl12_4)),
% 0.20/0.48    inference(subsumption_resolution,[],[f83,f64])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) | ~spl12_4),
% 0.20/0.48    inference(resolution,[],[f80,f55])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ( ! [X2,X0] : (~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)) )),
% 0.20/0.48    inference(equality_resolution,[],[f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | k1_funct_1(X2,X0) != X1 | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl12_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f79])).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    ~spl12_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f23,f93])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ~r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1)))),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) & r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.48    inference(flattening,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) & (r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2))) => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))))),
% 0.20/0.48    inference(negated_conjecture,[],[f7])).
% 0.20/0.48  fof(f7,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2))) => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_1)).
% 0.20/0.48  fof(f81,plain,(
% 0.20/0.48    spl12_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f21,f79])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    r2_hidden(sK0,k1_relat_1(sK2))),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    spl12_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f22,f74])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    r2_hidden(sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    spl12_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f20,f63])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    v1_funct_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    spl12_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f19,f59])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    v1_relat_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (23465)------------------------------
% 0.20/0.48  % (23465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (23465)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (23465)Memory used [KB]: 6396
% 0.20/0.48  % (23465)Time elapsed: 0.071 s
% 0.20/0.48  % (23465)------------------------------
% 0.20/0.48  % (23465)------------------------------
% 0.20/0.48  % (23461)Success in time 0.136 s
%------------------------------------------------------------------------------
