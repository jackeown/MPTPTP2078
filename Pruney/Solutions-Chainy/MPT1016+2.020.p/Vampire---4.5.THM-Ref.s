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
% DateTime   : Thu Dec  3 13:05:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 375 expanded)
%              Number of leaves         :   18 ( 103 expanded)
%              Depth                    :   12
%              Number of atoms          :  291 (1657 expanded)
%              Number of equality atoms :   48 ( 329 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (13137)Termination reason: Refutation not found, incomplete strategy

% (13137)Memory used [KB]: 10618
% (13137)Time elapsed: 0.124 s
% (13137)------------------------------
% (13137)------------------------------
fof(f323,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f64,f69,f79,f91,f245,f278,f294,f322])).

fof(f322,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_13
    | spl8_14 ),
    inference(avatar_contradiction_clause,[],[f318])).

fof(f318,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_13
    | spl8_14 ),
    inference(unit_resulting_resolution,[],[f68,f315])).

fof(f315,plain,
    ( sK2 = sK3
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_13
    | spl8_14 ),
    inference(backward_demodulation,[],[f314,f312])).

fof(f312,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_13
    | spl8_14 ),
    inference(unit_resulting_resolution,[],[f27,f52,f57,f269,f29,f265,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X3)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

fof(f265,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl8_13
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
        <=> ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).

fof(f269,plain,
    ( k1_xboole_0 != sK0
    | spl8_14 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl8_14
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f57,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl8_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f52,plain,
    ( v2_funct_1(sK1)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl8_1
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f27,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f314,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_13
    | spl8_14 ),
    inference(forward_demodulation,[],[f313,f78])).

fof(f78,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl8_5
  <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f313,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_13
    | spl8_14 ),
    inference(unit_resulting_resolution,[],[f27,f52,f63,f269,f29,f265,f37])).

fof(f63,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl8_3
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f68,plain,
    ( sK2 != sK3
    | spl8_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl8_4
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f294,plain,
    ( ~ spl8_3
    | ~ spl8_14 ),
    inference(avatar_contradiction_clause,[],[f290])).

fof(f290,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_14 ),
    inference(unit_resulting_resolution,[],[f40,f286])).

fof(f286,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_3
    | ~ spl8_14 ),
    inference(backward_demodulation,[],[f94,f270])).

fof(f270,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f268])).

fof(f94,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f63,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f278,plain,(
    spl8_13 ),
    inference(avatar_contradiction_clause,[],[f275])).

fof(f275,plain,
    ( $false
    | spl8_13 ),
    inference(unit_resulting_resolution,[],[f28,f266])).

fof(f266,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | spl8_13 ),
    inference(avatar_component_clause,[],[f264])).

fof(f28,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f245,plain,
    ( spl8_1
    | ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | spl8_1
    | ~ spl8_6 ),
    inference(trivial_inequality_removal,[],[f241])).

fof(f241,plain,
    ( k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,sK4(sK1))
    | spl8_1
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f215,f230])).

fof(f230,plain,
    ( sK4(sK1) = sK5(sK1)
    | spl8_1
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f205,f208,f190,f90])).

fof(f90,plain,
    ( ! [X2,X3] :
        ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3)
        | X2 = X3
        | ~ r2_hidden(X2,sK0)
        | ~ r2_hidden(X3,sK0) )
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl8_6
  <=> ! [X3,X2] :
        ( ~ r2_hidden(X2,sK0)
        | X2 = X3
        | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3)
        | ~ r2_hidden(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f190,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f72,f27,f53,f33])).

fof(f33,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

fof(f53,plain,
    ( ~ v2_funct_1(sK1)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f72,plain,(
    v1_relat_1(sK1) ),
    inference(unit_resulting_resolution,[],[f36,f29,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f36,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f208,plain,
    ( r2_hidden(sK5(sK1),sK0)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f84,f189,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f189,plain,
    ( r2_hidden(sK5(sK1),k1_relat_1(sK1))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f27,f72,f53,f32])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f84,plain,(
    r1_tarski(k1_relat_1(sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f72,f70,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f70,plain,(
    v4_relat_1(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f29,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f205,plain,
    ( r2_hidden(sK4(sK1),sK0)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f84,f188,f41])).

fof(f188,plain,
    ( r2_hidden(sK4(sK1),k1_relat_1(sK1))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f27,f72,f53,f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f215,plain,
    ( k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,sK5(sK1))
    | spl8_1
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f205,f208,f191,f90])).

fof(f191,plain,
    ( sK4(sK1) != sK5(sK1)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f27,f72,f53,f34])).

fof(f34,plain,(
    ! [X0] :
      ( sK4(X0) != sK5(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f91,plain,
    ( spl8_1
    | spl8_6 ),
    inference(avatar_split_clause,[],[f26,f89,f51])).

fof(f26,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(X3,sK0)
      | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3)
      | X2 = X3
      | v2_funct_1(sK1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f79,plain,
    ( ~ spl8_1
    | spl8_5 ),
    inference(avatar_split_clause,[],[f24,f76,f51])).

fof(f24,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f69,plain,
    ( ~ spl8_1
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f25,f66,f51])).

fof(f25,plain,
    ( sK2 != sK3
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f64,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f23,f61,f51])).

fof(f23,plain,
    ( r2_hidden(sK3,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f58,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f22,f55,f51])).

fof(f22,plain,
    ( r2_hidden(sK2,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:21:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (13131)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.50  % (13146)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.50  % (13132)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (13148)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.51  % (13128)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (13153)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (13137)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (13146)Refutation not found, incomplete strategy% (13146)------------------------------
% 0.22/0.52  % (13146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (13146)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (13146)Memory used [KB]: 10618
% 0.22/0.52  % (13146)Time elapsed: 0.114 s
% 0.22/0.52  % (13146)------------------------------
% 0.22/0.52  % (13146)------------------------------
% 0.22/0.52  % (13143)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (13134)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (13128)Refutation not found, incomplete strategy% (13128)------------------------------
% 0.22/0.52  % (13128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (13137)Refutation not found, incomplete strategy% (13137)------------------------------
% 0.22/0.52  % (13137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (13132)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  % (13137)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (13137)Memory used [KB]: 10618
% 0.22/0.52  % (13137)Time elapsed: 0.124 s
% 0.22/0.52  % (13137)------------------------------
% 0.22/0.52  % (13137)------------------------------
% 0.22/0.52  fof(f323,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f58,f64,f69,f79,f91,f245,f278,f294,f322])).
% 0.22/0.52  fof(f322,plain,(
% 0.22/0.52    ~spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_13 | spl8_14),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f318])).
% 0.22/0.52  fof(f318,plain,(
% 0.22/0.52    $false | (~spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_13 | spl8_14)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f68,f315])).
% 0.22/0.52  fof(f315,plain,(
% 0.22/0.52    sK2 = sK3 | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_5 | ~spl8_13 | spl8_14)),
% 0.22/0.52    inference(backward_demodulation,[],[f314,f312])).
% 0.22/0.52  fof(f312,plain,(
% 0.22/0.52    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | (~spl8_1 | ~spl8_2 | ~spl8_13 | spl8_14)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f27,f52,f57,f269,f29,f265,f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X3) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.52    inference(flattening,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).
% 0.22/0.52  fof(f265,plain,(
% 0.22/0.52    v1_funct_2(sK1,sK0,sK0) | ~spl8_13),
% 0.22/0.52    inference(avatar_component_clause,[],[f264])).
% 0.22/0.52  fof(f264,plain,(
% 0.22/0.52    spl8_13 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.52    inference(flattening,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.22/0.52    inference(negated_conjecture,[],[f10])).
% 0.22/0.52  fof(f10,conjecture,(
% 0.22/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).
% 0.22/0.52  fof(f269,plain,(
% 0.22/0.52    k1_xboole_0 != sK0 | spl8_14),
% 0.22/0.52    inference(avatar_component_clause,[],[f268])).
% 0.22/0.52  fof(f268,plain,(
% 0.22/0.52    spl8_14 <=> k1_xboole_0 = sK0),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    r2_hidden(sK2,sK0) | ~spl8_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f55])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    spl8_2 <=> r2_hidden(sK2,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    v2_funct_1(sK1) | ~spl8_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    spl8_1 <=> v2_funct_1(sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    v1_funct_1(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f314,plain,(
% 0.22/0.52    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | (~spl8_1 | ~spl8_3 | ~spl8_5 | ~spl8_13 | spl8_14)),
% 0.22/0.52    inference(forward_demodulation,[],[f313,f78])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~spl8_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f76])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    spl8_5 <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.22/0.52  fof(f313,plain,(
% 0.22/0.52    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | (~spl8_1 | ~spl8_3 | ~spl8_13 | spl8_14)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f27,f52,f63,f269,f29,f265,f37])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    r2_hidden(sK3,sK0) | ~spl8_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f61])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    spl8_3 <=> r2_hidden(sK3,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    sK2 != sK3 | spl8_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f66])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    spl8_4 <=> sK2 = sK3),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.22/0.52  fof(f294,plain,(
% 0.22/0.52    ~spl8_3 | ~spl8_14),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f290])).
% 0.22/0.52  fof(f290,plain,(
% 0.22/0.52    $false | (~spl8_3 | ~spl8_14)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f40,f286])).
% 0.22/0.52  fof(f286,plain,(
% 0.22/0.52    ~v1_xboole_0(k1_xboole_0) | (~spl8_3 | ~spl8_14)),
% 0.22/0.52    inference(backward_demodulation,[],[f94,f270])).
% 0.22/0.52  fof(f270,plain,(
% 0.22/0.52    k1_xboole_0 = sK0 | ~spl8_14),
% 0.22/0.52    inference(avatar_component_clause,[],[f268])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    ~v1_xboole_0(sK0) | ~spl8_3),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f63,f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    v1_xboole_0(k1_xboole_0)),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    v1_xboole_0(k1_xboole_0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.52  fof(f278,plain,(
% 0.22/0.52    spl8_13),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f275])).
% 0.22/0.52  fof(f275,plain,(
% 0.22/0.52    $false | spl8_13),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f28,f266])).
% 0.22/0.52  fof(f266,plain,(
% 0.22/0.52    ~v1_funct_2(sK1,sK0,sK0) | spl8_13),
% 0.22/0.52    inference(avatar_component_clause,[],[f264])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f245,plain,(
% 0.22/0.52    spl8_1 | ~spl8_6),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f244])).
% 0.22/0.52  fof(f244,plain,(
% 0.22/0.52    $false | (spl8_1 | ~spl8_6)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f241])).
% 0.22/0.52  fof(f241,plain,(
% 0.22/0.52    k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,sK4(sK1)) | (spl8_1 | ~spl8_6)),
% 0.22/0.52    inference(backward_demodulation,[],[f215,f230])).
% 0.22/0.52  fof(f230,plain,(
% 0.22/0.52    sK4(sK1) = sK5(sK1) | (spl8_1 | ~spl8_6)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f205,f208,f190,f90])).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    ( ! [X2,X3] : (k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3) | X2 = X3 | ~r2_hidden(X2,sK0) | ~r2_hidden(X3,sK0)) ) | ~spl8_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f89])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    spl8_6 <=> ! [X3,X2] : (~r2_hidden(X2,sK0) | X2 = X3 | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3) | ~r2_hidden(X3,sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.22/0.52  fof(f190,plain,(
% 0.22/0.52    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | spl8_1),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f72,f27,f53,f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X0] : (v2_funct_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ~v2_funct_1(sK1) | spl8_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f51])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    v1_relat_1(sK1)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f36,f29,f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.52  fof(f208,plain,(
% 0.22/0.52    r2_hidden(sK5(sK1),sK0) | spl8_1),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f84,f189,f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.52  fof(f189,plain,(
% 0.22/0.52    r2_hidden(sK5(sK1),k1_relat_1(sK1)) | spl8_1),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f27,f72,f53,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(sK5(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    r1_tarski(k1_relat_1(sK1),sK0)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f72,f70,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    v4_relat_1(sK1,sK0)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f29,f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.52  fof(f205,plain,(
% 0.22/0.52    r2_hidden(sK4(sK1),sK0) | spl8_1),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f84,f188,f41])).
% 0.22/0.52  fof(f188,plain,(
% 0.22/0.52    r2_hidden(sK4(sK1),k1_relat_1(sK1)) | spl8_1),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f27,f72,f53,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(sK4(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f215,plain,(
% 0.22/0.52    k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,sK5(sK1)) | (spl8_1 | ~spl8_6)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f205,f208,f191,f90])).
% 0.22/0.52  fof(f191,plain,(
% 0.22/0.52    sK4(sK1) != sK5(sK1) | spl8_1),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f27,f72,f53,f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X0] : (sK4(X0) != sK5(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    spl8_1 | spl8_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f26,f89,f51])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ( ! [X2,X3] : (~r2_hidden(X2,sK0) | ~r2_hidden(X3,sK0) | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3) | X2 = X3 | v2_funct_1(sK1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    ~spl8_1 | spl8_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f24,f76,f51])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~v2_funct_1(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    ~spl8_1 | ~spl8_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f25,f66,f51])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    sK2 != sK3 | ~v2_funct_1(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ~spl8_1 | spl8_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f23,f61,f51])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    r2_hidden(sK3,sK0) | ~v2_funct_1(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ~spl8_1 | spl8_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f22,f55,f51])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    r2_hidden(sK2,sK0) | ~v2_funct_1(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (13132)------------------------------
% 0.22/0.52  % (13132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (13132)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (13132)Memory used [KB]: 6396
% 0.22/0.52  % (13132)Time elapsed: 0.112 s
% 0.22/0.52  % (13132)------------------------------
% 0.22/0.52  % (13132)------------------------------
% 0.22/0.52  % (13124)Success in time 0.16 s
%------------------------------------------------------------------------------
