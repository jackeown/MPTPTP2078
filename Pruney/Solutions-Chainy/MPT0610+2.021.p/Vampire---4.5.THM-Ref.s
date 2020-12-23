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
% DateTime   : Thu Dec  3 12:51:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 133 expanded)
%              Number of leaves         :   23 (  60 expanded)
%              Depth                    :    7
%              Number of atoms          :  243 ( 432 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f311,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f45,f50,f54,f58,f66,f74,f82,f87,f102,f124,f249,f261,f282,f310])).

fof(f310,plain,
    ( spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_50 ),
    inference(avatar_contradiction_clause,[],[f309])).

fof(f309,plain,
    ( $false
    | spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_50 ),
    inference(subsumption_resolution,[],[f308,f49])).

fof(f49,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl2_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f308,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_1
    | ~ spl2_2
    | ~ spl2_50 ),
    inference(subsumption_resolution,[],[f307,f34])).

fof(f34,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl2_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f307,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl2_2
    | ~ spl2_50 ),
    inference(resolution,[],[f281,f39])).

fof(f39,plain,
    ( r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl2_2
  <=> r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f281,plain,
    ( ! [X5] :
        ( ~ r1_xboole_0(k1_relat_1(X5),k1_relat_1(sK1))
        | r1_xboole_0(X5,sK1)
        | ~ v1_relat_1(X5) )
    | ~ spl2_50 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl2_50
  <=> ! [X5] :
        ( r1_xboole_0(X5,sK1)
        | ~ r1_xboole_0(k1_relat_1(X5),k1_relat_1(sK1))
        | ~ v1_relat_1(X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).

fof(f282,plain,
    ( spl2_50
    | ~ spl2_20
    | ~ spl2_46 ),
    inference(avatar_split_clause,[],[f265,f259,f122,f280])).

fof(f122,plain,
    ( spl2_20
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,k2_zfmisc_1(X1,X2))
        | ~ r1_xboole_0(k1_relat_1(X0),X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f259,plain,
    ( spl2_46
  <=> ! [X1] :
        ( ~ r1_xboole_0(X1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))
        | r1_xboole_0(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f265,plain,
    ( ! [X5] :
        ( r1_xboole_0(X5,sK1)
        | ~ r1_xboole_0(k1_relat_1(X5),k1_relat_1(sK1))
        | ~ v1_relat_1(X5) )
    | ~ spl2_20
    | ~ spl2_46 ),
    inference(resolution,[],[f260,f123])).

fof(f123,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(X0,k2_zfmisc_1(X1,X2))
        | ~ r1_xboole_0(k1_relat_1(X0),X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f122])).

fof(f260,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))
        | r1_xboole_0(X1,sK1) )
    | ~ spl2_46 ),
    inference(avatar_component_clause,[],[f259])).

fof(f261,plain,
    ( spl2_46
    | ~ spl2_8
    | ~ spl2_44 ),
    inference(avatar_split_clause,[],[f256,f246,f64,f259])).

fof(f64,plain,
    ( spl2_8
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f246,plain,
    ( spl2_44
  <=> k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)) = k2_xboole_0(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f256,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))
        | r1_xboole_0(X1,sK1) )
    | ~ spl2_8
    | ~ spl2_44 ),
    inference(superposition,[],[f65,f248])).

fof(f248,plain,
    ( k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)) = k2_xboole_0(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f246])).

fof(f65,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | r1_xboole_0(X0,X1) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f64])).

fof(f249,plain,
    ( spl2_44
    | ~ spl2_3
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f243,f85,f42,f246])).

fof(f42,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f85,plain,
    ( spl2_13
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)) = k2_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f243,plain,
    ( k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)) = k2_xboole_0(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))
    | ~ spl2_3
    | ~ spl2_13 ),
    inference(resolution,[],[f86,f44])).

fof(f44,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f86,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)) = k2_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f85])).

fof(f124,plain,
    ( spl2_20
    | ~ spl2_5
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f120,f100,f52,f122])).

fof(f52,plain,
    ( spl2_5
  <=> ! [X0] :
        ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f100,plain,
    ( spl2_16
  <=> ! [X1,X3,X0,X2,X4] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X2,k2_zfmisc_1(X1,X3))
        | ~ r1_tarski(X2,k2_zfmisc_1(X0,X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f120,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(X0,k2_zfmisc_1(X1,X2))
        | ~ r1_xboole_0(k1_relat_1(X0),X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_5
    | ~ spl2_16 ),
    inference(resolution,[],[f101,f53])).

fof(f53,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
        | ~ v1_relat_1(X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f101,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ r1_tarski(X2,k2_zfmisc_1(X0,X4))
        | r1_xboole_0(X2,k2_zfmisc_1(X1,X3))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f100])).

fof(f102,plain,
    ( spl2_16
    | ~ spl2_10
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f98,f80,f72,f100])).

fof(f72,plain,
    ( spl2_10
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f80,plain,
    ( spl2_12
  <=> ! [X1,X3,X0,X2] :
        ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f98,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X2,k2_zfmisc_1(X1,X3))
        | ~ r1_tarski(X2,k2_zfmisc_1(X0,X4)) )
    | ~ spl2_10
    | ~ spl2_12 ),
    inference(resolution,[],[f81,f73])).

fof(f73,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X1,X2)
        | r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f72])).

fof(f81,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f80])).

fof(f87,plain,
    ( spl2_13
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f83,f56,f52,f85])).

fof(f56,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f83,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)) = k2_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) )
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(resolution,[],[f53,f57])).

fof(f57,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f56])).

fof(f82,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f29,f80])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f74,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f28,f72])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f66,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f26,f64])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f58,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f24,f56])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f54,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f23,f52])).

fof(f23,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f50,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f19,f47])).

fof(f19,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_xboole_0(X0,X1)
            & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_xboole_0(sK0,X1)
          & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ~ r1_xboole_0(sK0,X1)
        & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_xboole_0(sK0,sK1)
      & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
             => r1_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
           => r1_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t214_relat_1)).

fof(f45,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f20,f42])).

fof(f20,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f21,f37])).

fof(f21,plain,(
    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f35,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f22,f32])).

fof(f22,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:35:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (13432)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.42  % (13422)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.42  % (13432)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f311,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f35,f40,f45,f50,f54,f58,f66,f74,f82,f87,f102,f124,f249,f261,f282,f310])).
% 0.21/0.42  fof(f310,plain,(
% 0.21/0.42    spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_50),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f309])).
% 0.21/0.42  fof(f309,plain,(
% 0.21/0.42    $false | (spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_50)),
% 0.21/0.42    inference(subsumption_resolution,[],[f308,f49])).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    v1_relat_1(sK0) | ~spl2_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f47])).
% 0.21/0.42  fof(f47,plain,(
% 0.21/0.42    spl2_4 <=> v1_relat_1(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.42  fof(f308,plain,(
% 0.21/0.42    ~v1_relat_1(sK0) | (spl2_1 | ~spl2_2 | ~spl2_50)),
% 0.21/0.42    inference(subsumption_resolution,[],[f307,f34])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    ~r1_xboole_0(sK0,sK1) | spl2_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f32])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    spl2_1 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.42  fof(f307,plain,(
% 0.21/0.42    r1_xboole_0(sK0,sK1) | ~v1_relat_1(sK0) | (~spl2_2 | ~spl2_50)),
% 0.21/0.42    inference(resolution,[],[f281,f39])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) | ~spl2_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f37])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    spl2_2 <=> r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.42  fof(f281,plain,(
% 0.21/0.42    ( ! [X5] : (~r1_xboole_0(k1_relat_1(X5),k1_relat_1(sK1)) | r1_xboole_0(X5,sK1) | ~v1_relat_1(X5)) ) | ~spl2_50),
% 0.21/0.42    inference(avatar_component_clause,[],[f280])).
% 0.21/0.42  fof(f280,plain,(
% 0.21/0.42    spl2_50 <=> ! [X5] : (r1_xboole_0(X5,sK1) | ~r1_xboole_0(k1_relat_1(X5),k1_relat_1(sK1)) | ~v1_relat_1(X5))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).
% 0.21/0.42  fof(f282,plain,(
% 0.21/0.42    spl2_50 | ~spl2_20 | ~spl2_46),
% 0.21/0.42    inference(avatar_split_clause,[],[f265,f259,f122,f280])).
% 0.21/0.42  fof(f122,plain,(
% 0.21/0.42    spl2_20 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,k2_zfmisc_1(X1,X2)) | ~r1_xboole_0(k1_relat_1(X0),X1) | ~v1_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.42  fof(f259,plain,(
% 0.21/0.42    spl2_46 <=> ! [X1] : (~r1_xboole_0(X1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) | r1_xboole_0(X1,sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 0.21/0.42  fof(f265,plain,(
% 0.21/0.42    ( ! [X5] : (r1_xboole_0(X5,sK1) | ~r1_xboole_0(k1_relat_1(X5),k1_relat_1(sK1)) | ~v1_relat_1(X5)) ) | (~spl2_20 | ~spl2_46)),
% 0.21/0.42    inference(resolution,[],[f260,f123])).
% 0.21/0.42  fof(f123,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_zfmisc_1(X1,X2)) | ~r1_xboole_0(k1_relat_1(X0),X1) | ~v1_relat_1(X0)) ) | ~spl2_20),
% 0.21/0.42    inference(avatar_component_clause,[],[f122])).
% 0.21/0.42  fof(f260,plain,(
% 0.21/0.42    ( ! [X1] : (~r1_xboole_0(X1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) | r1_xboole_0(X1,sK1)) ) | ~spl2_46),
% 0.21/0.42    inference(avatar_component_clause,[],[f259])).
% 0.21/0.42  fof(f261,plain,(
% 0.21/0.42    spl2_46 | ~spl2_8 | ~spl2_44),
% 0.21/0.42    inference(avatar_split_clause,[],[f256,f246,f64,f259])).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    spl2_8 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.42  fof(f246,plain,(
% 0.21/0.42    spl2_44 <=> k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)) = k2_xboole_0(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 0.21/0.42  fof(f256,plain,(
% 0.21/0.42    ( ! [X1] : (~r1_xboole_0(X1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) | r1_xboole_0(X1,sK1)) ) | (~spl2_8 | ~spl2_44)),
% 0.21/0.42    inference(superposition,[],[f65,f248])).
% 0.21/0.42  fof(f248,plain,(
% 0.21/0.42    k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)) = k2_xboole_0(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) | ~spl2_44),
% 0.21/0.42    inference(avatar_component_clause,[],[f246])).
% 0.21/0.42  fof(f65,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) ) | ~spl2_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f64])).
% 0.21/0.42  fof(f249,plain,(
% 0.21/0.42    spl2_44 | ~spl2_3 | ~spl2_13),
% 0.21/0.42    inference(avatar_split_clause,[],[f243,f85,f42,f246])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    spl2_3 <=> v1_relat_1(sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.42  fof(f85,plain,(
% 0.21/0.42    spl2_13 <=> ! [X0] : (~v1_relat_1(X0) | k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)) = k2_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.42  fof(f243,plain,(
% 0.21/0.42    k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)) = k2_xboole_0(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) | (~spl2_3 | ~spl2_13)),
% 0.21/0.42    inference(resolution,[],[f86,f44])).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    v1_relat_1(sK1) | ~spl2_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f42])).
% 0.21/0.42  fof(f86,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_relat_1(X0) | k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)) = k2_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) | ~spl2_13),
% 0.21/0.42    inference(avatar_component_clause,[],[f85])).
% 0.21/0.42  fof(f124,plain,(
% 0.21/0.42    spl2_20 | ~spl2_5 | ~spl2_16),
% 0.21/0.42    inference(avatar_split_clause,[],[f120,f100,f52,f122])).
% 0.21/0.42  fof(f52,plain,(
% 0.21/0.42    spl2_5 <=> ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.42  fof(f100,plain,(
% 0.21/0.42    spl2_16 <=> ! [X1,X3,X0,X2,X4] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X2,k2_zfmisc_1(X1,X3)) | ~r1_tarski(X2,k2_zfmisc_1(X0,X4)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.42  fof(f120,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_zfmisc_1(X1,X2)) | ~r1_xboole_0(k1_relat_1(X0),X1) | ~v1_relat_1(X0)) ) | (~spl2_5 | ~spl2_16)),
% 0.21/0.42    inference(resolution,[],[f101,f53])).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) ) | ~spl2_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f52])).
% 0.21/0.42  fof(f101,plain,(
% 0.21/0.42    ( ! [X4,X2,X0,X3,X1] : (~r1_tarski(X2,k2_zfmisc_1(X0,X4)) | r1_xboole_0(X2,k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X0,X1)) ) | ~spl2_16),
% 0.21/0.42    inference(avatar_component_clause,[],[f100])).
% 0.21/0.42  fof(f102,plain,(
% 0.21/0.42    spl2_16 | ~spl2_10 | ~spl2_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f98,f80,f72,f100])).
% 0.21/0.42  fof(f72,plain,(
% 0.21/0.42    spl2_10 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.42  fof(f80,plain,(
% 0.21/0.42    spl2_12 <=> ! [X1,X3,X0,X2] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.42  fof(f98,plain,(
% 0.21/0.42    ( ! [X4,X2,X0,X3,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X2,k2_zfmisc_1(X1,X3)) | ~r1_tarski(X2,k2_zfmisc_1(X0,X4))) ) | (~spl2_10 | ~spl2_12)),
% 0.21/0.42    inference(resolution,[],[f81,f73])).
% 0.21/0.42  fof(f73,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl2_10),
% 0.21/0.42    inference(avatar_component_clause,[],[f72])).
% 0.21/0.42  fof(f81,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X0,X1)) ) | ~spl2_12),
% 0.21/0.42    inference(avatar_component_clause,[],[f80])).
% 0.21/0.42  fof(f87,plain,(
% 0.21/0.42    spl2_13 | ~spl2_5 | ~spl2_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f83,f56,f52,f85])).
% 0.21/0.42  fof(f56,plain,(
% 0.21/0.42    spl2_6 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.42  fof(f83,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_relat_1(X0) | k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)) = k2_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) | (~spl2_5 | ~spl2_6)),
% 0.21/0.42    inference(resolution,[],[f53,f57])).
% 0.21/0.42  fof(f57,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl2_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f56])).
% 0.21/0.42  fof(f82,plain,(
% 0.21/0.42    spl2_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f29,f80])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 0.21/0.42  fof(f74,plain,(
% 0.21/0.42    spl2_10),
% 0.21/0.42    inference(avatar_split_clause,[],[f28,f72])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.42    inference(flattening,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    spl2_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f26,f64])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    spl2_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f24,f56])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    spl2_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f23,f52])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    spl2_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f19,f47])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    v1_relat_1(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    (~r1_xboole_0(sK0,sK1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f17,f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_xboole_0(sK0,X1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ? [X1] : (~r1_xboole_0(sK0,X1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_xboole_0(sK0,sK1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.42    inference(flattening,[],[f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : ((~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,negated_conjecture,(
% 0.21/0.42    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 0.21/0.42    inference(negated_conjecture,[],[f6])).
% 0.21/0.42  fof(f6,conjecture,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t214_relat_1)).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    spl2_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f20,f42])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    v1_relat_1(sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f18])).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    spl2_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f21,f37])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.21/0.42    inference(cnf_transformation,[],[f18])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    ~spl2_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f22,f32])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ~r1_xboole_0(sK0,sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f18])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (13432)------------------------------
% 0.21/0.42  % (13432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (13432)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (13432)Memory used [KB]: 6268
% 0.21/0.42  % (13432)Time elapsed: 0.009 s
% 0.21/0.42  % (13432)------------------------------
% 0.21/0.42  % (13432)------------------------------
% 0.21/0.42  % (13421)Success in time 0.062 s
%------------------------------------------------------------------------------
