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
% DateTime   : Thu Dec  3 12:54:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 163 expanded)
%              Number of leaves         :   25 (  61 expanded)
%              Depth                    :   11
%              Number of atoms          :  209 ( 331 expanded)
%              Number of equality atoms :   38 (  76 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f204,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f76,f81,f95,f107,f108,f123,f125,f174,f190])).

% (5666)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f190,plain,(
    ~ spl7_19 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | ~ spl7_19 ),
    inference(resolution,[],[f173,f98])).

fof(f98,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f57,f32])).

fof(f32,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f47,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f49,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f173,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl7_19
  <=> r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f174,plain,
    ( ~ spl7_6
    | spl7_1
    | spl7_19
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f169,f121,f92,f84,f171,f63,f88])).

fof(f88,plain,
    ( spl7_6
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f63,plain,
    ( spl7_1
  <=> v5_funct_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f84,plain,
    ( spl7_5
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f92,plain,
    ( spl7_7
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f121,plain,
    ( spl7_11
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | v5_funct_1(X0,sK0)
        | r2_hidden(sK1(sK0,X0),k1_relat_1(X0))
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f169,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0)
    | v5_funct_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_11 ),
    inference(forward_demodulation,[],[f159,f86])).

fof(f86,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f159,plain,
    ( v5_funct_1(k1_xboole_0,sK0)
    | r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl7_7
    | ~ spl7_11 ),
    inference(resolution,[],[f122,f93])).

fof(f93,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f92])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | v5_funct_1(X0,sK0)
        | r2_hidden(sK1(sK0,X0),k1_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f121])).

fof(f125,plain,
    ( spl7_7
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f124,f104,f92])).

fof(f104,plain,
    ( spl7_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f124,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl7_8 ),
    inference(resolution,[],[f106,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f106,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f104])).

fof(f123,plain,
    ( spl7_11
    | ~ spl7_3
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f119,f68,f73,f121])).

fof(f73,plain,
    ( spl7_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f68,plain,
    ( spl7_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | r2_hidden(sK1(sK0,X0),k1_relat_1(X0))
        | v5_funct_1(X0,sK0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f35,f70])).

fof(f70,plain,
    ( v1_funct_1(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | r2_hidden(sK1(X0,X1),k1_relat_1(X1))
      | v5_funct_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,k1_relat_1(X1))
               => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

fof(f108,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f102,f88])).

fof(f102,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f98,f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(f107,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f101,f104])).

fof(f101,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f98,f37])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f95,plain,
    ( spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f82,f78,f92,f88,f84])).

fof(f78,plain,
    ( spl7_4
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f82,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_4 ),
    inference(superposition,[],[f58,f80])).

fof(f80,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) = X0
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(f81,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f31,f78])).

fof(f31,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f76,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f28,f73])).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => v5_funct_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v5_funct_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

fof(f71,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f29,f68])).

fof(f29,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f66,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f30,f63])).

fof(f30,plain,(
    ~ v5_funct_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:33:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (5674)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.49  % (5682)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.49  % (5682)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (5674)Refutation not found, incomplete strategy% (5674)------------------------------
% 0.20/0.50  % (5674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f204,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f66,f71,f76,f81,f95,f107,f108,f123,f125,f174,f190])).
% 0.20/0.50  % (5666)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  fof(f190,plain,(
% 0.20/0.50    ~spl7_19),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f187])).
% 0.20/0.50  fof(f187,plain,(
% 0.20/0.50    $false | ~spl7_19),
% 0.20/0.50    inference(resolution,[],[f173,f98])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.50    inference(resolution,[],[f57,f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f47,f56])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f41,f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f46,f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f48,f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f49,f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f50,f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 0.20/0.50  fof(f173,plain,(
% 0.20/0.50    r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0) | ~spl7_19),
% 0.20/0.50    inference(avatar_component_clause,[],[f171])).
% 0.20/0.50  fof(f171,plain,(
% 0.20/0.50    spl7_19 <=> r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.20/0.50  fof(f174,plain,(
% 0.20/0.50    ~spl7_6 | spl7_1 | spl7_19 | ~spl7_5 | ~spl7_7 | ~spl7_11),
% 0.20/0.50    inference(avatar_split_clause,[],[f169,f121,f92,f84,f171,f63,f88])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    spl7_6 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    spl7_1 <=> v5_funct_1(k1_xboole_0,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    spl7_5 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.50  fof(f92,plain,(
% 0.20/0.50    spl7_7 <=> v1_funct_1(k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.50  fof(f121,plain,(
% 0.20/0.50    spl7_11 <=> ! [X0] : (~v1_relat_1(X0) | v5_funct_1(X0,sK0) | r2_hidden(sK1(sK0,X0),k1_relat_1(X0)) | ~v1_funct_1(X0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.50  fof(f169,plain,(
% 0.20/0.50    r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0) | v5_funct_1(k1_xboole_0,sK0) | ~v1_relat_1(k1_xboole_0) | (~spl7_5 | ~spl7_7 | ~spl7_11)),
% 0.20/0.50    inference(forward_demodulation,[],[f159,f86])).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl7_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f84])).
% 0.20/0.50  fof(f159,plain,(
% 0.20/0.50    v5_funct_1(k1_xboole_0,sK0) | r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | (~spl7_7 | ~spl7_11)),
% 0.20/0.50    inference(resolution,[],[f122,f93])).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    v1_funct_1(k1_xboole_0) | ~spl7_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f92])).
% 0.20/0.50  fof(f122,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_funct_1(X0) | v5_funct_1(X0,sK0) | r2_hidden(sK1(sK0,X0),k1_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl7_11),
% 0.20/0.50    inference(avatar_component_clause,[],[f121])).
% 0.20/0.50  fof(f125,plain,(
% 0.20/0.50    spl7_7 | ~spl7_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f124,f104,f92])).
% 0.20/0.50  fof(f104,plain,(
% 0.20/0.50    spl7_8 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.50  fof(f124,plain,(
% 0.20/0.50    v1_funct_1(k1_xboole_0) | ~spl7_8),
% 0.20/0.50    inference(resolution,[],[f106,f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_xboole_0(X0) | v1_funct_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,axiom,(
% 0.20/0.50    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).
% 0.20/0.50  fof(f106,plain,(
% 0.20/0.50    v1_xboole_0(k1_xboole_0) | ~spl7_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f104])).
% 0.20/0.50  fof(f123,plain,(
% 0.20/0.50    spl7_11 | ~spl7_3 | ~spl7_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f119,f68,f73,f121])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    spl7_3 <=> v1_relat_1(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    spl7_2 <=> v1_funct_1(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_relat_1(sK0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK1(sK0,X0),k1_relat_1(X0)) | v5_funct_1(X0,sK0)) ) | ~spl7_2),
% 0.20/0.50    inference(resolution,[],[f35,f70])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    v1_funct_1(sK0) | ~spl7_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f68])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | r2_hidden(sK1(X0,X1),k1_relat_1(X1)) | v5_funct_1(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    spl7_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f102,f88])).
% 0.20/0.50  fof(f102,plain,(
% 0.20/0.50    v1_relat_1(k1_xboole_0)),
% 0.20/0.50    inference(resolution,[],[f98,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).
% 0.20/0.50  fof(f107,plain,(
% 0.20/0.50    spl7_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f101,f104])).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    v1_xboole_0(k1_xboole_0)),
% 0.20/0.50    inference(resolution,[],[f98,f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 0.20/0.50    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f82,f78,f92,f88,f84])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    spl7_4 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl7_4),
% 0.20/0.50    inference(superposition,[],[f58,f80])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl7_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f78])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)) | k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.50    inference(equality_resolution,[],[f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) = X0 | k6_relat_1(X0) != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,axiom,(
% 0.20/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    spl7_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f31,f78])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    spl7_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f28,f73])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    v1_relat_1(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 0.20/0.50    inference(negated_conjecture,[],[f15])).
% 0.20/0.50  fof(f15,conjecture,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    spl7_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f29,f68])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    v1_funct_1(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ~spl7_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f30,f63])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ~v5_funct_1(k1_xboole_0,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (5682)------------------------------
% 0.20/0.50  % (5682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (5682)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (5682)Memory used [KB]: 10746
% 0.20/0.50  % (5682)Time elapsed: 0.094 s
% 0.20/0.50  % (5682)------------------------------
% 0.20/0.50  % (5682)------------------------------
% 0.20/0.51  % (5665)Success in time 0.152 s
%------------------------------------------------------------------------------
