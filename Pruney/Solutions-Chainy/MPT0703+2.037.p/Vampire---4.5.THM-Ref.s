%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 143 expanded)
%              Number of leaves         :   20 (  58 expanded)
%              Depth                    :    8
%              Number of atoms          :  244 ( 462 expanded)
%              Number of equality atoms :   27 (  36 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f253,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f51,f56,f61,f79,f89,f136,f153,f172,f200,f241,f252])).

fof(f252,plain,
    ( spl3_3
    | ~ spl3_20 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | spl3_3
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f247,f50])).

fof(f50,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f247,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_20 ),
    inference(resolution,[],[f218,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f218,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK1,k2_relat_1(sK2)))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl3_20
  <=> r1_tarski(sK0,k3_xboole_0(sK1,k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f241,plain,
    ( spl3_20
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f214,f198,f134,f76,f58,f216])).

fof(f58,plain,
    ( spl3_5
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f76,plain,
    ( spl3_6
  <=> sK0 = k3_xboole_0(sK0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f134,plain,
    ( spl3_11
  <=> ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f198,plain,
    ( spl3_19
  <=> ! [X1,X2] :
        ( r1_tarski(k9_relat_1(sK2,X2),k3_xboole_0(X1,k2_relat_1(sK2)))
        | ~ r1_tarski(X2,k10_relat_1(sK2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f214,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK1,k2_relat_1(sK2)))
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f213,f78])).

fof(f78,plain,
    ( sK0 = k3_xboole_0(sK0,k2_relat_1(sK2))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f213,plain,
    ( r1_tarski(k3_xboole_0(sK0,k2_relat_1(sK2)),k3_xboole_0(sK1,k2_relat_1(sK2)))
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f211,f135])).

fof(f135,plain,
    ( ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k2_relat_1(sK2))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f134])).

fof(f211,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k3_xboole_0(sK1,k2_relat_1(sK2)))
    | ~ spl3_5
    | ~ spl3_19 ),
    inference(resolution,[],[f199,f60])).

fof(f60,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f199,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(X2,k10_relat_1(sK2,X1))
        | r1_tarski(k9_relat_1(sK2,X2),k3_xboole_0(X1,k2_relat_1(sK2))) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f198])).

fof(f200,plain,
    ( spl3_19
    | ~ spl3_11
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f178,f170,f134,f198])).

fof(f170,plain,
    ( spl3_15
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f178,plain,
    ( ! [X2,X1] :
        ( r1_tarski(k9_relat_1(sK2,X2),k3_xboole_0(X1,k2_relat_1(sK2)))
        | ~ r1_tarski(X2,k10_relat_1(sK2,X1)) )
    | ~ spl3_11
    | ~ spl3_15 ),
    inference(superposition,[],[f171,f135])).

fof(f171,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f170])).

fof(f172,plain,
    ( spl3_15
    | ~ spl3_1
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f168,f151,f38,f170])).

fof(f38,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f151,plain,
    ( spl3_14
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(sK2,X2)
        | ~ v1_relat_1(X2)
        | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f168,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) )
    | ~ spl3_1
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f167,f35])).

fof(f35,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f167,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK2,sK2)
        | ~ r1_tarski(X0,X1)
        | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) )
    | ~ spl3_1
    | ~ spl3_14 ),
    inference(resolution,[],[f152,f40])).

fof(f40,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f152,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | ~ r1_tarski(sK2,X2)
        | ~ r1_tarski(X0,X1)
        | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(X2,X1)) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f151])).

fof(f153,plain,
    ( spl3_14
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f84,f38,f151])).

fof(f84,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(sK2,X2)
        | ~ v1_relat_1(X2)
        | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(X2,X1)) )
    | ~ spl3_1 ),
    inference(resolution,[],[f33,f40])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(X3)
      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).

fof(f136,plain,
    ( spl3_11
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f132,f86,f43,f38,f134])).

fof(f43,plain,
    ( spl3_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f86,plain,
    ( spl3_7
  <=> k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f132,plain,
    ( ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k2_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f81,f88])).

fof(f88,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f81,plain,
    ( ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2)))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f80,f40])).

fof(f80,plain,
    ( ! [X0] :
        ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2)))
        | ~ v1_relat_1(sK2) )
    | ~ spl3_2 ),
    inference(resolution,[],[f29,f45])).

fof(f45,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(f89,plain,
    ( spl3_7
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f67,f38,f86])).

fof(f67,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f27,f40])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f79,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f63,f53,f76])).

fof(f53,plain,
    ( spl3_4
  <=> r1_tarski(sK0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f63,plain,
    ( sK0 = k3_xboole_0(sK0,k2_relat_1(sK2))
    | ~ spl3_4 ),
    inference(resolution,[],[f28,f55])).

fof(f55,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f61,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f24,f58])).

fof(f24,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k2_relat_1(X2))
        & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_tarski(sK0,k2_relat_1(sK2))
      & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

fof(f56,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f25,f53])).

fof(f25,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f51,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f26,f48])).

fof(f26,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f23,f43])).

fof(f23,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f41,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f22,f38])).

fof(f22,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:17:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (10952)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (10960)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.50  % (10965)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.50  % (10950)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.50  % (10954)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (10974)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.50  % (10964)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (10968)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.50  % (10975)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.50  % (10957)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.50  % (10953)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (10955)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (10958)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.50  % (10955)Refutation not found, incomplete strategy% (10955)------------------------------
% 0.20/0.50  % (10955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (10955)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (10955)Memory used [KB]: 6140
% 0.20/0.50  % (10955)Time elapsed: 0.097 s
% 0.20/0.50  % (10955)------------------------------
% 0.20/0.50  % (10955)------------------------------
% 0.20/0.51  % (10952)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (10966)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.51  % (10962)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.51  % (10972)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.51  % (10967)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f253,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f41,f46,f51,f56,f61,f79,f89,f136,f153,f172,f200,f241,f252])).
% 0.20/0.51  fof(f252,plain,(
% 0.20/0.51    spl3_3 | ~spl3_20),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f251])).
% 0.20/0.51  fof(f251,plain,(
% 0.20/0.51    $false | (spl3_3 | ~spl3_20)),
% 0.20/0.51    inference(subsumption_resolution,[],[f247,f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ~r1_tarski(sK0,sK1) | spl3_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    spl3_3 <=> r1_tarski(sK0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.51  fof(f247,plain,(
% 0.20/0.51    r1_tarski(sK0,sK1) | ~spl3_20),
% 0.20/0.51    inference(resolution,[],[f218,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).
% 0.20/0.51  fof(f218,plain,(
% 0.20/0.51    r1_tarski(sK0,k3_xboole_0(sK1,k2_relat_1(sK2))) | ~spl3_20),
% 0.20/0.51    inference(avatar_component_clause,[],[f216])).
% 0.20/0.51  fof(f216,plain,(
% 0.20/0.51    spl3_20 <=> r1_tarski(sK0,k3_xboole_0(sK1,k2_relat_1(sK2)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.51  fof(f241,plain,(
% 0.20/0.51    spl3_20 | ~spl3_5 | ~spl3_6 | ~spl3_11 | ~spl3_19),
% 0.20/0.51    inference(avatar_split_clause,[],[f214,f198,f134,f76,f58,f216])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    spl3_5 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    spl3_6 <=> sK0 = k3_xboole_0(sK0,k2_relat_1(sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    spl3_11 <=> ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k2_relat_1(sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.51  fof(f198,plain,(
% 0.20/0.51    spl3_19 <=> ! [X1,X2] : (r1_tarski(k9_relat_1(sK2,X2),k3_xboole_0(X1,k2_relat_1(sK2))) | ~r1_tarski(X2,k10_relat_1(sK2,X1)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.51  fof(f214,plain,(
% 0.20/0.51    r1_tarski(sK0,k3_xboole_0(sK1,k2_relat_1(sK2))) | (~spl3_5 | ~spl3_6 | ~spl3_11 | ~spl3_19)),
% 0.20/0.51    inference(forward_demodulation,[],[f213,f78])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    sK0 = k3_xboole_0(sK0,k2_relat_1(sK2)) | ~spl3_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f76])).
% 0.20/0.51  fof(f213,plain,(
% 0.20/0.51    r1_tarski(k3_xboole_0(sK0,k2_relat_1(sK2)),k3_xboole_0(sK1,k2_relat_1(sK2))) | (~spl3_5 | ~spl3_11 | ~spl3_19)),
% 0.20/0.51    inference(forward_demodulation,[],[f211,f135])).
% 0.20/0.51  fof(f135,plain,(
% 0.20/0.51    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k2_relat_1(sK2))) ) | ~spl3_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f134])).
% 0.20/0.51  fof(f211,plain,(
% 0.20/0.51    r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k3_xboole_0(sK1,k2_relat_1(sK2))) | (~spl3_5 | ~spl3_19)),
% 0.20/0.51    inference(resolution,[],[f199,f60])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | ~spl3_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f58])).
% 0.20/0.51  fof(f199,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~r1_tarski(X2,k10_relat_1(sK2,X1)) | r1_tarski(k9_relat_1(sK2,X2),k3_xboole_0(X1,k2_relat_1(sK2)))) ) | ~spl3_19),
% 0.20/0.51    inference(avatar_component_clause,[],[f198])).
% 0.20/0.51  fof(f200,plain,(
% 0.20/0.51    spl3_19 | ~spl3_11 | ~spl3_15),
% 0.20/0.51    inference(avatar_split_clause,[],[f178,f170,f134,f198])).
% 0.20/0.51  fof(f170,plain,(
% 0.20/0.51    spl3_15 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.51  fof(f178,plain,(
% 0.20/0.51    ( ! [X2,X1] : (r1_tarski(k9_relat_1(sK2,X2),k3_xboole_0(X1,k2_relat_1(sK2))) | ~r1_tarski(X2,k10_relat_1(sK2,X1))) ) | (~spl3_11 | ~spl3_15)),
% 0.20/0.51    inference(superposition,[],[f171,f135])).
% 0.20/0.51  fof(f171,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | ~r1_tarski(X0,X1)) ) | ~spl3_15),
% 0.20/0.51    inference(avatar_component_clause,[],[f170])).
% 0.20/0.51  fof(f172,plain,(
% 0.20/0.51    spl3_15 | ~spl3_1 | ~spl3_14),
% 0.20/0.51    inference(avatar_split_clause,[],[f168,f151,f38,f170])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    spl3_1 <=> v1_relat_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.51  fof(f151,plain,(
% 0.20/0.51    spl3_14 <=> ! [X1,X0,X2] : (~r1_tarski(X0,X1) | ~r1_tarski(sK2,X2) | ~v1_relat_1(X2) | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(X2,X1)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.51  fof(f168,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ) | (~spl3_1 | ~spl3_14)),
% 0.20/0.51    inference(subsumption_resolution,[],[f167,f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.51    inference(flattening,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.51  fof(f167,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(sK2,sK2) | ~r1_tarski(X0,X1) | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ) | (~spl3_1 | ~spl3_14)),
% 0.20/0.51    inference(resolution,[],[f152,f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    v1_relat_1(sK2) | ~spl3_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f38])).
% 0.20/0.51  fof(f152,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(sK2,X2) | ~r1_tarski(X0,X1) | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(X2,X1))) ) | ~spl3_14),
% 0.20/0.51    inference(avatar_component_clause,[],[f151])).
% 0.20/0.51  fof(f153,plain,(
% 0.20/0.51    spl3_14 | ~spl3_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f84,f38,f151])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(sK2,X2) | ~v1_relat_1(X2) | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(X2,X1))) ) | ~spl3_1),
% 0.20/0.51    inference(resolution,[],[f33,f40])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3) | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (! [X3] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(flattening,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (! [X3] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | (~r1_tarski(X0,X1) | ~r1_tarski(X2,X3))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).
% 0.20/0.51  fof(f136,plain,(
% 0.20/0.51    spl3_11 | ~spl3_1 | ~spl3_2 | ~spl3_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f132,f86,f43,f38,f134])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    spl3_2 <=> v1_funct_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    spl3_7 <=> k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.51  fof(f132,plain,(
% 0.20/0.51    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k2_relat_1(sK2))) ) | (~spl3_1 | ~spl3_2 | ~spl3_7)),
% 0.20/0.51    inference(forward_demodulation,[],[f81,f88])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) | ~spl3_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f86])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2)))) ) | (~spl3_1 | ~spl3_2)),
% 0.20/0.51    inference(subsumption_resolution,[],[f80,f40])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2))) | ~v1_relat_1(sK2)) ) | ~spl3_2),
% 0.20/0.51    inference(resolution,[],[f29,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    v1_funct_1(sK2) | ~spl3_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f43])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(flattening,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    spl3_7 | ~spl3_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f67,f38,f86])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) | ~spl3_1),
% 0.20/0.51    inference(resolution,[],[f27,f40])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    spl3_6 | ~spl3_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f63,f53,f76])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    spl3_4 <=> r1_tarski(sK0,k2_relat_1(sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    sK0 = k3_xboole_0(sK0,k2_relat_1(sK2)) | ~spl3_4),
% 0.20/0.51    inference(resolution,[],[f28,f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    r1_tarski(sK0,k2_relat_1(sK2)) | ~spl3_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f53])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    spl3_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f24,f58])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.51    inference(flattening,[],[f9])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.20/0.51    inference(negated_conjecture,[],[f7])).
% 0.20/0.51  fof(f7,conjecture,(
% 0.20/0.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    spl3_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f25,f53])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    r1_tarski(sK0,k2_relat_1(sK2))),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ~spl3_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f26,f48])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ~r1_tarski(sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    spl3_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f23,f43])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    v1_funct_1(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    spl3_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f22,f38])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    v1_relat_1(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (10952)------------------------------
% 0.20/0.51  % (10952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (10952)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (10952)Memory used [KB]: 6268
% 0.20/0.51  % (10952)Time elapsed: 0.090 s
% 0.20/0.51  % (10952)------------------------------
% 0.20/0.51  % (10952)------------------------------
% 0.20/0.52  % (10949)Success in time 0.16 s
%------------------------------------------------------------------------------
