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
% DateTime   : Thu Dec  3 12:53:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 186 expanded)
%              Number of leaves         :   28 (  76 expanded)
%              Depth                    :    9
%              Number of atoms          :  277 ( 433 expanded)
%              Number of equality atoms :   42 (  61 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f858,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f69,f74,f144,f148,f155,f213,f373,f437,f488,f662,f682,f753,f839,f856])).

fof(f856,plain,
    ( spl2_3
    | ~ spl2_58
    | ~ spl2_62 ),
    inference(avatar_contradiction_clause,[],[f851])).

fof(f851,plain,
    ( $false
    | spl2_3
    | ~ spl2_58
    | ~ spl2_62 ),
    inference(unit_resulting_resolution,[],[f73,f752,f838,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f838,plain,
    ( r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))
    | ~ spl2_62 ),
    inference(avatar_component_clause,[],[f836])).

fof(f836,plain,
    ( spl2_62
  <=> r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_62])])).

fof(f752,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0)))
    | ~ spl2_58 ),
    inference(avatar_component_clause,[],[f751])).

fof(f751,plain,
    ( spl2_58
  <=> ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).

fof(f73,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl2_3
  <=> r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f839,plain,
    ( spl2_62
    | ~ spl2_15
    | ~ spl2_41 ),
    inference(avatar_split_clause,[],[f830,f486,f210,f836])).

fof(f210,plain,
    ( spl2_15
  <=> k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f486,plain,
    ( spl2_41
  <=> ! [X5] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X5),k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f830,plain,
    ( r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))
    | ~ spl2_15
    | ~ spl2_41 ),
    inference(forward_demodulation,[],[f825,f41])).

fof(f41,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f825,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1(sK0)),k1_relat_1(k7_relat_1(sK1,sK0)))
    | ~ spl2_15
    | ~ spl2_41 ),
    inference(superposition,[],[f487,f212])).

fof(f212,plain,
    ( k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f210])).

fof(f487,plain,
    ( ! [X5] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X5),k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X5)))
    | ~ spl2_41 ),
    inference(avatar_component_clause,[],[f486])).

fof(f753,plain,
    ( spl2_58
    | ~ spl2_32
    | ~ spl2_53 ),
    inference(avatar_split_clause,[],[f700,f680,f371,f751])).

fof(f371,plain,
    ( spl2_32
  <=> ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f680,plain,
    ( spl2_53
  <=> ! [X1,X0] : r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k10_relat_1(sK1,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).

fof(f700,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0)))
    | ~ spl2_32
    | ~ spl2_53 ),
    inference(superposition,[],[f681,f372])).

fof(f372,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0))
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f371])).

fof(f681,plain,
    ( ! [X0,X1] : r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k10_relat_1(sK1,X1))
    | ~ spl2_53 ),
    inference(avatar_component_clause,[],[f680])).

fof(f682,plain,
    ( spl2_53
    | ~ spl2_1
    | ~ spl2_11
    | ~ spl2_50 ),
    inference(avatar_split_clause,[],[f670,f660,f153,f61,f680])).

fof(f61,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f153,plain,
    ( spl2_11
  <=> ! [X0] : r1_tarski(k7_relat_1(sK1,X0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f660,plain,
    ( spl2_50
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X0)
        | r1_tarski(k10_relat_1(k7_relat_1(sK1,X1),X2),k10_relat_1(X0,X2))
        | ~ r1_tarski(k7_relat_1(sK1,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).

fof(f670,plain,
    ( ! [X0,X1] : r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k10_relat_1(sK1,X1))
    | ~ spl2_1
    | ~ spl2_11
    | ~ spl2_50 ),
    inference(subsumption_resolution,[],[f667,f154])).

fof(f154,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK1,X0),sK1)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f153])).

fof(f667,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k10_relat_1(sK1,X1))
        | ~ r1_tarski(k7_relat_1(sK1,X0),sK1) )
    | ~ spl2_1
    | ~ spl2_50 ),
    inference(resolution,[],[f661,f63])).

fof(f63,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f661,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | r1_tarski(k10_relat_1(k7_relat_1(sK1,X1),X2),k10_relat_1(X0,X2))
        | ~ r1_tarski(k7_relat_1(sK1,X1),X0) )
    | ~ spl2_50 ),
    inference(avatar_component_clause,[],[f660])).

fof(f662,plain,
    ( spl2_50
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f313,f61,f660])).

fof(f313,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | r1_tarski(k10_relat_1(k7_relat_1(sK1,X1),X2),k10_relat_1(X0,X2))
        | ~ r1_tarski(k7_relat_1(sK1,X1),X0) )
    | ~ spl2_1 ),
    inference(resolution,[],[f136,f63])).

fof(f136,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ v1_relat_1(X5)
      | ~ v1_relat_1(X7)
      | r1_tarski(k10_relat_1(k7_relat_1(X5,X6),X8),k10_relat_1(X7,X8))
      | ~ r1_tarski(k7_relat_1(X5,X6),X7) ) ),
    inference(resolution,[],[f53,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t179_relat_1)).

fof(f488,plain,
    ( spl2_41
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f448,f435,f486])).

fof(f435,plain,
    ( spl2_37
  <=> ! [X0] : k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f448,plain,
    ( ! [X5] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X5),k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X5)))
    | ~ spl2_37 ),
    inference(subsumption_resolution,[],[f445,f40])).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f445,plain,
    ( ! [X5] :
        ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X5),k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X5)))
        | ~ v1_relat_1(k6_relat_1(X5)) )
    | ~ spl2_37 ),
    inference(superposition,[],[f47,f436])).

fof(f436,plain,
    ( ! [X0] : k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,X0)))
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f435])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f437,plain,
    ( spl2_37
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f301,f61,f435])).

fof(f301,plain,
    ( ! [X0] : k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,X0)))
    | ~ spl2_1 ),
    inference(resolution,[],[f140,f63])).

fof(f140,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(k6_relat_1(X2),k1_relat_1(X1)) = k7_relat_1(k6_relat_1(X2),k1_relat_1(k7_relat_1(X1,X2))) ) ),
    inference(forward_demodulation,[],[f138,f41])).

fof(f138,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(k6_relat_1(X2),k1_relat_1(X1)) = k7_relat_1(k6_relat_1(X2),k1_relat_1(k7_relat_1(X1,k1_relat_1(k6_relat_1(X2))))) ) ),
    inference(resolution,[],[f45,f40])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).

fof(f373,plain,
    ( spl2_32
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f295,f146,f61,f371])).

fof(f146,plain,
    ( spl2_10
  <=> ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f295,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0))
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f292,f147])).

fof(f147,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f146])).

fof(f292,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0)))
    | ~ spl2_1 ),
    inference(resolution,[],[f92,f63])).

fof(f92,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X2)) = k10_relat_1(k7_relat_1(X1,X2),k2_relat_1(k7_relat_1(X1,X2))) ) ),
    inference(resolution,[],[f44,f46])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f213,plain,
    ( spl2_15
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f208,f66,f210])).

fof(f66,plain,
    ( spl2_2
  <=> r1_tarski(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f208,plain,
    ( k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl2_2 ),
    inference(resolution,[],[f199,f68])).

fof(f68,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f199,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2) ) ),
    inference(forward_demodulation,[],[f124,f111])).

fof(f111,plain,(
    ! [X2,X1] : k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(resolution,[],[f48,f40])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f124,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | k6_relat_1(X1) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f122,f41])).

fof(f122,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k1_relat_1(k6_relat_1(X1)),X2)
      | k6_relat_1(X1) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ) ),
    inference(resolution,[],[f52,f40])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f155,plain,
    ( spl2_11
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f150,f142,f61,f153])).

fof(f142,plain,
    ( spl2_9
  <=> ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f150,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK1,X0),sK1)
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f149,f63])).

fof(f149,plain,
    ( ! [X0] :
        ( r1_tarski(k7_relat_1(sK1,X0),sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl2_9 ),
    inference(superposition,[],[f51,f143])).

fof(f143,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f142])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(f148,plain,
    ( spl2_10
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f117,f61,f146])).

fof(f117,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)
    | ~ spl2_1 ),
    inference(resolution,[],[f49,f63])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f144,plain,
    ( spl2_9
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f110,f61,f142])).

fof(f110,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)
    | ~ spl2_1 ),
    inference(resolution,[],[f48,f63])).

fof(f74,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f39,f71])).

fof(f39,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f33])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f69,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f38,f66])).

fof(f38,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f64,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f37,f61])).

fof(f37,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:37:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (25521)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.48  % (25532)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (25524)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.49  % (25534)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.49  % (25520)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.49  % (25528)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (25525)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.50  % (25523)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (25526)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.50  % (25536)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (25535)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (25522)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (25540)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (25531)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (25527)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (25542)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (25518)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (25537)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (25530)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (25519)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (25539)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (25541)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % (25538)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % (25529)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  % (25543)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.54  % (25533)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.57  % (25520)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f858,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f64,f69,f74,f144,f148,f155,f213,f373,f437,f488,f662,f682,f753,f839,f856])).
% 0.21/0.57  fof(f856,plain,(
% 0.21/0.57    spl2_3 | ~spl2_58 | ~spl2_62),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f851])).
% 0.21/0.57  fof(f851,plain,(
% 0.21/0.57    $false | (spl2_3 | ~spl2_58 | ~spl2_62)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f73,f752,f838,f57])).
% 0.21/0.57  fof(f57,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.57    inference(flattening,[],[f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.57  fof(f838,plain,(
% 0.21/0.57    r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) | ~spl2_62),
% 0.21/0.57    inference(avatar_component_clause,[],[f836])).
% 0.21/0.57  fof(f836,plain,(
% 0.21/0.57    spl2_62 <=> r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_62])])).
% 0.21/0.57  fof(f752,plain,(
% 0.21/0.57    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0)))) ) | ~spl2_58),
% 0.21/0.57    inference(avatar_component_clause,[],[f751])).
% 0.21/0.57  fof(f751,plain,(
% 0.21/0.57    spl2_58 <=> ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).
% 0.21/0.57  fof(f73,plain,(
% 0.21/0.57    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | spl2_3),
% 0.21/0.57    inference(avatar_component_clause,[],[f71])).
% 0.21/0.57  fof(f71,plain,(
% 0.21/0.57    spl2_3 <=> r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.57  fof(f839,plain,(
% 0.21/0.57    spl2_62 | ~spl2_15 | ~spl2_41),
% 0.21/0.57    inference(avatar_split_clause,[],[f830,f486,f210,f836])).
% 0.21/0.57  fof(f210,plain,(
% 0.21/0.57    spl2_15 <=> k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.57  fof(f486,plain,(
% 0.21/0.57    spl2_41 <=> ! [X5] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X5),k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X5)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 0.21/0.57  fof(f830,plain,(
% 0.21/0.57    r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) | (~spl2_15 | ~spl2_41)),
% 0.21/0.57    inference(forward_demodulation,[],[f825,f41])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.57  fof(f825,plain,(
% 0.21/0.57    r1_tarski(k1_relat_1(k6_relat_1(sK0)),k1_relat_1(k7_relat_1(sK1,sK0))) | (~spl2_15 | ~spl2_41)),
% 0.21/0.57    inference(superposition,[],[f487,f212])).
% 0.21/0.57  fof(f212,plain,(
% 0.21/0.57    k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)) | ~spl2_15),
% 0.21/0.57    inference(avatar_component_clause,[],[f210])).
% 0.21/0.57  fof(f487,plain,(
% 0.21/0.57    ( ! [X5] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X5),k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X5)))) ) | ~spl2_41),
% 0.21/0.57    inference(avatar_component_clause,[],[f486])).
% 0.21/0.57  fof(f753,plain,(
% 0.21/0.57    spl2_58 | ~spl2_32 | ~spl2_53),
% 0.21/0.57    inference(avatar_split_clause,[],[f700,f680,f371,f751])).
% 0.21/0.57  fof(f371,plain,(
% 0.21/0.57    spl2_32 <=> ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.21/0.57  fof(f680,plain,(
% 0.21/0.57    spl2_53 <=> ! [X1,X0] : r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k10_relat_1(sK1,X1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).
% 0.21/0.57  fof(f700,plain,(
% 0.21/0.57    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0)))) ) | (~spl2_32 | ~spl2_53)),
% 0.21/0.57    inference(superposition,[],[f681,f372])).
% 0.21/0.57  fof(f372,plain,(
% 0.21/0.57    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0))) ) | ~spl2_32),
% 0.21/0.57    inference(avatar_component_clause,[],[f371])).
% 0.21/0.57  fof(f681,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k10_relat_1(sK1,X1))) ) | ~spl2_53),
% 0.21/0.57    inference(avatar_component_clause,[],[f680])).
% 0.21/0.57  fof(f682,plain,(
% 0.21/0.57    spl2_53 | ~spl2_1 | ~spl2_11 | ~spl2_50),
% 0.21/0.57    inference(avatar_split_clause,[],[f670,f660,f153,f61,f680])).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    spl2_1 <=> v1_relat_1(sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.57  fof(f153,plain,(
% 0.21/0.57    spl2_11 <=> ! [X0] : r1_tarski(k7_relat_1(sK1,X0),sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.57  fof(f660,plain,(
% 0.21/0.57    spl2_50 <=> ! [X1,X0,X2] : (~v1_relat_1(X0) | r1_tarski(k10_relat_1(k7_relat_1(sK1,X1),X2),k10_relat_1(X0,X2)) | ~r1_tarski(k7_relat_1(sK1,X1),X0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).
% 0.21/0.57  fof(f670,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k10_relat_1(sK1,X1))) ) | (~spl2_1 | ~spl2_11 | ~spl2_50)),
% 0.21/0.57    inference(subsumption_resolution,[],[f667,f154])).
% 0.21/0.57  fof(f154,plain,(
% 0.21/0.57    ( ! [X0] : (r1_tarski(k7_relat_1(sK1,X0),sK1)) ) | ~spl2_11),
% 0.21/0.57    inference(avatar_component_clause,[],[f153])).
% 0.21/0.57  fof(f667,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k10_relat_1(sK1,X1)) | ~r1_tarski(k7_relat_1(sK1,X0),sK1)) ) | (~spl2_1 | ~spl2_50)),
% 0.21/0.57    inference(resolution,[],[f661,f63])).
% 0.21/0.57  fof(f63,plain,(
% 0.21/0.57    v1_relat_1(sK1) | ~spl2_1),
% 0.21/0.57    inference(avatar_component_clause,[],[f61])).
% 0.21/0.57  fof(f661,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r1_tarski(k10_relat_1(k7_relat_1(sK1,X1),X2),k10_relat_1(X0,X2)) | ~r1_tarski(k7_relat_1(sK1,X1),X0)) ) | ~spl2_50),
% 0.21/0.57    inference(avatar_component_clause,[],[f660])).
% 0.21/0.57  fof(f662,plain,(
% 0.21/0.57    spl2_50 | ~spl2_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f313,f61,f660])).
% 0.21/0.57  fof(f313,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r1_tarski(k10_relat_1(k7_relat_1(sK1,X1),X2),k10_relat_1(X0,X2)) | ~r1_tarski(k7_relat_1(sK1,X1),X0)) ) | ~spl2_1),
% 0.21/0.57    inference(resolution,[],[f136,f63])).
% 0.21/0.57  fof(f136,plain,(
% 0.21/0.57    ( ! [X6,X8,X7,X5] : (~v1_relat_1(X5) | ~v1_relat_1(X7) | r1_tarski(k10_relat_1(k7_relat_1(X5,X6),X8),k10_relat_1(X7,X8)) | ~r1_tarski(k7_relat_1(X5,X6),X7)) )),
% 0.21/0.57    inference(resolution,[],[f53,f46])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ! [X0,X1] : (! [X2] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(flattening,[],[f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ! [X0,X1] : (! [X2] : ((r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t179_relat_1)).
% 0.21/0.57  fof(f488,plain,(
% 0.21/0.57    spl2_41 | ~spl2_37),
% 0.21/0.57    inference(avatar_split_clause,[],[f448,f435,f486])).
% 0.21/0.57  fof(f435,plain,(
% 0.21/0.57    spl2_37 <=> ! [X0] : k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,X0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 0.21/0.57  fof(f448,plain,(
% 0.21/0.57    ( ! [X5] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X5),k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X5)))) ) | ~spl2_37),
% 0.21/0.57    inference(subsumption_resolution,[],[f445,f40])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.57  fof(f445,plain,(
% 0.21/0.57    ( ! [X5] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X5),k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X5))) | ~v1_relat_1(k6_relat_1(X5))) ) | ~spl2_37),
% 0.21/0.57    inference(superposition,[],[f47,f436])).
% 0.21/0.57  fof(f436,plain,(
% 0.21/0.57    ( ! [X0] : (k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,X0)))) ) | ~spl2_37),
% 0.21/0.57    inference(avatar_component_clause,[],[f435])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.21/0.57  fof(f437,plain,(
% 0.21/0.57    spl2_37 | ~spl2_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f301,f61,f435])).
% 0.21/0.57  fof(f301,plain,(
% 0.21/0.57    ( ! [X0] : (k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,X0)))) ) | ~spl2_1),
% 0.21/0.57    inference(resolution,[],[f140,f63])).
% 0.21/0.57  fof(f140,plain,(
% 0.21/0.57    ( ! [X2,X1] : (~v1_relat_1(X1) | k7_relat_1(k6_relat_1(X2),k1_relat_1(X1)) = k7_relat_1(k6_relat_1(X2),k1_relat_1(k7_relat_1(X1,X2)))) )),
% 0.21/0.57    inference(forward_demodulation,[],[f138,f41])).
% 0.21/0.57  fof(f138,plain,(
% 0.21/0.57    ( ! [X2,X1] : (~v1_relat_1(X1) | k7_relat_1(k6_relat_1(X2),k1_relat_1(X1)) = k7_relat_1(k6_relat_1(X2),k1_relat_1(k7_relat_1(X1,k1_relat_1(k6_relat_1(X2)))))) )),
% 0.21/0.57    inference(resolution,[],[f45,f40])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).
% 0.21/0.57  fof(f373,plain,(
% 0.21/0.57    spl2_32 | ~spl2_1 | ~spl2_10),
% 0.21/0.57    inference(avatar_split_clause,[],[f295,f146,f61,f371])).
% 0.21/0.57  fof(f146,plain,(
% 0.21/0.57    spl2_10 <=> ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.57  fof(f295,plain,(
% 0.21/0.57    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0))) ) | (~spl2_1 | ~spl2_10)),
% 0.21/0.57    inference(forward_demodulation,[],[f292,f147])).
% 0.21/0.57  fof(f147,plain,(
% 0.21/0.57    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) ) | ~spl2_10),
% 0.21/0.57    inference(avatar_component_clause,[],[f146])).
% 0.21/0.57  fof(f292,plain,(
% 0.21/0.57    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0)))) ) | ~spl2_1),
% 0.21/0.57    inference(resolution,[],[f92,f63])).
% 0.21/0.57  fof(f92,plain,(
% 0.21/0.57    ( ! [X2,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X2)) = k10_relat_1(k7_relat_1(X1,X2),k2_relat_1(k7_relat_1(X1,X2)))) )),
% 0.21/0.57    inference(resolution,[],[f44,f46])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.21/0.57  fof(f213,plain,(
% 0.21/0.57    spl2_15 | ~spl2_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f208,f66,f210])).
% 0.21/0.57  fof(f66,plain,(
% 0.21/0.57    spl2_2 <=> r1_tarski(sK0,k1_relat_1(sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.57  fof(f208,plain,(
% 0.21/0.57    k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)) | ~spl2_2),
% 0.21/0.57    inference(resolution,[],[f199,f68])).
% 0.21/0.57  fof(f68,plain,(
% 0.21/0.57    r1_tarski(sK0,k1_relat_1(sK1)) | ~spl2_2),
% 0.21/0.57    inference(avatar_component_clause,[],[f66])).
% 0.21/0.57  fof(f199,plain,(
% 0.21/0.57    ( ! [X2,X1] : (~r1_tarski(X1,X2) | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2)) )),
% 0.21/0.57    inference(forward_demodulation,[],[f124,f111])).
% 0.21/0.57  fof(f111,plain,(
% 0.21/0.57    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) )),
% 0.21/0.57    inference(resolution,[],[f48,f40])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.57  fof(f124,plain,(
% 0.21/0.57    ( ! [X2,X1] : (~r1_tarski(X1,X2) | k6_relat_1(X1) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) )),
% 0.21/0.57    inference(forward_demodulation,[],[f122,f41])).
% 0.21/0.57  fof(f122,plain,(
% 0.21/0.57    ( ! [X2,X1] : (~r1_tarski(k1_relat_1(k6_relat_1(X1)),X2) | k6_relat_1(X1) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) )),
% 0.21/0.57    inference(resolution,[],[f52,f40])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(flattening,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 0.21/0.57  fof(f155,plain,(
% 0.21/0.57    spl2_11 | ~spl2_1 | ~spl2_9),
% 0.21/0.57    inference(avatar_split_clause,[],[f150,f142,f61,f153])).
% 0.21/0.57  fof(f142,plain,(
% 0.21/0.57    spl2_9 <=> ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.57  fof(f150,plain,(
% 0.21/0.57    ( ! [X0] : (r1_tarski(k7_relat_1(sK1,X0),sK1)) ) | (~spl2_1 | ~spl2_9)),
% 0.21/0.57    inference(subsumption_resolution,[],[f149,f63])).
% 0.21/0.57  fof(f149,plain,(
% 0.21/0.57    ( ! [X0] : (r1_tarski(k7_relat_1(sK1,X0),sK1) | ~v1_relat_1(sK1)) ) | ~spl2_9),
% 0.21/0.57    inference(superposition,[],[f51,f143])).
% 0.21/0.57  fof(f143,plain,(
% 0.21/0.57    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)) ) | ~spl2_9),
% 0.21/0.57    inference(avatar_component_clause,[],[f142])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).
% 0.21/0.57  fof(f148,plain,(
% 0.21/0.57    spl2_10 | ~spl2_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f117,f61,f146])).
% 0.21/0.57  fof(f117,plain,(
% 0.21/0.57    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) ) | ~spl2_1),
% 0.21/0.57    inference(resolution,[],[f49,f63])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.57  fof(f144,plain,(
% 0.21/0.57    spl2_9 | ~spl2_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f110,f61,f142])).
% 0.21/0.57  fof(f110,plain,(
% 0.21/0.57    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)) ) | ~spl2_1),
% 0.21/0.57    inference(resolution,[],[f48,f63])).
% 0.21/0.57  fof(f74,plain,(
% 0.21/0.57    ~spl2_3),
% 0.21/0.57    inference(avatar_split_clause,[],[f39,f71])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.21/0.57    inference(cnf_transformation,[],[f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 0.21/0.57    inference(flattening,[],[f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.21/0.57    inference(negated_conjecture,[],[f15])).
% 0.21/0.57  fof(f15,conjecture,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 0.21/0.57  fof(f69,plain,(
% 0.21/0.57    spl2_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f38,f66])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.21/0.57    inference(cnf_transformation,[],[f34])).
% 0.21/0.57  fof(f64,plain,(
% 0.21/0.57    spl2_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f37,f61])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    v1_relat_1(sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f34])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (25520)------------------------------
% 0.21/0.57  % (25520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (25520)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (25520)Memory used [KB]: 6780
% 0.21/0.57  % (25520)Time elapsed: 0.167 s
% 0.21/0.57  % (25520)------------------------------
% 0.21/0.57  % (25520)------------------------------
% 0.21/0.58  % (25517)Success in time 0.223 s
%------------------------------------------------------------------------------
