%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:51 EST 2020

% Result     : Theorem 2.41s
% Output     : Refutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 277 expanded)
%              Number of leaves         :   36 ( 125 expanded)
%              Depth                    :    9
%              Number of atoms          :  464 (1267 expanded)
%              Number of equality atoms :   40 (  54 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3451,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f82,f83,f88,f93,f98,f103,f183,f249,f362,f367,f593,f701,f854,f1032,f2636,f3150,f3156,f3321,f3322,f3450])).

fof(f3450,plain,
    ( ~ spl3_6
    | ~ spl3_7
    | spl3_248 ),
    inference(avatar_contradiction_clause,[],[f3447])).

fof(f3447,plain,
    ( $false
    | ~ spl3_6
    | ~ spl3_7
    | spl3_248 ),
    inference(unit_resulting_resolution,[],[f505,f3155])).

fof(f3155,plain,
    ( ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | spl3_248 ),
    inference(avatar_component_clause,[],[f3153])).

fof(f3153,plain,
    ( spl3_248
  <=> v1_funct_1(k7_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_248])])).

fof(f505,plain,
    ( ! [X0] : v1_funct_1(k7_relat_1(sK0,X0))
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f498,f204])).

fof(f204,plain,
    ( ! [X0] : k7_relat_1(sK0,X0) = k5_relat_1(k6_relat_1(X0),sK0)
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f102,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f102,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl3_7
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f498,plain,
    ( ! [X0] : v1_funct_1(k5_relat_1(k6_relat_1(X0),sK0))
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f66,f67,f102,f97,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f97,plain,
    ( v1_funct_1(sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_6
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f67,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f66,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f3322,plain,
    ( ~ spl3_7
    | ~ spl3_6
    | ~ spl3_2
    | spl3_70
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f3165,f78,f698,f74,f95,f100])).

fof(f74,plain,
    ( spl3_2
  <=> r1_tarski(sK2,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f698,plain,
    ( spl3_70
  <=> r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).

fof(f78,plain,
    ( spl3_3
  <=> r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f3165,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f79,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(f79,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f3321,plain,
    ( spl3_2
    | ~ spl3_70
    | ~ spl3_96 ),
    inference(avatar_split_clause,[],[f3270,f851,f698,f74])).

fof(f851,plain,
    ( spl3_96
  <=> r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_96])])).

fof(f3270,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | ~ spl3_70
    | ~ spl3_96 ),
    inference(unit_resulting_resolution,[],[f700,f853,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f54,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f853,plain,
    ( r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(sK0))
    | ~ spl3_96 ),
    inference(avatar_component_clause,[],[f851])).

fof(f700,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ spl3_70 ),
    inference(avatar_component_clause,[],[f698])).

fof(f3156,plain,
    ( ~ spl3_5
    | ~ spl3_4
    | ~ spl3_225
    | ~ spl3_248
    | ~ spl3_32
    | spl3_3
    | ~ spl3_7
    | ~ spl3_110 ),
    inference(avatar_split_clause,[],[f3151,f1029,f100,f78,f358,f3153,f2610,f85,f90])).

fof(f90,plain,
    ( spl3_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f85,plain,
    ( spl3_4
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f2610,plain,
    ( spl3_225
  <=> v1_relat_1(k7_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_225])])).

fof(f358,plain,
    ( spl3_32
  <=> sK2 = k1_relat_1(k7_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f1029,plain,
    ( spl3_110
  <=> sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_110])])).

fof(f3151,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | sK2 != k1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_7
    | ~ spl3_110 ),
    inference(forward_demodulation,[],[f3118,f197])).

fof(f197,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f102,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f3118,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK0,sK2))
    | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_110 ),
    inference(superposition,[],[f57,f1031])).

fof(f1031,plain,
    ( sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))
    | ~ spl3_110 ),
    inference(avatar_component_clause,[],[f1029])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

fof(f3150,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2636,plain,
    ( ~ spl3_7
    | spl3_225 ),
    inference(avatar_split_clause,[],[f2631,f2610,f100])).

fof(f2631,plain,
    ( ~ v1_relat_1(sK0)
    | spl3_225 ),
    inference(resolution,[],[f2612,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f2612,plain,
    ( ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | spl3_225 ),
    inference(avatar_component_clause,[],[f2610])).

fof(f1032,plain,
    ( spl3_110
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f1025,f364,f100,f90,f1029])).

fof(f364,plain,
    ( spl3_33
  <=> sK2 = k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f1025,plain,
    ( sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_33 ),
    inference(backward_demodulation,[],[f366,f1005])).

fof(f1005,plain,
    ( ! [X0] : k5_relat_1(k7_relat_1(sK0,X0),sK1) = k7_relat_1(k5_relat_1(sK0,sK1),X0)
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f102,f92,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

fof(f92,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f366,plain,
    ( sK2 = k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f364])).

fof(f854,plain,
    ( spl3_96
    | ~ spl3_18
    | ~ spl3_55 ),
    inference(avatar_split_clause,[],[f835,f590,f246,f851])).

fof(f246,plain,
    ( spl3_18
  <=> r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f590,plain,
    ( spl3_55
  <=> k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f835,plain,
    ( r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(sK0))
    | ~ spl3_18
    | ~ spl3_55 ),
    inference(backward_demodulation,[],[f248,f592])).

fof(f592,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1))
    | ~ spl3_55 ),
    inference(avatar_component_clause,[],[f590])).

fof(f248,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f246])).

fof(f701,plain,
    ( ~ spl3_7
    | ~ spl3_5
    | spl3_70
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f578,f70,f698,f90,f100])).

fof(f70,plain,
    ( spl3_1
  <=> r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f578,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl3_1 ),
    inference(superposition,[],[f71,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f71,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f593,plain,
    ( spl3_55
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f574,f100,f90,f590])).

fof(f574,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f102,f92,f59])).

fof(f367,plain,
    ( ~ spl3_14
    | spl3_33
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f354,f70,f364,f180])).

fof(f180,plain,
    ( spl3_14
  <=> v1_relat_1(k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f354,plain,
    ( sK2 = k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl3_1 ),
    inference(resolution,[],[f56,f71])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f362,plain,
    ( ~ spl3_7
    | spl3_32
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f353,f74,f358,f100])).

fof(f353,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f56,f75])).

fof(f75,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f249,plain,
    ( spl3_18
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f236,f100,f90,f246])).

fof(f236,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f102,f92,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(f183,plain,
    ( spl3_14
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f172,f100,f90,f180])).

fof(f172,plain,
    ( v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f102,f92,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f103,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f45,f100])).

fof(f45,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
      | ~ r1_tarski(sK2,k1_relat_1(sK0))
      | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) )
    & ( ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
        & r1_tarski(sK2,k1_relat_1(sK0)) )
      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) )
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f43,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  | ~ r1_tarski(X2,k1_relat_1(X0))
                  | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
                & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                    & r1_tarski(X2,k1_relat_1(X0)) )
                  | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(sK0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) )
              & ( ( r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(sK0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(sK0))
              | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) )
            & ( ( r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(sK0)) )
              | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) ) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1))
            | ~ r1_tarski(X2,k1_relat_1(sK0))
            | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))) )
          & ( ( r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1))
              & r1_tarski(X2,k1_relat_1(sK0)) )
            | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))) ) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1))
          | ~ r1_tarski(X2,k1_relat_1(sK0))
          | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))) )
        & ( ( r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1))
            & r1_tarski(X2,k1_relat_1(sK0)) )
          | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))) ) )
   => ( ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
        | ~ r1_tarski(sK2,k1_relat_1(sK0))
        | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) )
      & ( ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
          & r1_tarski(sK2,k1_relat_1(sK0)) )
        | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(X0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
              & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(X0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
              & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
              <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_1)).

fof(f98,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f46,f95])).

fof(f46,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f93,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f47,f90])).

fof(f47,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f88,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f48,f85])).

fof(f48,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f83,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f49,f74,f70])).

fof(f49,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f82,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f50,f78,f70])).

fof(f50,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f81,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f51,f78,f74,f70])).

fof(f51,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:58:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (16208)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.48  % (16220)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.49  % (16204)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.50  % (16211)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.50  % (16203)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.50  % (16212)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.51  % (16221)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.51  % (16199)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.51  % (16202)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.51  % (16213)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.51  % (16202)Refutation not found, incomplete strategy% (16202)------------------------------
% 0.22/0.51  % (16202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (16202)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (16202)Memory used [KB]: 10618
% 0.22/0.51  % (16202)Time elapsed: 0.102 s
% 0.22/0.51  % (16202)------------------------------
% 0.22/0.51  % (16202)------------------------------
% 0.22/0.51  % (16201)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.51  % (16214)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.51  % (16210)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.51  % (16205)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.51  % (16200)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.52  % (16215)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.52  % (16217)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.52  % (16222)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.52  % (16222)Refutation not found, incomplete strategy% (16222)------------------------------
% 0.22/0.52  % (16222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (16222)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (16222)Memory used [KB]: 10618
% 0.22/0.52  % (16222)Time elapsed: 0.114 s
% 0.22/0.52  % (16222)------------------------------
% 0.22/0.52  % (16222)------------------------------
% 0.22/0.52  % (16219)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.52  % (16206)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (16218)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.53  % (16209)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.53  % (16209)Refutation not found, incomplete strategy% (16209)------------------------------
% 0.22/0.53  % (16209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (16209)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (16209)Memory used [KB]: 10618
% 0.22/0.53  % (16209)Time elapsed: 0.123 s
% 0.22/0.53  % (16209)------------------------------
% 0.22/0.53  % (16209)------------------------------
% 0.22/0.53  % (16216)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.44/0.54  % (16207)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 2.09/0.64  % (16221)Refutation not found, incomplete strategy% (16221)------------------------------
% 2.09/0.64  % (16221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.64  % (16221)Termination reason: Refutation not found, incomplete strategy
% 2.09/0.64  
% 2.09/0.64  % (16221)Memory used [KB]: 1663
% 2.09/0.64  % (16221)Time elapsed: 0.177 s
% 2.09/0.64  % (16221)------------------------------
% 2.09/0.64  % (16221)------------------------------
% 2.41/0.68  % (16205)Refutation found. Thanks to Tanya!
% 2.41/0.68  % SZS status Theorem for theBenchmark
% 2.41/0.68  % SZS output start Proof for theBenchmark
% 2.41/0.68  fof(f3451,plain,(
% 2.41/0.68    $false),
% 2.41/0.68    inference(avatar_sat_refutation,[],[f81,f82,f83,f88,f93,f98,f103,f183,f249,f362,f367,f593,f701,f854,f1032,f2636,f3150,f3156,f3321,f3322,f3450])).
% 2.41/0.68  fof(f3450,plain,(
% 2.41/0.68    ~spl3_6 | ~spl3_7 | spl3_248),
% 2.41/0.68    inference(avatar_contradiction_clause,[],[f3447])).
% 2.41/0.68  fof(f3447,plain,(
% 2.41/0.68    $false | (~spl3_6 | ~spl3_7 | spl3_248)),
% 2.41/0.68    inference(unit_resulting_resolution,[],[f505,f3155])).
% 2.41/0.68  fof(f3155,plain,(
% 2.41/0.68    ~v1_funct_1(k7_relat_1(sK0,sK2)) | spl3_248),
% 2.41/0.68    inference(avatar_component_clause,[],[f3153])).
% 2.41/0.68  fof(f3153,plain,(
% 2.41/0.68    spl3_248 <=> v1_funct_1(k7_relat_1(sK0,sK2))),
% 2.41/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_248])])).
% 2.41/0.68  fof(f505,plain,(
% 2.41/0.68    ( ! [X0] : (v1_funct_1(k7_relat_1(sK0,X0))) ) | (~spl3_6 | ~spl3_7)),
% 2.41/0.68    inference(forward_demodulation,[],[f498,f204])).
% 2.41/0.68  fof(f204,plain,(
% 2.41/0.68    ( ! [X0] : (k7_relat_1(sK0,X0) = k5_relat_1(k6_relat_1(X0),sK0)) ) | ~spl3_7),
% 2.41/0.68    inference(unit_resulting_resolution,[],[f102,f65])).
% 2.41/0.68  fof(f65,plain,(
% 2.41/0.68    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 2.41/0.68    inference(cnf_transformation,[],[f37])).
% 2.41/0.68  fof(f37,plain,(
% 2.41/0.68    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 2.41/0.68    inference(ennf_transformation,[],[f10])).
% 2.41/0.68  fof(f10,axiom,(
% 2.41/0.68    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 2.41/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 2.41/0.68  fof(f102,plain,(
% 2.41/0.68    v1_relat_1(sK0) | ~spl3_7),
% 2.41/0.68    inference(avatar_component_clause,[],[f100])).
% 2.41/0.68  fof(f100,plain,(
% 2.41/0.68    spl3_7 <=> v1_relat_1(sK0)),
% 2.41/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 2.41/0.68  fof(f498,plain,(
% 2.41/0.68    ( ! [X0] : (v1_funct_1(k5_relat_1(k6_relat_1(X0),sK0))) ) | (~spl3_6 | ~spl3_7)),
% 2.41/0.68    inference(unit_resulting_resolution,[],[f66,f67,f102,f97,f63])).
% 2.41/0.68  fof(f63,plain,(
% 2.41/0.68    ( ! [X0,X1] : (v1_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.41/0.68    inference(cnf_transformation,[],[f35])).
% 2.41/0.68  fof(f35,plain,(
% 2.41/0.68    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.41/0.68    inference(flattening,[],[f34])).
% 2.41/0.68  fof(f34,plain,(
% 2.41/0.68    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.41/0.68    inference(ennf_transformation,[],[f12])).
% 2.41/0.68  fof(f12,axiom,(
% 2.41/0.68    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 2.41/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).
% 2.41/0.68  fof(f97,plain,(
% 2.41/0.68    v1_funct_1(sK0) | ~spl3_6),
% 2.41/0.68    inference(avatar_component_clause,[],[f95])).
% 2.41/0.68  fof(f95,plain,(
% 2.41/0.68    spl3_6 <=> v1_funct_1(sK0)),
% 2.41/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 2.41/0.68  fof(f67,plain,(
% 2.41/0.68    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 2.41/0.68    inference(cnf_transformation,[],[f13])).
% 2.41/0.68  fof(f13,axiom,(
% 2.41/0.68    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.41/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 2.41/0.68  fof(f66,plain,(
% 2.41/0.68    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.41/0.68    inference(cnf_transformation,[],[f13])).
% 2.41/0.68  fof(f3322,plain,(
% 2.41/0.68    ~spl3_7 | ~spl3_6 | ~spl3_2 | spl3_70 | ~spl3_3),
% 2.41/0.68    inference(avatar_split_clause,[],[f3165,f78,f698,f74,f95,f100])).
% 2.41/0.68  fof(f74,plain,(
% 2.41/0.68    spl3_2 <=> r1_tarski(sK2,k1_relat_1(sK0))),
% 2.41/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.41/0.68  fof(f698,plain,(
% 2.41/0.68    spl3_70 <=> r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))),
% 2.41/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).
% 2.41/0.68  fof(f78,plain,(
% 2.41/0.68    spl3_3 <=> r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))),
% 2.41/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.41/0.68  fof(f3165,plain,(
% 2.41/0.68    r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl3_3),
% 2.41/0.68    inference(resolution,[],[f79,f52])).
% 2.41/0.68  fof(f52,plain,(
% 2.41/0.68    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(X2,X0),X1) | r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.41/0.68    inference(cnf_transformation,[],[f21])).
% 2.41/0.68  fof(f21,plain,(
% 2.41/0.68    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.41/0.68    inference(flattening,[],[f20])).
% 2.41/0.68  fof(f20,plain,(
% 2.41/0.68    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.41/0.68    inference(ennf_transformation,[],[f14])).
% 2.41/0.68  fof(f14,axiom,(
% 2.41/0.68    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 2.41/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).
% 2.41/0.68  fof(f79,plain,(
% 2.41/0.68    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~spl3_3),
% 2.41/0.68    inference(avatar_component_clause,[],[f78])).
% 2.41/0.68  fof(f3321,plain,(
% 2.41/0.68    spl3_2 | ~spl3_70 | ~spl3_96),
% 2.41/0.68    inference(avatar_split_clause,[],[f3270,f851,f698,f74])).
% 2.41/0.68  fof(f851,plain,(
% 2.41/0.68    spl3_96 <=> r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(sK0))),
% 2.41/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_96])])).
% 2.41/0.68  fof(f3270,plain,(
% 2.41/0.68    r1_tarski(sK2,k1_relat_1(sK0)) | (~spl3_70 | ~spl3_96)),
% 2.41/0.68    inference(unit_resulting_resolution,[],[f700,f853,f111])).
% 2.41/0.68  fof(f111,plain,(
% 2.41/0.68    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.41/0.68    inference(superposition,[],[f54,f55])).
% 2.41/0.68  fof(f55,plain,(
% 2.41/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.41/0.68    inference(cnf_transformation,[],[f24])).
% 2.41/0.68  fof(f24,plain,(
% 2.41/0.68    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.41/0.68    inference(ennf_transformation,[],[f2])).
% 2.41/0.68  fof(f2,axiom,(
% 2.41/0.68    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.41/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.41/0.68  fof(f54,plain,(
% 2.41/0.68    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 2.41/0.68    inference(cnf_transformation,[],[f23])).
% 2.41/0.68  fof(f23,plain,(
% 2.41/0.68    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 2.41/0.68    inference(ennf_transformation,[],[f1])).
% 2.41/0.68  fof(f1,axiom,(
% 2.41/0.68    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 2.41/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 2.41/0.68  fof(f853,plain,(
% 2.41/0.68    r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(sK0)) | ~spl3_96),
% 2.41/0.68    inference(avatar_component_clause,[],[f851])).
% 2.41/0.68  fof(f700,plain,(
% 2.41/0.68    r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | ~spl3_70),
% 2.41/0.68    inference(avatar_component_clause,[],[f698])).
% 2.41/0.68  fof(f3156,plain,(
% 2.41/0.68    ~spl3_5 | ~spl3_4 | ~spl3_225 | ~spl3_248 | ~spl3_32 | spl3_3 | ~spl3_7 | ~spl3_110),
% 2.41/0.68    inference(avatar_split_clause,[],[f3151,f1029,f100,f78,f358,f3153,f2610,f85,f90])).
% 2.41/0.68  fof(f90,plain,(
% 2.41/0.68    spl3_5 <=> v1_relat_1(sK1)),
% 2.41/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.41/0.68  fof(f85,plain,(
% 2.41/0.68    spl3_4 <=> v1_funct_1(sK1)),
% 2.41/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.41/0.68  fof(f2610,plain,(
% 2.41/0.68    spl3_225 <=> v1_relat_1(k7_relat_1(sK0,sK2))),
% 2.41/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_225])])).
% 2.41/0.68  fof(f358,plain,(
% 2.41/0.68    spl3_32 <=> sK2 = k1_relat_1(k7_relat_1(sK0,sK2))),
% 2.41/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 2.41/0.68  fof(f1029,plain,(
% 2.41/0.68    spl3_110 <=> sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))),
% 2.41/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_110])])).
% 2.41/0.68  fof(f3151,plain,(
% 2.41/0.68    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | sK2 != k1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl3_7 | ~spl3_110)),
% 2.41/0.68    inference(forward_demodulation,[],[f3118,f197])).
% 2.41/0.68  fof(f197,plain,(
% 2.41/0.68    ( ! [X0] : (k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)) ) | ~spl3_7),
% 2.41/0.68    inference(unit_resulting_resolution,[],[f102,f53])).
% 2.41/0.68  fof(f53,plain,(
% 2.41/0.68    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.41/0.68    inference(cnf_transformation,[],[f22])).
% 2.41/0.68  fof(f22,plain,(
% 2.41/0.68    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.41/0.68    inference(ennf_transformation,[],[f6])).
% 2.41/0.68  fof(f6,axiom,(
% 2.41/0.68    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.41/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 2.41/0.68  fof(f3118,plain,(
% 2.41/0.68    sK2 != k1_relat_1(k7_relat_1(sK0,sK2)) | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~v1_funct_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl3_110),
% 2.41/0.68    inference(superposition,[],[f57,f1031])).
% 2.41/0.68  fof(f1031,plain,(
% 2.41/0.68    sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) | ~spl3_110),
% 2.41/0.68    inference(avatar_component_clause,[],[f1029])).
% 2.41/0.68  fof(f57,plain,(
% 2.41/0.68    ( ! [X0,X1] : (k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.41/0.68    inference(cnf_transformation,[],[f28])).
% 2.41/0.68  fof(f28,plain,(
% 2.41/0.68    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.41/0.68    inference(flattening,[],[f27])).
% 2.41/0.68  fof(f27,plain,(
% 2.41/0.68    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.41/0.68    inference(ennf_transformation,[],[f15])).
% 2.41/0.68  fof(f15,axiom,(
% 2.41/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 2.41/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).
% 2.41/0.68  fof(f3150,plain,(
% 2.41/0.68    k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | ~r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))),
% 2.41/0.68    introduced(theory_tautology_sat_conflict,[])).
% 2.41/0.68  fof(f2636,plain,(
% 2.41/0.68    ~spl3_7 | spl3_225),
% 2.41/0.68    inference(avatar_split_clause,[],[f2631,f2610,f100])).
% 2.41/0.68  fof(f2631,plain,(
% 2.41/0.68    ~v1_relat_1(sK0) | spl3_225),
% 2.41/0.68    inference(resolution,[],[f2612,f68])).
% 2.41/0.68  fof(f68,plain,(
% 2.41/0.68    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.41/0.68    inference(cnf_transformation,[],[f38])).
% 2.41/0.68  fof(f38,plain,(
% 2.41/0.68    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.41/0.68    inference(ennf_transformation,[],[f4])).
% 2.41/0.68  fof(f4,axiom,(
% 2.41/0.68    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.41/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 2.41/0.68  fof(f2612,plain,(
% 2.41/0.68    ~v1_relat_1(k7_relat_1(sK0,sK2)) | spl3_225),
% 2.41/0.68    inference(avatar_component_clause,[],[f2610])).
% 2.41/0.68  fof(f1032,plain,(
% 2.41/0.68    spl3_110 | ~spl3_5 | ~spl3_7 | ~spl3_33),
% 2.41/0.68    inference(avatar_split_clause,[],[f1025,f364,f100,f90,f1029])).
% 2.41/0.68  fof(f364,plain,(
% 2.41/0.68    spl3_33 <=> sK2 = k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2))),
% 2.41/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 2.41/0.68  fof(f1025,plain,(
% 2.41/0.68    sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) | (~spl3_5 | ~spl3_7 | ~spl3_33)),
% 2.41/0.68    inference(backward_demodulation,[],[f366,f1005])).
% 2.41/0.68  fof(f1005,plain,(
% 2.41/0.68    ( ! [X0] : (k5_relat_1(k7_relat_1(sK0,X0),sK1) = k7_relat_1(k5_relat_1(sK0,sK1),X0)) ) | (~spl3_5 | ~spl3_7)),
% 2.41/0.68    inference(unit_resulting_resolution,[],[f102,f92,f64])).
% 2.41/0.68  fof(f64,plain,(
% 2.41/0.68    ( ! [X2,X0,X1] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 2.41/0.68    inference(cnf_transformation,[],[f36])).
% 2.41/0.68  fof(f36,plain,(
% 2.41/0.68    ! [X0,X1] : (! [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 2.41/0.68    inference(ennf_transformation,[],[f5])).
% 2.41/0.68  fof(f5,axiom,(
% 2.41/0.68    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 2.41/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).
% 2.41/0.68  fof(f92,plain,(
% 2.41/0.68    v1_relat_1(sK1) | ~spl3_5),
% 2.41/0.68    inference(avatar_component_clause,[],[f90])).
% 2.41/0.68  fof(f366,plain,(
% 2.41/0.68    sK2 = k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2)) | ~spl3_33),
% 2.41/0.68    inference(avatar_component_clause,[],[f364])).
% 2.41/0.68  fof(f854,plain,(
% 2.41/0.68    spl3_96 | ~spl3_18 | ~spl3_55),
% 2.41/0.68    inference(avatar_split_clause,[],[f835,f590,f246,f851])).
% 2.41/0.68  fof(f246,plain,(
% 2.41/0.68    spl3_18 <=> r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))),
% 2.41/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 2.41/0.68  fof(f590,plain,(
% 2.41/0.68    spl3_55 <=> k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1))),
% 2.41/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 2.41/0.68  fof(f835,plain,(
% 2.41/0.68    r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(sK0)) | (~spl3_18 | ~spl3_55)),
% 2.41/0.68    inference(backward_demodulation,[],[f248,f592])).
% 2.41/0.68  fof(f592,plain,(
% 2.41/0.68    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1)) | ~spl3_55),
% 2.41/0.68    inference(avatar_component_clause,[],[f590])).
% 2.41/0.68  fof(f248,plain,(
% 2.41/0.68    r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) | ~spl3_18),
% 2.41/0.68    inference(avatar_component_clause,[],[f246])).
% 2.41/0.68  fof(f701,plain,(
% 2.41/0.68    ~spl3_7 | ~spl3_5 | spl3_70 | ~spl3_1),
% 2.41/0.68    inference(avatar_split_clause,[],[f578,f70,f698,f90,f100])).
% 2.41/0.68  fof(f70,plain,(
% 2.41/0.68    spl3_1 <=> r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 2.41/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.41/0.68  fof(f578,plain,(
% 2.41/0.68    r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | ~spl3_1),
% 2.41/0.68    inference(superposition,[],[f71,f59])).
% 2.41/0.68  fof(f59,plain,(
% 2.41/0.68    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.41/0.68    inference(cnf_transformation,[],[f30])).
% 2.41/0.68  fof(f30,plain,(
% 2.41/0.68    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.41/0.68    inference(ennf_transformation,[],[f7])).
% 2.41/0.68  fof(f7,axiom,(
% 2.41/0.68    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 2.41/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 2.41/0.68  fof(f71,plain,(
% 2.41/0.68    r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | ~spl3_1),
% 2.41/0.68    inference(avatar_component_clause,[],[f70])).
% 2.41/0.68  fof(f593,plain,(
% 2.41/0.68    spl3_55 | ~spl3_5 | ~spl3_7),
% 2.41/0.68    inference(avatar_split_clause,[],[f574,f100,f90,f590])).
% 2.41/0.68  fof(f574,plain,(
% 2.41/0.68    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1)) | (~spl3_5 | ~spl3_7)),
% 2.41/0.68    inference(unit_resulting_resolution,[],[f102,f92,f59])).
% 2.41/0.68  fof(f367,plain,(
% 2.41/0.68    ~spl3_14 | spl3_33 | ~spl3_1),
% 2.41/0.68    inference(avatar_split_clause,[],[f354,f70,f364,f180])).
% 2.41/0.68  fof(f180,plain,(
% 2.41/0.68    spl3_14 <=> v1_relat_1(k5_relat_1(sK0,sK1))),
% 2.41/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 2.41/0.68  fof(f354,plain,(
% 2.41/0.68    sK2 = k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2)) | ~v1_relat_1(k5_relat_1(sK0,sK1)) | ~spl3_1),
% 2.41/0.68    inference(resolution,[],[f56,f71])).
% 2.41/0.68  fof(f56,plain,(
% 2.41/0.68    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 2.41/0.68    inference(cnf_transformation,[],[f26])).
% 2.41/0.68  fof(f26,plain,(
% 2.41/0.68    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.41/0.68    inference(flattening,[],[f25])).
% 2.41/0.68  fof(f25,plain,(
% 2.41/0.68    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.41/0.68    inference(ennf_transformation,[],[f9])).
% 2.41/0.68  fof(f9,axiom,(
% 2.41/0.68    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 2.41/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 2.41/0.68  fof(f362,plain,(
% 2.41/0.68    ~spl3_7 | spl3_32 | ~spl3_2),
% 2.41/0.68    inference(avatar_split_clause,[],[f353,f74,f358,f100])).
% 2.41/0.68  fof(f353,plain,(
% 2.41/0.68    sK2 = k1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(sK0) | ~spl3_2),
% 2.41/0.68    inference(resolution,[],[f56,f75])).
% 2.41/0.68  fof(f75,plain,(
% 2.41/0.68    r1_tarski(sK2,k1_relat_1(sK0)) | ~spl3_2),
% 2.41/0.68    inference(avatar_component_clause,[],[f74])).
% 2.41/0.68  fof(f249,plain,(
% 2.41/0.68    spl3_18 | ~spl3_5 | ~spl3_7),
% 2.41/0.68    inference(avatar_split_clause,[],[f236,f100,f90,f246])).
% 2.41/0.68  fof(f236,plain,(
% 2.41/0.68    r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) | (~spl3_5 | ~spl3_7)),
% 2.41/0.68    inference(unit_resulting_resolution,[],[f102,f92,f58])).
% 2.41/0.68  fof(f58,plain,(
% 2.41/0.68    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.41/0.68    inference(cnf_transformation,[],[f29])).
% 2.41/0.68  fof(f29,plain,(
% 2.41/0.68    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.41/0.68    inference(ennf_transformation,[],[f8])).
% 2.41/0.68  fof(f8,axiom,(
% 2.41/0.68    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 2.41/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).
% 2.41/0.68  fof(f183,plain,(
% 2.41/0.68    spl3_14 | ~spl3_5 | ~spl3_7),
% 2.41/0.68    inference(avatar_split_clause,[],[f172,f100,f90,f180])).
% 2.41/0.68  fof(f172,plain,(
% 2.41/0.68    v1_relat_1(k5_relat_1(sK0,sK1)) | (~spl3_5 | ~spl3_7)),
% 2.41/0.68    inference(unit_resulting_resolution,[],[f102,f92,f61])).
% 2.41/0.68  fof(f61,plain,(
% 2.41/0.68    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.41/0.68    inference(cnf_transformation,[],[f33])).
% 2.41/0.68  fof(f33,plain,(
% 2.41/0.68    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 2.41/0.68    inference(flattening,[],[f32])).
% 2.41/0.68  fof(f32,plain,(
% 2.41/0.68    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 2.41/0.68    inference(ennf_transformation,[],[f3])).
% 2.41/0.68  fof(f3,axiom,(
% 2.41/0.68    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 2.41/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 2.41/0.68  fof(f103,plain,(
% 2.41/0.68    spl3_7),
% 2.41/0.68    inference(avatar_split_clause,[],[f45,f100])).
% 2.41/0.68  fof(f45,plain,(
% 2.41/0.68    v1_relat_1(sK0)),
% 2.41/0.68    inference(cnf_transformation,[],[f44])).
% 2.41/0.68  fof(f44,plain,(
% 2.41/0.68    (((~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) & r1_tarski(sK2,k1_relat_1(sK0))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))))) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 2.41/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f43,f42,f41])).
% 2.41/0.68  fof(f41,plain,(
% 2.41/0.68    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 2.41/0.68    introduced(choice_axiom,[])).
% 2.41/0.68  fof(f42,plain,(
% 2.41/0.68    ? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))))) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 2.41/0.68    introduced(choice_axiom,[])).
% 2.41/0.68  fof(f43,plain,(
% 2.41/0.68    ? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))))) => ((~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) & r1_tarski(sK2,k1_relat_1(sK0))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))))),
% 2.41/0.68    introduced(choice_axiom,[])).
% 2.41/0.68  fof(f40,plain,(
% 2.41/0.68    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.41/0.68    inference(flattening,[],[f39])).
% 2.41/0.68  fof(f39,plain,(
% 2.41/0.68    ? [X0] : (? [X1] : (? [X2] : (((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.41/0.68    inference(nnf_transformation,[],[f19])).
% 2.41/0.68  fof(f19,plain,(
% 2.41/0.68    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.41/0.68    inference(flattening,[],[f18])).
% 2.41/0.68  fof(f18,plain,(
% 2.41/0.68    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.41/0.68    inference(ennf_transformation,[],[f17])).
% 2.41/0.68  fof(f17,negated_conjecture,(
% 2.41/0.68    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 2.41/0.68    inference(negated_conjecture,[],[f16])).
% 2.41/0.68  fof(f16,conjecture,(
% 2.41/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 2.41/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_1)).
% 2.41/0.68  fof(f98,plain,(
% 2.41/0.68    spl3_6),
% 2.41/0.68    inference(avatar_split_clause,[],[f46,f95])).
% 2.41/0.68  fof(f46,plain,(
% 2.41/0.68    v1_funct_1(sK0)),
% 2.41/0.68    inference(cnf_transformation,[],[f44])).
% 2.41/0.68  fof(f93,plain,(
% 2.41/0.68    spl3_5),
% 2.41/0.68    inference(avatar_split_clause,[],[f47,f90])).
% 2.41/0.68  fof(f47,plain,(
% 2.41/0.68    v1_relat_1(sK1)),
% 2.41/0.68    inference(cnf_transformation,[],[f44])).
% 2.41/0.68  fof(f88,plain,(
% 2.41/0.68    spl3_4),
% 2.41/0.68    inference(avatar_split_clause,[],[f48,f85])).
% 2.41/0.68  fof(f48,plain,(
% 2.41/0.68    v1_funct_1(sK1)),
% 2.41/0.68    inference(cnf_transformation,[],[f44])).
% 2.41/0.68  fof(f83,plain,(
% 2.41/0.68    spl3_1 | spl3_2),
% 2.41/0.68    inference(avatar_split_clause,[],[f49,f74,f70])).
% 2.41/0.68  fof(f49,plain,(
% 2.41/0.68    r1_tarski(sK2,k1_relat_1(sK0)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 2.41/0.68    inference(cnf_transformation,[],[f44])).
% 2.41/0.68  fof(f82,plain,(
% 2.41/0.68    spl3_1 | spl3_3),
% 2.41/0.68    inference(avatar_split_clause,[],[f50,f78,f70])).
% 2.41/0.68  fof(f50,plain,(
% 2.41/0.68    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 2.41/0.68    inference(cnf_transformation,[],[f44])).
% 2.41/0.68  fof(f81,plain,(
% 2.41/0.68    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 2.41/0.68    inference(avatar_split_clause,[],[f51,f78,f74,f70])).
% 2.41/0.68  fof(f51,plain,(
% 2.41/0.68    ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 2.41/0.68    inference(cnf_transformation,[],[f44])).
% 2.41/0.68  % SZS output end Proof for theBenchmark
% 2.41/0.68  % (16205)------------------------------
% 2.41/0.68  % (16205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.41/0.68  % (16205)Termination reason: Refutation
% 2.41/0.68  
% 2.41/0.68  % (16205)Memory used [KB]: 13688
% 2.41/0.68  % (16205)Time elapsed: 0.223 s
% 2.41/0.68  % (16205)------------------------------
% 2.41/0.68  % (16205)------------------------------
% 2.41/0.68  % (16198)Success in time 0.321 s
%------------------------------------------------------------------------------
