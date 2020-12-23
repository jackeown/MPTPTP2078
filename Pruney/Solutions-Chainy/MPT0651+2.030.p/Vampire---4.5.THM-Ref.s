%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 187 expanded)
%              Number of leaves         :   27 (  82 expanded)
%              Depth                    :    7
%              Number of atoms          :  349 ( 601 expanded)
%              Number of equality atoms :  115 ( 200 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f553,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f54,f59,f64,f71,f76,f85,f102,f115,f125,f160,f199,f223,f251,f273,f378,f520,f552])).

fof(f552,plain,
    ( spl1_2
    | ~ spl1_7
    | ~ spl1_27
    | ~ spl1_33 ),
    inference(avatar_contradiction_clause,[],[f551])).

fof(f551,plain,
    ( $false
    | spl1_2
    | ~ spl1_7
    | ~ spl1_27
    | ~ spl1_33 ),
    inference(subsumption_resolution,[],[f550,f48])).

fof(f48,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl1_2
  <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f550,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl1_7
    | ~ spl1_27
    | ~ spl1_33 ),
    inference(forward_demodulation,[],[f549,f75])).

fof(f75,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl1_7
  <=> k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f549,plain,
    ( k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k2_relat_1(k2_funct_1(sK0))
    | ~ spl1_27
    | ~ spl1_33 ),
    inference(forward_demodulation,[],[f548,f222])).

fof(f222,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0))
    | ~ spl1_27 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl1_27
  <=> k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_27])])).

fof(f548,plain,
    ( k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0)))
    | ~ spl1_33 ),
    inference(equality_resolution,[],[f272])).

fof(f272,plain,
    ( ! [X2] :
        ( k2_relat_1(sK0) != X2
        | k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k2_relat_1(k5_relat_1(k6_relat_1(X2),k2_funct_1(sK0))) )
    | ~ spl1_33 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl1_33
  <=> ! [X2] :
        ( k2_relat_1(sK0) != X2
        | k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k2_relat_1(k5_relat_1(k6_relat_1(X2),k2_funct_1(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_33])])).

fof(f520,plain,
    ( spl1_1
    | ~ spl1_14
    | ~ spl1_44 ),
    inference(avatar_split_clause,[],[f517,f376,f122,f42])).

fof(f42,plain,
    ( spl1_1
  <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f122,plain,
    ( spl1_14
  <=> sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f376,plain,
    ( spl1_44
  <=> ! [X2] :
        ( k2_relat_1(sK0) != X2
        | k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k1_relat_1(k5_relat_1(sK0,k6_relat_1(X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_44])])).

fof(f517,plain,
    ( k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl1_14
    | ~ spl1_44 ),
    inference(forward_demodulation,[],[f516,f124])).

fof(f124,plain,
    ( sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))
    | ~ spl1_14 ),
    inference(avatar_component_clause,[],[f122])).

fof(f516,plain,
    ( k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k1_relat_1(k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))))
    | ~ spl1_44 ),
    inference(equality_resolution,[],[f377])).

fof(f377,plain,
    ( ! [X2] :
        ( k2_relat_1(sK0) != X2
        | k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k1_relat_1(k5_relat_1(sK0,k6_relat_1(X2))) )
    | ~ spl1_44 ),
    inference(avatar_component_clause,[],[f376])).

fof(f378,plain,
    ( spl1_44
    | ~ spl1_6
    | ~ spl1_8
    | ~ spl1_30 ),
    inference(avatar_split_clause,[],[f374,f249,f82,f68,f376])).

fof(f68,plain,
    ( spl1_6
  <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f82,plain,
    ( spl1_8
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f249,plain,
    ( spl1_30
  <=> ! [X3,X4] :
        ( k1_relat_1(X4) != X3
        | ~ v1_relat_1(X4)
        | k1_relat_1(k5_relat_1(sK0,k6_relat_1(X3))) = k1_relat_1(k5_relat_1(sK0,X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_30])])).

fof(f374,plain,
    ( ! [X2] :
        ( k2_relat_1(sK0) != X2
        | k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k1_relat_1(k5_relat_1(sK0,k6_relat_1(X2))) )
    | ~ spl1_6
    | ~ spl1_8
    | ~ spl1_30 ),
    inference(forward_demodulation,[],[f371,f70])).

fof(f70,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f371,plain,
    ( ! [X2] :
        ( k1_relat_1(k2_funct_1(sK0)) != X2
        | k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k1_relat_1(k5_relat_1(sK0,k6_relat_1(X2))) )
    | ~ spl1_8
    | ~ spl1_30 ),
    inference(resolution,[],[f250,f84])).

fof(f84,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f82])).

fof(f250,plain,
    ( ! [X4,X3] :
        ( ~ v1_relat_1(X4)
        | k1_relat_1(X4) != X3
        | k1_relat_1(k5_relat_1(sK0,k6_relat_1(X3))) = k1_relat_1(k5_relat_1(sK0,X4)) )
    | ~ spl1_30 ),
    inference(avatar_component_clause,[],[f249])).

fof(f273,plain,
    ( spl1_33
    | ~ spl1_8
    | ~ spl1_23 ),
    inference(avatar_split_clause,[],[f267,f197,f82,f271])).

fof(f197,plain,
    ( spl1_23
  <=> ! [X3,X4] :
        ( k2_relat_1(sK0) != X3
        | ~ v1_relat_1(X4)
        | k2_relat_1(k5_relat_1(sK0,X4)) = k2_relat_1(k5_relat_1(k6_relat_1(X3),X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_23])])).

fof(f267,plain,
    ( ! [X2] :
        ( k2_relat_1(sK0) != X2
        | k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k2_relat_1(k5_relat_1(k6_relat_1(X2),k2_funct_1(sK0))) )
    | ~ spl1_8
    | ~ spl1_23 ),
    inference(resolution,[],[f198,f84])).

fof(f198,plain,
    ( ! [X4,X3] :
        ( ~ v1_relat_1(X4)
        | k2_relat_1(sK0) != X3
        | k2_relat_1(k5_relat_1(sK0,X4)) = k2_relat_1(k5_relat_1(k6_relat_1(X3),X4)) )
    | ~ spl1_23 ),
    inference(avatar_component_clause,[],[f197])).

fof(f251,plain,
    ( spl1_30
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f247,f113,f249])).

fof(f113,plain,
    ( spl1_12
  <=> ! [X11,X10] :
        ( k1_relat_1(k5_relat_1(sK0,X10)) = k1_relat_1(k5_relat_1(sK0,X11))
        | k1_relat_1(X10) != k1_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_relat_1(X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f247,plain,
    ( ! [X4,X3] :
        ( k1_relat_1(X4) != X3
        | ~ v1_relat_1(X4)
        | k1_relat_1(k5_relat_1(sK0,k6_relat_1(X3))) = k1_relat_1(k5_relat_1(sK0,X4)) )
    | ~ spl1_12 ),
    inference(forward_demodulation,[],[f240,f39])).

fof(f39,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f240,plain,
    ( ! [X4,X3] :
        ( k1_relat_1(k6_relat_1(X3)) != k1_relat_1(X4)
        | ~ v1_relat_1(X4)
        | k1_relat_1(k5_relat_1(sK0,k6_relat_1(X3))) = k1_relat_1(k5_relat_1(sK0,X4)) )
    | ~ spl1_12 ),
    inference(resolution,[],[f114,f35])).

fof(f35,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f114,plain,
    ( ! [X10,X11] :
        ( ~ v1_relat_1(X10)
        | k1_relat_1(X10) != k1_relat_1(X11)
        | ~ v1_relat_1(X11)
        | k1_relat_1(k5_relat_1(sK0,X10)) = k1_relat_1(k5_relat_1(sK0,X11)) )
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f113])).

fof(f223,plain,
    ( spl1_27
    | ~ spl1_6
    | ~ spl1_19 ),
    inference(avatar_split_clause,[],[f218,f157,f68,f220])).

fof(f157,plain,
    ( spl1_19
  <=> k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(sK0))),k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).

fof(f218,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0))
    | ~ spl1_6
    | ~ spl1_19 ),
    inference(forward_demodulation,[],[f159,f70])).

fof(f159,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(sK0))),k2_funct_1(sK0))
    | ~ spl1_19 ),
    inference(avatar_component_clause,[],[f157])).

fof(f199,plain,
    ( spl1_23
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f195,f99,f197])).

fof(f99,plain,
    ( spl1_9
  <=> ! [X1,X0] :
        ( k2_relat_1(k5_relat_1(sK0,X0)) = k2_relat_1(k5_relat_1(X1,X0))
        | k2_relat_1(X1) != k2_relat_1(sK0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f195,plain,
    ( ! [X4,X3] :
        ( k2_relat_1(sK0) != X3
        | ~ v1_relat_1(X4)
        | k2_relat_1(k5_relat_1(sK0,X4)) = k2_relat_1(k5_relat_1(k6_relat_1(X3),X4)) )
    | ~ spl1_9 ),
    inference(forward_demodulation,[],[f184,f40])).

fof(f40,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f184,plain,
    ( ! [X4,X3] :
        ( k2_relat_1(sK0) != k2_relat_1(k6_relat_1(X3))
        | ~ v1_relat_1(X4)
        | k2_relat_1(k5_relat_1(sK0,X4)) = k2_relat_1(k5_relat_1(k6_relat_1(X3),X4)) )
    | ~ spl1_9 ),
    inference(resolution,[],[f100,f35])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(X1) != k2_relat_1(sK0)
        | ~ v1_relat_1(X0)
        | k2_relat_1(k5_relat_1(sK0,X0)) = k2_relat_1(k5_relat_1(X1,X0)) )
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f99])).

fof(f160,plain,
    ( spl1_19
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f136,f82,f157])).

fof(f136,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(sK0))),k2_funct_1(sK0))
    | ~ spl1_8 ),
    inference(resolution,[],[f84,f37])).

fof(f37,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f125,plain,
    ( spl1_14
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f97,f61,f122])).

fof(f61,plain,
    ( spl1_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f97,plain,
    ( sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))
    | ~ spl1_5 ),
    inference(resolution,[],[f63,f38])).

fof(f38,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f63,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f115,plain,
    ( spl1_12
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f91,f61,f113])).

fof(f91,plain,
    ( ! [X10,X11] :
        ( k1_relat_1(k5_relat_1(sK0,X10)) = k1_relat_1(k5_relat_1(sK0,X11))
        | k1_relat_1(X10) != k1_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_relat_1(X10) )
    | ~ spl1_5 ),
    inference(resolution,[],[f63,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k1_relat_1(X0) = k1_relat_1(X1)
               => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_relat_1)).

fof(f102,plain,
    ( spl1_9
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f87,f61,f99])).

fof(f87,plain,
    ( ! [X2,X3] :
        ( k2_relat_1(k5_relat_1(X2,X3)) = k2_relat_1(k5_relat_1(sK0,X3))
        | k2_relat_1(sK0) != k2_relat_1(X2)
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X2) )
    | ~ spl1_5 ),
    inference(resolution,[],[f63,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
      | k2_relat_1(X0) != k2_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k2_relat_1(X0) = k2_relat_1(X1)
               => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_relat_1)).

fof(f85,plain,
    ( ~ spl1_5
    | spl1_8
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f79,f56,f82,f61])).

fof(f56,plain,
    ( spl1_4
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f79,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(resolution,[],[f58,f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f58,plain,
    ( v1_funct_1(sK0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f76,plain,
    ( ~ spl1_5
    | ~ spl1_4
    | spl1_7
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f66,f51,f73,f56,f61])).

fof(f51,plain,
    ( spl1_3
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f66,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_3 ),
    inference(resolution,[],[f53,f34])).

fof(f34,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f53,plain,
    ( v2_funct_1(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f71,plain,
    ( ~ spl1_5
    | ~ spl1_4
    | spl1_6
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f65,f51,f68,f56,f61])).

fof(f65,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_3 ),
    inference(resolution,[],[f53,f33])).

fof(f33,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f64,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f25,f61])).

fof(f25,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
      | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
        | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
            & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

fof(f59,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f26,f56])).

fof(f26,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f27,f51])).

fof(f27,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f28,f46,f42])).

fof(f28,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:26:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (20021)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.49  % (20008)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.49  % (20018)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.49  % (20011)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.49  % (20015)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.49  % (20013)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (20016)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.50  % (20014)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.50  % (20007)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.50  % (20009)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  % (20009)Refutation not found, incomplete strategy% (20009)------------------------------
% 0.21/0.50  % (20009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (20009)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (20009)Memory used [KB]: 10490
% 0.21/0.50  % (20009)Time elapsed: 0.086 s
% 0.21/0.50  % (20009)------------------------------
% 0.21/0.50  % (20009)------------------------------
% 0.21/0.50  % (20028)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.50  % (20023)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.50  % (20006)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (20020)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.51  % (20013)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f553,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f49,f54,f59,f64,f71,f76,f85,f102,f115,f125,f160,f199,f223,f251,f273,f378,f520,f552])).
% 0.21/0.51  fof(f552,plain,(
% 0.21/0.51    spl1_2 | ~spl1_7 | ~spl1_27 | ~spl1_33),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f551])).
% 0.21/0.51  fof(f551,plain,(
% 0.21/0.51    $false | (spl1_2 | ~spl1_7 | ~spl1_27 | ~spl1_33)),
% 0.21/0.51    inference(subsumption_resolution,[],[f550,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | spl1_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    spl1_2 <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.51  fof(f550,plain,(
% 0.21/0.51    k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | (~spl1_7 | ~spl1_27 | ~spl1_33)),
% 0.21/0.51    inference(forward_demodulation,[],[f549,f75])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~spl1_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    spl1_7 <=> k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.21/0.51  fof(f549,plain,(
% 0.21/0.51    k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k2_relat_1(k2_funct_1(sK0)) | (~spl1_27 | ~spl1_33)),
% 0.21/0.51    inference(forward_demodulation,[],[f548,f222])).
% 0.21/0.51  fof(f222,plain,(
% 0.21/0.51    k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0)) | ~spl1_27),
% 0.21/0.51    inference(avatar_component_clause,[],[f220])).
% 0.21/0.51  fof(f220,plain,(
% 0.21/0.51    spl1_27 <=> k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_27])])).
% 0.21/0.51  fof(f548,plain,(
% 0.21/0.51    k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0))) | ~spl1_33),
% 0.21/0.51    inference(equality_resolution,[],[f272])).
% 0.21/0.51  fof(f272,plain,(
% 0.21/0.51    ( ! [X2] : (k2_relat_1(sK0) != X2 | k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k2_relat_1(k5_relat_1(k6_relat_1(X2),k2_funct_1(sK0)))) ) | ~spl1_33),
% 0.21/0.51    inference(avatar_component_clause,[],[f271])).
% 0.21/0.51  fof(f271,plain,(
% 0.21/0.51    spl1_33 <=> ! [X2] : (k2_relat_1(sK0) != X2 | k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k2_relat_1(k5_relat_1(k6_relat_1(X2),k2_funct_1(sK0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_33])])).
% 0.21/0.51  fof(f520,plain,(
% 0.21/0.51    spl1_1 | ~spl1_14 | ~spl1_44),
% 0.21/0.51    inference(avatar_split_clause,[],[f517,f376,f122,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    spl1_1 <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    spl1_14 <=> sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.21/0.51  fof(f376,plain,(
% 0.21/0.51    spl1_44 <=> ! [X2] : (k2_relat_1(sK0) != X2 | k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k1_relat_1(k5_relat_1(sK0,k6_relat_1(X2))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_44])])).
% 0.21/0.51  fof(f517,plain,(
% 0.21/0.51    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | (~spl1_14 | ~spl1_44)),
% 0.21/0.51    inference(forward_demodulation,[],[f516,f124])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) | ~spl1_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f122])).
% 0.21/0.51  fof(f516,plain,(
% 0.21/0.51    k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k1_relat_1(k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))) | ~spl1_44),
% 0.21/0.51    inference(equality_resolution,[],[f377])).
% 0.21/0.51  fof(f377,plain,(
% 0.21/0.51    ( ! [X2] : (k2_relat_1(sK0) != X2 | k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k1_relat_1(k5_relat_1(sK0,k6_relat_1(X2)))) ) | ~spl1_44),
% 0.21/0.51    inference(avatar_component_clause,[],[f376])).
% 0.21/0.51  fof(f378,plain,(
% 0.21/0.51    spl1_44 | ~spl1_6 | ~spl1_8 | ~spl1_30),
% 0.21/0.51    inference(avatar_split_clause,[],[f374,f249,f82,f68,f376])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    spl1_6 <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    spl1_8 <=> v1_relat_1(k2_funct_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.21/0.51  fof(f249,plain,(
% 0.21/0.51    spl1_30 <=> ! [X3,X4] : (k1_relat_1(X4) != X3 | ~v1_relat_1(X4) | k1_relat_1(k5_relat_1(sK0,k6_relat_1(X3))) = k1_relat_1(k5_relat_1(sK0,X4)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_30])])).
% 0.21/0.51  fof(f374,plain,(
% 0.21/0.51    ( ! [X2] : (k2_relat_1(sK0) != X2 | k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k1_relat_1(k5_relat_1(sK0,k6_relat_1(X2)))) ) | (~spl1_6 | ~spl1_8 | ~spl1_30)),
% 0.21/0.51    inference(forward_demodulation,[],[f371,f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~spl1_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f68])).
% 0.21/0.51  fof(f371,plain,(
% 0.21/0.51    ( ! [X2] : (k1_relat_1(k2_funct_1(sK0)) != X2 | k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k1_relat_1(k5_relat_1(sK0,k6_relat_1(X2)))) ) | (~spl1_8 | ~spl1_30)),
% 0.21/0.51    inference(resolution,[],[f250,f84])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    v1_relat_1(k2_funct_1(sK0)) | ~spl1_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f82])).
% 0.21/0.51  fof(f250,plain,(
% 0.21/0.51    ( ! [X4,X3] : (~v1_relat_1(X4) | k1_relat_1(X4) != X3 | k1_relat_1(k5_relat_1(sK0,k6_relat_1(X3))) = k1_relat_1(k5_relat_1(sK0,X4))) ) | ~spl1_30),
% 0.21/0.51    inference(avatar_component_clause,[],[f249])).
% 0.21/0.51  fof(f273,plain,(
% 0.21/0.51    spl1_33 | ~spl1_8 | ~spl1_23),
% 0.21/0.51    inference(avatar_split_clause,[],[f267,f197,f82,f271])).
% 0.21/0.51  fof(f197,plain,(
% 0.21/0.51    spl1_23 <=> ! [X3,X4] : (k2_relat_1(sK0) != X3 | ~v1_relat_1(X4) | k2_relat_1(k5_relat_1(sK0,X4)) = k2_relat_1(k5_relat_1(k6_relat_1(X3),X4)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_23])])).
% 0.21/0.51  fof(f267,plain,(
% 0.21/0.51    ( ! [X2] : (k2_relat_1(sK0) != X2 | k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k2_relat_1(k5_relat_1(k6_relat_1(X2),k2_funct_1(sK0)))) ) | (~spl1_8 | ~spl1_23)),
% 0.21/0.51    inference(resolution,[],[f198,f84])).
% 0.21/0.51  fof(f198,plain,(
% 0.21/0.51    ( ! [X4,X3] : (~v1_relat_1(X4) | k2_relat_1(sK0) != X3 | k2_relat_1(k5_relat_1(sK0,X4)) = k2_relat_1(k5_relat_1(k6_relat_1(X3),X4))) ) | ~spl1_23),
% 0.21/0.51    inference(avatar_component_clause,[],[f197])).
% 0.21/0.51  fof(f251,plain,(
% 0.21/0.51    spl1_30 | ~spl1_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f247,f113,f249])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    spl1_12 <=> ! [X11,X10] : (k1_relat_1(k5_relat_1(sK0,X10)) = k1_relat_1(k5_relat_1(sK0,X11)) | k1_relat_1(X10) != k1_relat_1(X11) | ~v1_relat_1(X11) | ~v1_relat_1(X10))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.21/0.51  fof(f247,plain,(
% 0.21/0.51    ( ! [X4,X3] : (k1_relat_1(X4) != X3 | ~v1_relat_1(X4) | k1_relat_1(k5_relat_1(sK0,k6_relat_1(X3))) = k1_relat_1(k5_relat_1(sK0,X4))) ) | ~spl1_12),
% 0.21/0.51    inference(forward_demodulation,[],[f240,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.51  fof(f240,plain,(
% 0.21/0.51    ( ! [X4,X3] : (k1_relat_1(k6_relat_1(X3)) != k1_relat_1(X4) | ~v1_relat_1(X4) | k1_relat_1(k5_relat_1(sK0,k6_relat_1(X3))) = k1_relat_1(k5_relat_1(sK0,X4))) ) | ~spl1_12),
% 0.21/0.51    inference(resolution,[],[f114,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    ( ! [X10,X11] : (~v1_relat_1(X10) | k1_relat_1(X10) != k1_relat_1(X11) | ~v1_relat_1(X11) | k1_relat_1(k5_relat_1(sK0,X10)) = k1_relat_1(k5_relat_1(sK0,X11))) ) | ~spl1_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f113])).
% 0.21/0.51  fof(f223,plain,(
% 0.21/0.51    spl1_27 | ~spl1_6 | ~spl1_19),
% 0.21/0.51    inference(avatar_split_clause,[],[f218,f157,f68,f220])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    spl1_19 <=> k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(sK0))),k2_funct_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).
% 0.21/0.51  fof(f218,plain,(
% 0.21/0.51    k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0)) | (~spl1_6 | ~spl1_19)),
% 0.21/0.51    inference(forward_demodulation,[],[f159,f70])).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(sK0))),k2_funct_1(sK0)) | ~spl1_19),
% 0.21/0.51    inference(avatar_component_clause,[],[f157])).
% 0.21/0.51  fof(f199,plain,(
% 0.21/0.51    spl1_23 | ~spl1_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f195,f99,f197])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    spl1_9 <=> ! [X1,X0] : (k2_relat_1(k5_relat_1(sK0,X0)) = k2_relat_1(k5_relat_1(X1,X0)) | k2_relat_1(X1) != k2_relat_1(sK0) | ~v1_relat_1(X0) | ~v1_relat_1(X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    ( ! [X4,X3] : (k2_relat_1(sK0) != X3 | ~v1_relat_1(X4) | k2_relat_1(k5_relat_1(sK0,X4)) = k2_relat_1(k5_relat_1(k6_relat_1(X3),X4))) ) | ~spl1_9),
% 0.21/0.51    inference(forward_demodulation,[],[f184,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f184,plain,(
% 0.21/0.51    ( ! [X4,X3] : (k2_relat_1(sK0) != k2_relat_1(k6_relat_1(X3)) | ~v1_relat_1(X4) | k2_relat_1(k5_relat_1(sK0,X4)) = k2_relat_1(k5_relat_1(k6_relat_1(X3),X4))) ) | ~spl1_9),
% 0.21/0.51    inference(resolution,[],[f100,f35])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(X1) != k2_relat_1(sK0) | ~v1_relat_1(X0) | k2_relat_1(k5_relat_1(sK0,X0)) = k2_relat_1(k5_relat_1(X1,X0))) ) | ~spl1_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f99])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    spl1_19 | ~spl1_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f136,f82,f157])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(sK0))),k2_funct_1(sK0)) | ~spl1_8),
% 0.21/0.51    inference(resolution,[],[f84,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    spl1_14 | ~spl1_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f97,f61,f122])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    spl1_5 <=> v1_relat_1(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) | ~spl1_5),
% 0.21/0.51    inference(resolution,[],[f63,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    v1_relat_1(sK0) | ~spl1_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f61])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    spl1_12 | ~spl1_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f91,f61,f113])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    ( ! [X10,X11] : (k1_relat_1(k5_relat_1(sK0,X10)) = k1_relat_1(k5_relat_1(sK0,X11)) | k1_relat_1(X10) != k1_relat_1(X11) | ~v1_relat_1(X11) | ~v1_relat_1(X10)) ) | ~spl1_5),
% 0.21/0.51    inference(resolution,[],[f63,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k1_relat_1(X0) = k1_relat_1(X1) => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_relat_1)).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    spl1_9 | ~spl1_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f87,f61,f99])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X2,X3] : (k2_relat_1(k5_relat_1(X2,X3)) = k2_relat_1(k5_relat_1(sK0,X3)) | k2_relat_1(sK0) != k2_relat_1(X2) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) ) | ~spl1_5),
% 0.21/0.51    inference(resolution,[],[f63,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k2_relat_1(X0) = k2_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_relat_1)).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ~spl1_5 | spl1_8 | ~spl1_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f79,f56,f82,f61])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    spl1_4 <=> v1_funct_1(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | ~spl1_4),
% 0.21/0.51    inference(resolution,[],[f58,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    v1_funct_1(sK0) | ~spl1_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f56])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ~spl1_5 | ~spl1_4 | spl1_7 | ~spl1_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f66,f51,f73,f56,f61])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    spl1_3 <=> v2_funct_1(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_3),
% 0.21/0.51    inference(resolution,[],[f53,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    v2_funct_1(sK0) | ~spl1_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f51])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ~spl1_5 | ~spl1_4 | spl1_6 | ~spl1_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f65,f51,f68,f56,f61])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_3),
% 0.21/0.51    inference(resolution,[],[f53,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    spl1_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f25,f61])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    v1_relat_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    (k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0] : (((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f9])).
% 0.21/0.51  fof(f9,conjecture,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    spl1_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f26,f56])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    v1_funct_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    spl1_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f27,f51])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    v2_funct_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ~spl1_1 | ~spl1_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f28,f46,f42])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (20013)------------------------------
% 0.21/0.51  % (20013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (20013)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (20013)Memory used [KB]: 6396
% 0.21/0.51  % (20013)Time elapsed: 0.095 s
% 0.21/0.51  % (20013)------------------------------
% 0.21/0.51  % (20013)------------------------------
% 0.21/0.51  % (20027)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.51  % (20026)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.51  % (20005)Success in time 0.155 s
%------------------------------------------------------------------------------
