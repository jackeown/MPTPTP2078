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
% DateTime   : Thu Dec  3 12:52:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 250 expanded)
%              Number of leaves         :   18 (  66 expanded)
%              Depth                    :   16
%              Number of atoms          :  365 (1371 expanded)
%              Number of equality atoms :   88 ( 463 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f844,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f118,f122,f131,f177,f251,f294,f335,f438,f447,f824,f843])).

fof(f843,plain,(
    ~ spl13_16 ),
    inference(avatar_contradiction_clause,[],[f836])).

fof(f836,plain,
    ( $false
    | ~ spl13_16 ),
    inference(unit_resulting_resolution,[],[f28,f250])).

fof(f250,plain,
    ( sK2 = k6_relat_1(sK0)
    | ~ spl13_16 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl13_16
  <=> sK2 = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_16])])).

fof(f28,plain,(
    sK2 != k6_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( ( k5_relat_1(X2,X1) = X1
                & v2_funct_1(X1)
                & r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X0
                & k1_relat_1(X1) = X0 )
             => k6_relat_1(X0) = X2 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( k5_relat_1(X2,X1) = X1
              & v2_funct_1(X1)
              & r1_tarski(k2_relat_1(X2),X0)
              & k1_relat_1(X2) = X0
              & k1_relat_1(X1) = X0 )
           => k6_relat_1(X0) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_1)).

fof(f824,plain,
    ( ~ spl13_6
    | ~ spl13_14
    | spl13_18
    | ~ spl13_20
    | ~ spl13_22 ),
    inference(avatar_contradiction_clause,[],[f823])).

fof(f823,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_14
    | spl13_18
    | ~ spl13_20
    | ~ spl13_22 ),
    inference(trivial_inequality_removal,[],[f818])).

fof(f818,plain,
    ( k1_funct_1(sK1,sK3(sK0,sK2)) != k1_funct_1(sK1,sK3(sK0,sK2))
    | ~ spl13_6
    | ~ spl13_14
    | spl13_18
    | ~ spl13_20
    | ~ spl13_22 ),
    inference(backward_demodulation,[],[f465,f796])).

fof(f796,plain,
    ( sK3(sK0,sK2) = k1_funct_1(sK2,sK3(sK0,sK2))
    | ~ spl13_6
    | ~ spl13_14
    | ~ spl13_20
    | ~ spl13_22 ),
    inference(unit_resulting_resolution,[],[f236,f407,f396,f437])).

fof(f437,plain,
    ( ! [X6,X5] :
        ( k1_funct_1(sK1,X5) != k1_funct_1(sK1,X6)
        | X5 = X6
        | ~ r2_hidden(X5,sK0)
        | ~ r2_hidden(X6,sK0) )
    | ~ spl13_22 ),
    inference(avatar_component_clause,[],[f436])).

fof(f436,plain,
    ( spl13_22
  <=> ! [X5,X6] :
        ( ~ r2_hidden(X6,sK0)
        | X5 = X6
        | ~ r2_hidden(X5,sK0)
        | k1_funct_1(sK1,X5) != k1_funct_1(sK1,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_22])])).

fof(f396,plain,
    ( k1_funct_1(sK1,sK3(sK0,sK2)) = k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2)))
    | ~ spl13_14
    | ~ spl13_20 ),
    inference(forward_demodulation,[],[f375,f27])).

fof(f27,plain,(
    sK1 = k5_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f375,plain,
    ( k1_funct_1(k5_relat_1(sK2,sK1),sK3(sK0,sK2)) = k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2)))
    | ~ spl13_14
    | ~ spl13_20 ),
    inference(unit_resulting_resolution,[],[f30,f29,f236,f334])).

fof(f334,plain,
    ( ! [X8,X7] :
        ( ~ v1_funct_1(X7)
        | k1_funct_1(k5_relat_1(sK2,X7),X8) = k1_funct_1(X7,k1_funct_1(sK2,X8))
        | ~ v1_relat_1(X7)
        | ~ r2_hidden(X8,sK0) )
    | ~ spl13_20 ),
    inference(avatar_component_clause,[],[f333])).

fof(f333,plain,
    ( spl13_20
  <=> ! [X7,X8] :
        ( ~ r2_hidden(X8,sK0)
        | k1_funct_1(k5_relat_1(sK2,X7),X8) = k1_funct_1(X7,k1_funct_1(sK2,X8))
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_20])])).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f30,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f407,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),sK0)
    | ~ spl13_6
    | ~ spl13_14 ),
    inference(unit_resulting_resolution,[],[f25,f364,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f364,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),k2_relat_1(sK2))
    | ~ spl13_6
    | ~ spl13_14 ),
    inference(unit_resulting_resolution,[],[f254,f60])).

fof(f60,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X2,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X3,X2),X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f254,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,sK2),k1_funct_1(sK2,sK3(sK0,sK2))),sK2)
    | ~ spl13_6
    | ~ spl13_14 ),
    inference(unit_resulting_resolution,[],[f236,f142])).

fof(f142,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl13_6 ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl13_6 ),
    inference(forward_demodulation,[],[f140,f24])).

fof(f24,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f140,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2)
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ r2_hidden(X0,sK0) )
    | ~ spl13_6 ),
    inference(superposition,[],[f62,f138])).

fof(f138,plain,
    ( ! [X3] :
        ( k1_funct_1(sK2,X3) = sK11(sK2,X3)
        | ~ r2_hidden(X3,sK0) )
    | ~ spl13_6 ),
    inference(forward_demodulation,[],[f135,f24])).

fof(f135,plain,
    ( ! [X3] :
        ( k1_funct_1(sK2,X3) = sK11(sK2,X3)
        | ~ r2_hidden(X3,k1_relat_1(sK2)) )
    | ~ spl13_6 ),
    inference(resolution,[],[f130,f62])).

fof(f130,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK2)
        | k1_funct_1(sK2,X2) = X3 )
    | ~ spl13_6 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl13_6
  <=> ! [X3,X2] :
        ( k1_funct_1(sK2,X2) = X3
        | ~ r2_hidden(k4_tarski(X2,X3),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f62,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK11(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK11(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f25,plain,(
    r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f236,plain,
    ( r2_hidden(sK3(sK0,sK2),sK0)
    | ~ spl13_14 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl13_14
  <=> r2_hidden(sK3(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).

fof(f465,plain,
    ( k1_funct_1(sK1,sK3(sK0,sK2)) != k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2)))
    | ~ spl13_6
    | ~ spl13_14
    | spl13_18
    | ~ spl13_22 ),
    inference(unit_resulting_resolution,[],[f407,f293,f236,f437])).

fof(f293,plain,
    ( sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2))
    | spl13_18 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl13_18
  <=> sK3(sK0,sK2) = k1_funct_1(sK2,sK3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).

fof(f447,plain,(
    spl13_21 ),
    inference(avatar_contradiction_clause,[],[f439])).

fof(f439,plain,
    ( $false
    | spl13_21 ),
    inference(unit_resulting_resolution,[],[f26,f434])).

fof(f434,plain,
    ( ~ v2_funct_1(sK1)
    | spl13_21 ),
    inference(avatar_component_clause,[],[f432])).

fof(f432,plain,
    ( spl13_21
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_21])])).

fof(f26,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f438,plain,
    ( ~ spl13_21
    | ~ spl13_9
    | spl13_22 ),
    inference(avatar_split_clause,[],[f80,f436,f170,f432])).

fof(f170,plain,
    ( spl13_9
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).

fof(f80,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X6,sK0)
      | ~ r2_hidden(X5,sK0)
      | ~ v1_relat_1(sK1)
      | k1_funct_1(sK1,X5) != k1_funct_1(sK1,X6)
      | X5 = X6
      | ~ v2_funct_1(sK1) ) ),
    inference(forward_demodulation,[],[f79,f23])).

fof(f23,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f79,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,sK0)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X6,k1_relat_1(sK1))
      | k1_funct_1(sK1,X5) != k1_funct_1(sK1,X6)
      | X5 = X6
      | ~ v2_funct_1(sK1) ) ),
    inference(forward_demodulation,[],[f76,f23])).

fof(f76,plain,(
    ! [X6,X5] :
      ( ~ v1_relat_1(sK1)
      | ~ r2_hidden(X5,k1_relat_1(sK1))
      | ~ r2_hidden(X6,k1_relat_1(sK1))
      | k1_funct_1(sK1,X5) != k1_funct_1(sK1,X6)
      | X5 = X6
      | ~ v2_funct_1(sK1) ) ),
    inference(resolution,[],[f30,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
      | X1 = X2
      | ~ v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(f335,plain,
    ( ~ spl13_2
    | spl13_20 ),
    inference(avatar_split_clause,[],[f72,f333,f103])).

fof(f103,plain,
    ( spl13_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f72,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(X8,sK0)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X7)
      | ~ v1_funct_1(X7)
      | k1_funct_1(k5_relat_1(sK2,X7),X8) = k1_funct_1(X7,k1_funct_1(sK2,X8)) ) ),
    inference(forward_demodulation,[],[f68,f24])).

fof(f68,plain,(
    ! [X8,X7] :
      ( ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X7)
      | ~ v1_funct_1(X7)
      | ~ r2_hidden(X8,k1_relat_1(sK2))
      | k1_funct_1(k5_relat_1(sK2,X7),X8) = k1_funct_1(X7,k1_funct_1(sK2,X8)) ) ),
    inference(resolution,[],[f22,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

fof(f22,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f294,plain,
    ( spl13_16
    | ~ spl13_2
    | ~ spl13_3
    | ~ spl13_18 ),
    inference(avatar_split_clause,[],[f91,f291,f107,f103,f248])).

fof(f107,plain,
    ( spl13_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f91,plain,
    ( sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = k6_relat_1(sK0) ),
    inference(superposition,[],[f57,f24])).

fof(f57,plain,(
    ! [X1] :
      ( sK3(k1_relat_1(X1),X1) != k1_funct_1(X1,sK3(k1_relat_1(X1),X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1))
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

fof(f251,plain,
    ( spl13_16
    | ~ spl13_2
    | ~ spl13_3
    | spl13_14 ),
    inference(avatar_split_clause,[],[f90,f234,f107,f103,f248])).

fof(f90,plain,
    ( r2_hidden(sK3(sK0,sK2),sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = k6_relat_1(sK0) ),
    inference(superposition,[],[f58,f24])).

fof(f58,plain,(
    ! [X1] :
      ( r2_hidden(sK3(k1_relat_1(X1),X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | r2_hidden(sK3(X0,X1),X0)
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f177,plain,(
    spl13_9 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | spl13_9 ),
    inference(unit_resulting_resolution,[],[f29,f172])).

fof(f172,plain,
    ( ~ v1_relat_1(sK1)
    | spl13_9 ),
    inference(avatar_component_clause,[],[f170])).

fof(f131,plain,
    ( spl13_6
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f65,f103,f129])).

fof(f65,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(sK2)
      | k1_funct_1(sK2,X2) = X3
      | ~ r2_hidden(k4_tarski(X2,X3),sK2) ) ),
    inference(resolution,[],[f22,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f122,plain,(
    spl13_3 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl13_3 ),
    inference(unit_resulting_resolution,[],[f22,f109])).

fof(f109,plain,
    ( ~ v1_funct_1(sK2)
    | spl13_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f118,plain,(
    spl13_2 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl13_2 ),
    inference(unit_resulting_resolution,[],[f21,f105])).

fof(f105,plain,
    ( ~ v1_relat_1(sK2)
    | spl13_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:12:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (12386)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.48  % (12378)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.49  % (12374)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (12375)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (12376)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (12400)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.51  % (12377)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (12383)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (12394)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (12372)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (12384)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (12385)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (12388)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (12373)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (12395)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (12397)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (12371)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (12401)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (12389)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (12399)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (12402)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (12393)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (12380)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (12391)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (12390)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (12379)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (12392)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.56  % (12396)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.56  % (12375)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f844,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f118,f122,f131,f177,f251,f294,f335,f438,f447,f824,f843])).
% 0.21/0.56  fof(f843,plain,(
% 0.21/0.56    ~spl13_16),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f836])).
% 0.21/0.56  fof(f836,plain,(
% 0.21/0.56    $false | ~spl13_16),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f28,f250])).
% 0.21/0.56  fof(f250,plain,(
% 0.21/0.56    sK2 = k6_relat_1(sK0) | ~spl13_16),
% 0.21/0.56    inference(avatar_component_clause,[],[f248])).
% 0.21/0.56  fof(f248,plain,(
% 0.21/0.56    spl13_16 <=> sK2 = k6_relat_1(sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_16])])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    sK2 != k6_relat_1(sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,plain,(
% 0.21/0.56    ? [X0,X1] : (? [X2] : (k6_relat_1(X0) != X2 & k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.56    inference(flattening,[],[f10])).
% 0.21/0.56  fof(f10,plain,(
% 0.21/0.56    ? [X0,X1] : (? [X2] : ((k6_relat_1(X0) != X2 & (k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0)) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.56    inference(ennf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 0.21/0.56    inference(negated_conjecture,[],[f8])).
% 0.21/0.56  fof(f8,conjecture,(
% 0.21/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_1)).
% 0.21/0.56  fof(f824,plain,(
% 0.21/0.56    ~spl13_6 | ~spl13_14 | spl13_18 | ~spl13_20 | ~spl13_22),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f823])).
% 0.21/0.56  fof(f823,plain,(
% 0.21/0.56    $false | (~spl13_6 | ~spl13_14 | spl13_18 | ~spl13_20 | ~spl13_22)),
% 0.21/0.56    inference(trivial_inequality_removal,[],[f818])).
% 0.21/0.56  fof(f818,plain,(
% 0.21/0.56    k1_funct_1(sK1,sK3(sK0,sK2)) != k1_funct_1(sK1,sK3(sK0,sK2)) | (~spl13_6 | ~spl13_14 | spl13_18 | ~spl13_20 | ~spl13_22)),
% 0.21/0.56    inference(backward_demodulation,[],[f465,f796])).
% 0.21/0.56  fof(f796,plain,(
% 0.21/0.56    sK3(sK0,sK2) = k1_funct_1(sK2,sK3(sK0,sK2)) | (~spl13_6 | ~spl13_14 | ~spl13_20 | ~spl13_22)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f236,f407,f396,f437])).
% 0.21/0.56  fof(f437,plain,(
% 0.21/0.56    ( ! [X6,X5] : (k1_funct_1(sK1,X5) != k1_funct_1(sK1,X6) | X5 = X6 | ~r2_hidden(X5,sK0) | ~r2_hidden(X6,sK0)) ) | ~spl13_22),
% 0.21/0.56    inference(avatar_component_clause,[],[f436])).
% 0.21/0.56  fof(f436,plain,(
% 0.21/0.56    spl13_22 <=> ! [X5,X6] : (~r2_hidden(X6,sK0) | X5 = X6 | ~r2_hidden(X5,sK0) | k1_funct_1(sK1,X5) != k1_funct_1(sK1,X6))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_22])])).
% 0.21/0.56  fof(f396,plain,(
% 0.21/0.56    k1_funct_1(sK1,sK3(sK0,sK2)) = k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2))) | (~spl13_14 | ~spl13_20)),
% 0.21/0.56    inference(forward_demodulation,[],[f375,f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    sK1 = k5_relat_1(sK2,sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f11])).
% 0.21/0.56  fof(f375,plain,(
% 0.21/0.56    k1_funct_1(k5_relat_1(sK2,sK1),sK3(sK0,sK2)) = k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2))) | (~spl13_14 | ~spl13_20)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f30,f29,f236,f334])).
% 0.21/0.56  fof(f334,plain,(
% 0.21/0.56    ( ! [X8,X7] : (~v1_funct_1(X7) | k1_funct_1(k5_relat_1(sK2,X7),X8) = k1_funct_1(X7,k1_funct_1(sK2,X8)) | ~v1_relat_1(X7) | ~r2_hidden(X8,sK0)) ) | ~spl13_20),
% 0.21/0.56    inference(avatar_component_clause,[],[f333])).
% 0.21/0.56  fof(f333,plain,(
% 0.21/0.56    spl13_20 <=> ! [X7,X8] : (~r2_hidden(X8,sK0) | k1_funct_1(k5_relat_1(sK2,X7),X8) = k1_funct_1(X7,k1_funct_1(sK2,X8)) | ~v1_relat_1(X7) | ~v1_funct_1(X7))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_20])])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    v1_relat_1(sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f11])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    v1_funct_1(sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f11])).
% 0.21/0.56  fof(f407,plain,(
% 0.21/0.56    r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),sK0) | (~spl13_6 | ~spl13_14)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f25,f364,f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.56  fof(f364,plain,(
% 0.21/0.56    r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),k2_relat_1(sK2)) | (~spl13_6 | ~spl13_14)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f254,f60])).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    ( ! [X2,X0,X3] : (r2_hidden(X2,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X3,X2),X0)) )),
% 0.21/0.56    inference(equality_resolution,[],[f44])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.21/0.56  fof(f254,plain,(
% 0.21/0.56    r2_hidden(k4_tarski(sK3(sK0,sK2),k1_funct_1(sK2,sK3(sK0,sK2))),sK2) | (~spl13_6 | ~spl13_14)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f236,f142])).
% 0.21/0.56  fof(f142,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2) | ~r2_hidden(X0,sK0)) ) | ~spl13_6),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f141])).
% 0.21/0.56  fof(f141,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2) | ~r2_hidden(X0,sK0)) ) | ~spl13_6),
% 0.21/0.56    inference(forward_demodulation,[],[f140,f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    sK0 = k1_relat_1(sK2)),
% 0.21/0.56    inference(cnf_transformation,[],[f11])).
% 0.21/0.56  fof(f140,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2) | ~r2_hidden(X0,k1_relat_1(sK2)) | ~r2_hidden(X0,sK0)) ) | ~spl13_6),
% 0.21/0.56    inference(superposition,[],[f62,f138])).
% 0.21/0.56  fof(f138,plain,(
% 0.21/0.56    ( ! [X3] : (k1_funct_1(sK2,X3) = sK11(sK2,X3) | ~r2_hidden(X3,sK0)) ) | ~spl13_6),
% 0.21/0.56    inference(forward_demodulation,[],[f135,f24])).
% 0.21/0.56  fof(f135,plain,(
% 0.21/0.56    ( ! [X3] : (k1_funct_1(sK2,X3) = sK11(sK2,X3) | ~r2_hidden(X3,k1_relat_1(sK2))) ) | ~spl13_6),
% 0.21/0.56    inference(resolution,[],[f130,f62])).
% 0.21/0.56  fof(f130,plain,(
% 0.21/0.56    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK2) | k1_funct_1(sK2,X2) = X3) ) | ~spl13_6),
% 0.21/0.56    inference(avatar_component_clause,[],[f129])).
% 0.21/0.56  fof(f129,plain,(
% 0.21/0.56    spl13_6 <=> ! [X3,X2] : (k1_funct_1(sK2,X2) = X3 | ~r2_hidden(k4_tarski(X2,X3),sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK11(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0))) )),
% 0.21/0.56    inference(equality_resolution,[],[f52])).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK11(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    r1_tarski(k2_relat_1(sK2),sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f11])).
% 0.21/0.56  fof(f236,plain,(
% 0.21/0.56    r2_hidden(sK3(sK0,sK2),sK0) | ~spl13_14),
% 0.21/0.56    inference(avatar_component_clause,[],[f234])).
% 0.21/0.56  fof(f234,plain,(
% 0.21/0.56    spl13_14 <=> r2_hidden(sK3(sK0,sK2),sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).
% 0.21/0.56  fof(f465,plain,(
% 0.21/0.56    k1_funct_1(sK1,sK3(sK0,sK2)) != k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2))) | (~spl13_6 | ~spl13_14 | spl13_18 | ~spl13_22)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f407,f293,f236,f437])).
% 0.21/0.56  fof(f293,plain,(
% 0.21/0.56    sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2)) | spl13_18),
% 0.21/0.56    inference(avatar_component_clause,[],[f291])).
% 0.21/0.56  fof(f291,plain,(
% 0.21/0.56    spl13_18 <=> sK3(sK0,sK2) = k1_funct_1(sK2,sK3(sK0,sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).
% 0.21/0.56  fof(f447,plain,(
% 0.21/0.56    spl13_21),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f439])).
% 0.21/0.56  fof(f439,plain,(
% 0.21/0.56    $false | spl13_21),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f26,f434])).
% 0.21/0.56  fof(f434,plain,(
% 0.21/0.56    ~v2_funct_1(sK1) | spl13_21),
% 0.21/0.56    inference(avatar_component_clause,[],[f432])).
% 0.21/0.56  fof(f432,plain,(
% 0.21/0.56    spl13_21 <=> v2_funct_1(sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_21])])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    v2_funct_1(sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f11])).
% 0.21/0.56  fof(f438,plain,(
% 0.21/0.56    ~spl13_21 | ~spl13_9 | spl13_22),
% 0.21/0.56    inference(avatar_split_clause,[],[f80,f436,f170,f432])).
% 0.21/0.56  fof(f170,plain,(
% 0.21/0.56    spl13_9 <=> v1_relat_1(sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).
% 0.21/0.56  fof(f80,plain,(
% 0.21/0.56    ( ! [X6,X5] : (~r2_hidden(X6,sK0) | ~r2_hidden(X5,sK0) | ~v1_relat_1(sK1) | k1_funct_1(sK1,X5) != k1_funct_1(sK1,X6) | X5 = X6 | ~v2_funct_1(sK1)) )),
% 0.21/0.56    inference(forward_demodulation,[],[f79,f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    sK0 = k1_relat_1(sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f11])).
% 0.21/0.56  fof(f79,plain,(
% 0.21/0.56    ( ! [X6,X5] : (~r2_hidden(X5,sK0) | ~v1_relat_1(sK1) | ~r2_hidden(X6,k1_relat_1(sK1)) | k1_funct_1(sK1,X5) != k1_funct_1(sK1,X6) | X5 = X6 | ~v2_funct_1(sK1)) )),
% 0.21/0.56    inference(forward_demodulation,[],[f76,f23])).
% 0.21/0.56  fof(f76,plain,(
% 0.21/0.56    ( ! [X6,X5] : (~v1_relat_1(sK1) | ~r2_hidden(X5,k1_relat_1(sK1)) | ~r2_hidden(X6,k1_relat_1(sK1)) | k1_funct_1(sK1,X5) != k1_funct_1(sK1,X6) | X5 = X6 | ~v2_funct_1(sK1)) )),
% 0.21/0.56    inference(resolution,[],[f30,f36])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~r2_hidden(X2,k1_relat_1(X0)) | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | X1 = X2 | ~v2_funct_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(flattening,[],[f16])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 0.21/0.56  fof(f335,plain,(
% 0.21/0.56    ~spl13_2 | spl13_20),
% 0.21/0.56    inference(avatar_split_clause,[],[f72,f333,f103])).
% 0.21/0.56  fof(f103,plain,(
% 0.21/0.56    spl13_2 <=> v1_relat_1(sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).
% 0.21/0.56  fof(f72,plain,(
% 0.21/0.56    ( ! [X8,X7] : (~r2_hidden(X8,sK0) | ~v1_relat_1(sK2) | ~v1_relat_1(X7) | ~v1_funct_1(X7) | k1_funct_1(k5_relat_1(sK2,X7),X8) = k1_funct_1(X7,k1_funct_1(sK2,X8))) )),
% 0.21/0.56    inference(forward_demodulation,[],[f68,f24])).
% 0.21/0.56  fof(f68,plain,(
% 0.21/0.56    ( ! [X8,X7] : (~v1_relat_1(sK2) | ~v1_relat_1(X7) | ~v1_funct_1(X7) | ~r2_hidden(X8,k1_relat_1(sK2)) | k1_funct_1(k5_relat_1(sK2,X7),X8) = k1_funct_1(X7,k1_funct_1(sK2,X8))) )),
% 0.21/0.56    inference(resolution,[],[f22,f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f15])).
% 0.21/0.56  fof(f15,plain,(
% 0.21/0.56    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.56    inference(flattening,[],[f14])).
% 0.21/0.56  fof(f14,plain,(
% 0.21/0.56    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.56    inference(ennf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    v1_funct_1(sK2)),
% 0.21/0.56    inference(cnf_transformation,[],[f11])).
% 0.21/0.56  fof(f294,plain,(
% 0.21/0.56    spl13_16 | ~spl13_2 | ~spl13_3 | ~spl13_18),
% 0.21/0.56    inference(avatar_split_clause,[],[f91,f291,f107,f103,f248])).
% 0.21/0.56  fof(f107,plain,(
% 0.21/0.56    spl13_3 <=> v1_funct_1(sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).
% 0.21/0.56  fof(f91,plain,(
% 0.21/0.56    sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK2 = k6_relat_1(sK0)),
% 0.21/0.56    inference(superposition,[],[f57,f24])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    ( ! [X1] : (sK3(k1_relat_1(X1),X1) != k1_funct_1(X1,sK3(k1_relat_1(X1),X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k6_relat_1(k1_relat_1(X1)) = X1) )),
% 0.21/0.56    inference(equality_resolution,[],[f32])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1)) | k6_relat_1(X0) = X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,plain,(
% 0.21/0.56    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.56    inference(flattening,[],[f12])).
% 0.21/0.56  fof(f12,plain,(
% 0.21/0.56    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).
% 0.21/0.56  fof(f251,plain,(
% 0.21/0.56    spl13_16 | ~spl13_2 | ~spl13_3 | spl13_14),
% 0.21/0.56    inference(avatar_split_clause,[],[f90,f234,f107,f103,f248])).
% 0.21/0.56  fof(f90,plain,(
% 0.21/0.56    r2_hidden(sK3(sK0,sK2),sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK2 = k6_relat_1(sK0)),
% 0.21/0.56    inference(superposition,[],[f58,f24])).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    ( ! [X1] : (r2_hidden(sK3(k1_relat_1(X1),X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k6_relat_1(k1_relat_1(X1)) = X1) )),
% 0.21/0.56    inference(equality_resolution,[],[f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | r2_hidden(sK3(X0,X1),X0) | k6_relat_1(X0) = X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f177,plain,(
% 0.21/0.56    spl13_9),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f174])).
% 0.21/0.56  fof(f174,plain,(
% 0.21/0.56    $false | spl13_9),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f29,f172])).
% 0.21/0.56  fof(f172,plain,(
% 0.21/0.56    ~v1_relat_1(sK1) | spl13_9),
% 0.21/0.56    inference(avatar_component_clause,[],[f170])).
% 0.21/0.56  fof(f131,plain,(
% 0.21/0.56    spl13_6 | ~spl13_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f65,f103,f129])).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    ( ! [X2,X3] : (~v1_relat_1(sK2) | k1_funct_1(sK2,X2) = X3 | ~r2_hidden(k4_tarski(X2,X3),sK2)) )),
% 0.21/0.56    inference(resolution,[],[f22,f49])).
% 0.21/0.56  fof(f49,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f20])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.56    inference(flattening,[],[f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.56  fof(f122,plain,(
% 0.21/0.56    spl13_3),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f119])).
% 0.21/0.56  fof(f119,plain,(
% 0.21/0.56    $false | spl13_3),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f22,f109])).
% 0.21/0.56  fof(f109,plain,(
% 0.21/0.56    ~v1_funct_1(sK2) | spl13_3),
% 0.21/0.56    inference(avatar_component_clause,[],[f107])).
% 0.21/0.56  fof(f118,plain,(
% 0.21/0.56    spl13_2),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f115])).
% 0.21/0.57  fof(f115,plain,(
% 0.21/0.57    $false | spl13_2),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f21,f105])).
% 0.21/0.57  fof(f105,plain,(
% 0.21/0.57    ~v1_relat_1(sK2) | spl13_2),
% 0.21/0.57    inference(avatar_component_clause,[],[f103])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    v1_relat_1(sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f11])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (12375)------------------------------
% 0.21/0.57  % (12375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (12375)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (12375)Memory used [KB]: 6780
% 0.21/0.57  % (12375)Time elapsed: 0.153 s
% 0.21/0.57  % (12375)------------------------------
% 0.21/0.57  % (12375)------------------------------
% 1.57/0.57  % (12398)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.57/0.58  % (12365)Success in time 0.214 s
%------------------------------------------------------------------------------
