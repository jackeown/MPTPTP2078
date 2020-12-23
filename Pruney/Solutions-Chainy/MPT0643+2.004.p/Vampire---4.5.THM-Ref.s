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
% DateTime   : Thu Dec  3 12:52:40 EST 2020

% Result     : Theorem 1.75s
% Output     : Refutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 283 expanded)
%              Number of leaves         :   19 (  86 expanded)
%              Depth                    :    9
%              Number of atoms          :  449 (1437 expanded)
%              Number of equality atoms :   85 ( 402 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1007,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f125,f134,f138,f156,f167,f186,f191,f275,f307,f343,f361,f762,f771,f950,f1006])).

fof(f1006,plain,(
    ~ spl14_22 ),
    inference(avatar_contradiction_clause,[],[f999])).

fof(f999,plain,
    ( $false
    | ~ spl14_22 ),
    inference(unit_resulting_resolution,[],[f28,f274])).

fof(f274,plain,
    ( sK2 = k6_relat_1(sK0)
    | ~ spl14_22 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl14_22
  <=> sK2 = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_22])])).

fof(f28,plain,(
    sK2 != k6_relat_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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

fof(f950,plain,
    ( ~ spl14_4
    | ~ spl14_9
    | ~ spl14_11
    | ~ spl14_12
    | ~ spl14_19
    | spl14_24
    | ~ spl14_27
    | ~ spl14_28
    | ~ spl14_34 ),
    inference(avatar_contradiction_clause,[],[f949])).

fof(f949,plain,
    ( $false
    | ~ spl14_4
    | ~ spl14_9
    | ~ spl14_11
    | ~ spl14_12
    | ~ spl14_19
    | spl14_24
    | ~ spl14_27
    | ~ spl14_28
    | ~ spl14_34 ),
    inference(trivial_inequality_removal,[],[f948])).

fof(f948,plain,
    ( k1_funct_1(sK1,sK3(sK0,sK2)) != k1_funct_1(sK1,sK3(sK0,sK2))
    | ~ spl14_4
    | ~ spl14_9
    | ~ spl14_11
    | ~ spl14_12
    | ~ spl14_19
    | spl14_24
    | ~ spl14_27
    | ~ spl14_28
    | ~ spl14_34 ),
    inference(forward_demodulation,[],[f775,f789])).

fof(f789,plain,
    ( sK3(sK0,sK2) = k1_funct_1(sK2,sK3(sK0,sK2))
    | ~ spl14_4
    | ~ spl14_9
    | ~ spl14_11
    | ~ spl14_12
    | ~ spl14_19
    | ~ spl14_27
    | ~ spl14_28
    | ~ spl14_34 ),
    inference(unit_resulting_resolution,[],[f245,f390,f387,f761])).

fof(f761,plain,
    ( ! [X8,X7] :
        ( ~ r2_hidden(X8,sK0)
        | X7 = X8
        | k1_funct_1(sK1,X8) != k1_funct_1(sK1,X7)
        | ~ r2_hidden(X7,sK0) )
    | ~ spl14_34 ),
    inference(avatar_component_clause,[],[f760])).

fof(f760,plain,
    ( spl14_34
  <=> ! [X7,X8] :
        ( ~ r2_hidden(X8,sK0)
        | X7 = X8
        | k1_funct_1(sK1,X8) != k1_funct_1(sK1,X7)
        | ~ r2_hidden(X7,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_34])])).

fof(f387,plain,
    ( k1_funct_1(sK1,sK3(sK0,sK2)) = k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2)))
    | ~ spl14_9
    | ~ spl14_11
    | ~ spl14_12
    | ~ spl14_19
    | ~ spl14_27
    | ~ spl14_28 ),
    inference(backward_demodulation,[],[f369,f380])).

fof(f380,plain,
    ( k1_funct_1(sK2,sK3(sK0,sK2)) = sK6(sK2,sK1,sK3(sK0,sK2),k1_funct_1(sK1,sK3(sK0,sK2)))
    | ~ spl14_9
    | ~ spl14_12
    | ~ spl14_19
    | ~ spl14_28 ),
    inference(unit_resulting_resolution,[],[f276,f365])).

fof(f365,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | k1_funct_1(sK2,X0) = sK6(sK2,sK1,X0,X1) )
    | ~ spl14_9
    | ~ spl14_28 ),
    inference(resolution,[],[f360,f166])).

fof(f166,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK2)
        | k1_funct_1(sK2,X2) = X3 )
    | ~ spl14_9 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl14_9
  <=> ! [X3,X2] :
        ( k1_funct_1(sK2,X2) = X3
        | ~ r2_hidden(k4_tarski(X2,X3),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_9])])).

fof(f360,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,sK6(sK2,sK1,X0,X1)),sK2)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1) )
    | ~ spl14_28 ),
    inference(avatar_component_clause,[],[f359])).

fof(f359,plain,
    ( spl14_28
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(X0,sK6(sK2,sK1,X0,X1)),sK2)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_28])])).

fof(f276,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,sK2),k1_funct_1(sK1,sK3(sK0,sK2))),sK1)
    | ~ spl14_12
    | ~ spl14_19 ),
    inference(unit_resulting_resolution,[],[f245,f190])).

fof(f190,plain,
    ( ! [X4] :
        ( r2_hidden(k4_tarski(X4,k1_funct_1(sK1,X4)),sK1)
        | ~ r2_hidden(X4,sK0) )
    | ~ spl14_12 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl14_12
  <=> ! [X4] :
        ( ~ r2_hidden(X4,sK0)
        | r2_hidden(k4_tarski(X4,k1_funct_1(sK1,X4)),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_12])])).

fof(f369,plain,
    ( k1_funct_1(sK1,sK3(sK0,sK2)) = k1_funct_1(sK1,sK6(sK2,sK1,sK3(sK0,sK2),k1_funct_1(sK1,sK3(sK0,sK2))))
    | ~ spl14_11
    | ~ spl14_12
    | ~ spl14_19
    | ~ spl14_27 ),
    inference(unit_resulting_resolution,[],[f276,f347])).

fof(f347,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK1,sK6(sK2,sK1,X0,X1)) = X1
        | ~ r2_hidden(k4_tarski(X0,X1),sK1) )
    | ~ spl14_11
    | ~ spl14_27 ),
    inference(resolution,[],[f342,f185])).

fof(f185,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK1)
        | k1_funct_1(sK1,X2) = X3 )
    | ~ spl14_11 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl14_11
  <=> ! [X3,X2] :
        ( k1_funct_1(sK1,X2) = X3
        | ~ r2_hidden(k4_tarski(X2,X3),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_11])])).

fof(f342,plain,
    ( ! [X2,X3] :
        ( r2_hidden(k4_tarski(sK6(sK2,sK1,X2,X3),X3),sK1)
        | ~ r2_hidden(k4_tarski(X2,X3),sK1) )
    | ~ spl14_27 ),
    inference(avatar_component_clause,[],[f341])).

fof(f341,plain,
    ( spl14_27
  <=> ! [X3,X2] :
        ( r2_hidden(k4_tarski(sK6(sK2,sK1,X2,X3),X3),sK1)
        | ~ r2_hidden(k4_tarski(X2,X3),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_27])])).

fof(f390,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),sK0)
    | ~ spl14_4
    | ~ spl14_9
    | ~ spl14_12
    | ~ spl14_19
    | ~ spl14_27
    | ~ spl14_28 ),
    inference(backward_demodulation,[],[f351,f380])).

fof(f351,plain,
    ( r2_hidden(sK6(sK2,sK1,sK3(sK0,sK2),k1_funct_1(sK1,sK3(sK0,sK2))),sK0)
    | ~ spl14_4
    | ~ spl14_12
    | ~ spl14_19
    | ~ spl14_27 ),
    inference(unit_resulting_resolution,[],[f276,f348])).

fof(f348,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK6(sK2,sK1,X2,X3),sK0)
        | ~ r2_hidden(k4_tarski(X2,X3),sK1) )
    | ~ spl14_4
    | ~ spl14_27 ),
    inference(resolution,[],[f342,f133])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | r2_hidden(X0,sK0) )
    | ~ spl14_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl14_4
  <=> ! [X1,X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).

fof(f245,plain,
    ( r2_hidden(sK3(sK0,sK2),sK0)
    | ~ spl14_19 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl14_19
  <=> r2_hidden(sK3(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_19])])).

fof(f775,plain,
    ( k1_funct_1(sK1,sK3(sK0,sK2)) != k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2)))
    | ~ spl14_4
    | ~ spl14_9
    | ~ spl14_12
    | ~ spl14_19
    | spl14_24
    | ~ spl14_27
    | ~ spl14_28
    | ~ spl14_34 ),
    inference(unit_resulting_resolution,[],[f245,f306,f390,f761])).

fof(f306,plain,
    ( sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2))
    | spl14_24 ),
    inference(avatar_component_clause,[],[f304])).

fof(f304,plain,
    ( spl14_24
  <=> sK3(sK0,sK2) = k1_funct_1(sK2,sK3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_24])])).

fof(f771,plain,(
    spl14_33 ),
    inference(avatar_contradiction_clause,[],[f763])).

fof(f763,plain,
    ( $false
    | spl14_33 ),
    inference(unit_resulting_resolution,[],[f26,f758])).

fof(f758,plain,
    ( ~ v2_funct_1(sK1)
    | spl14_33 ),
    inference(avatar_component_clause,[],[f756])).

fof(f756,plain,
    ( spl14_33
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_33])])).

fof(f26,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f762,plain,
    ( ~ spl14_33
    | ~ spl14_3
    | spl14_34 ),
    inference(avatar_split_clause,[],[f95,f760,f128,f756])).

fof(f128,plain,
    ( spl14_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).

fof(f95,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(X8,sK0)
      | ~ r2_hidden(X7,sK0)
      | ~ v1_relat_1(sK1)
      | k1_funct_1(sK1,X8) != k1_funct_1(sK1,X7)
      | X7 = X8
      | ~ v2_funct_1(sK1) ) ),
    inference(forward_demodulation,[],[f94,f23])).

fof(f23,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f94,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(X7,sK0)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X8,k1_relat_1(sK1))
      | k1_funct_1(sK1,X8) != k1_funct_1(sK1,X7)
      | X7 = X8
      | ~ v2_funct_1(sK1) ) ),
    inference(forward_demodulation,[],[f91,f23])).

fof(f91,plain,(
    ! [X8,X7] :
      ( ~ v1_relat_1(sK1)
      | ~ r2_hidden(X7,k1_relat_1(sK1))
      | ~ r2_hidden(X8,k1_relat_1(sK1))
      | k1_funct_1(sK1,X8) != k1_funct_1(sK1,X7)
      | X7 = X8
      | ~ v2_funct_1(sK1) ) ),
    inference(resolution,[],[f30,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
      | X1 = X2
      | ~ v2_funct_1(X0) ) ),
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

fof(f30,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f361,plain,
    ( spl14_28
    | ~ spl14_1
    | ~ spl14_3 ),
    inference(avatar_split_clause,[],[f113,f128,f115,f359])).

fof(f115,plain,
    ( spl14_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK2)
      | r2_hidden(k4_tarski(X0,sK6(sK2,sK1,X0,X1)),sK2)
      | ~ r2_hidden(k4_tarski(X0,X1),sK1) ) ),
    inference(duplicate_literal_removal,[],[f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK2)
      | r2_hidden(k4_tarski(X0,sK6(sK2,sK1,X0,X1)),sK2)
      | ~ r2_hidden(k4_tarski(X0,X1),sK1) ) ),
    inference(superposition,[],[f64,f27])).

fof(f27,plain,(
    sK1 = k5_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,sK6(X0,X1,X3,X4)),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X3,sK6(X0,X1,X3,X4)),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
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
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(f343,plain,
    ( spl14_27
    | ~ spl14_1
    | ~ spl14_3 ),
    inference(avatar_split_clause,[],[f112,f128,f115,f341])).

fof(f112,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK2)
      | r2_hidden(k4_tarski(sK6(sK2,sK1,X2,X3),X3),sK1)
      | ~ r2_hidden(k4_tarski(X2,X3),sK1) ) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK2)
      | r2_hidden(k4_tarski(sK6(sK2,sK1,X2,X3),X3),sK1)
      | ~ r2_hidden(k4_tarski(X2,X3),sK1) ) ),
    inference(superposition,[],[f63,f27])).

fof(f63,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK6(X0,X1,X3,X4),X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK6(X0,X1,X3,X4),X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f307,plain,
    ( spl14_22
    | ~ spl14_1
    | ~ spl14_6
    | ~ spl14_24 ),
    inference(avatar_split_clause,[],[f107,f304,f145,f115,f272])).

fof(f145,plain,
    ( spl14_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).

fof(f107,plain,
    ( sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = k6_relat_1(sK0) ),
    inference(superposition,[],[f60,f24])).

fof(f24,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

fof(f275,plain,
    ( spl14_22
    | ~ spl14_1
    | ~ spl14_6
    | spl14_19 ),
    inference(avatar_split_clause,[],[f106,f243,f145,f115,f272])).

fof(f106,plain,
    ( r2_hidden(sK3(sK0,sK2),sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = k6_relat_1(sK0) ),
    inference(superposition,[],[f61,f24])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f12])).

fof(f191,plain,
    ( ~ spl14_3
    | spl14_12 ),
    inference(avatar_split_clause,[],[f93,f189,f128])).

fof(f93,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | ~ v1_relat_1(sK1)
      | r2_hidden(k4_tarski(X4,k1_funct_1(sK1,X4)),sK1) ) ),
    inference(forward_demodulation,[],[f88,f23])).

fof(f88,plain,(
    ! [X4] :
      ( ~ v1_relat_1(sK1)
      | ~ r2_hidden(X4,k1_relat_1(sK1))
      | r2_hidden(k4_tarski(X4,k1_funct_1(sK1,X4)),sK1) ) ),
    inference(resolution,[],[f30,f69])).

fof(f69,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | k1_funct_1(X2,X0) != X1
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f186,plain,
    ( spl14_11
    | ~ spl14_3 ),
    inference(avatar_split_clause,[],[f87,f128,f184])).

fof(f87,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(sK1)
      | k1_funct_1(sK1,X2) = X3
      | ~ r2_hidden(k4_tarski(X2,X3),sK1) ) ),
    inference(resolution,[],[f30,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f167,plain,
    ( spl14_9
    | ~ spl14_1 ),
    inference(avatar_split_clause,[],[f74,f115,f165])).

fof(f74,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(sK2)
      | k1_funct_1(sK2,X2) = X3
      | ~ r2_hidden(k4_tarski(X2,X3),sK2) ) ),
    inference(resolution,[],[f22,f56])).

fof(f22,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f156,plain,(
    spl14_6 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | spl14_6 ),
    inference(unit_resulting_resolution,[],[f22,f147])).

fof(f147,plain,
    ( ~ v1_funct_1(sK2)
    | spl14_6 ),
    inference(avatar_component_clause,[],[f145])).

fof(f138,plain,(
    spl14_3 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | spl14_3 ),
    inference(unit_resulting_resolution,[],[f29,f130])).

fof(f130,plain,
    ( ~ v1_relat_1(sK1)
    | spl14_3 ),
    inference(avatar_component_clause,[],[f128])).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f134,plain,
    ( ~ spl14_3
    | spl14_4 ),
    inference(avatar_split_clause,[],[f92,f132,f128])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK0)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(k4_tarski(X0,X1),sK1) ) ),
    inference(forward_demodulation,[],[f86,f23])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | r2_hidden(X0,k1_relat_1(sK1))
      | ~ r2_hidden(k4_tarski(X0,X1),sK1) ) ),
    inference(resolution,[],[f30,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f125,plain,(
    spl14_1 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | spl14_1 ),
    inference(unit_resulting_resolution,[],[f21,f117])).

fof(f117,plain,
    ( ~ v1_relat_1(sK2)
    | spl14_1 ),
    inference(avatar_component_clause,[],[f115])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:38:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (29098)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.49  % (29090)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (29088)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (29104)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (29096)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (29087)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (29086)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (29085)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (29084)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (29076)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (29103)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (29095)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (29080)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (29079)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (29078)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (29077)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (29099)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (29091)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (29102)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (29101)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (29100)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (29082)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (29094)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (29093)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (29083)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.56  % (29081)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.56  % (29092)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (29093)Refutation not found, incomplete strategy% (29093)------------------------------
% 0.21/0.56  % (29093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (29093)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (29093)Memory used [KB]: 10746
% 0.21/0.56  % (29093)Time elapsed: 0.151 s
% 0.21/0.56  % (29093)------------------------------
% 0.21/0.56  % (29093)------------------------------
% 0.21/0.57  % (29105)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.58  % (29089)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.75/0.59  % (29097)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.75/0.60  % (29080)Refutation found. Thanks to Tanya!
% 1.75/0.60  % SZS status Theorem for theBenchmark
% 1.75/0.60  % SZS output start Proof for theBenchmark
% 1.75/0.60  fof(f1007,plain,(
% 1.75/0.60    $false),
% 1.75/0.60    inference(avatar_sat_refutation,[],[f125,f134,f138,f156,f167,f186,f191,f275,f307,f343,f361,f762,f771,f950,f1006])).
% 1.75/0.60  fof(f1006,plain,(
% 1.75/0.60    ~spl14_22),
% 1.75/0.60    inference(avatar_contradiction_clause,[],[f999])).
% 1.75/0.60  fof(f999,plain,(
% 1.75/0.60    $false | ~spl14_22),
% 1.75/0.60    inference(unit_resulting_resolution,[],[f28,f274])).
% 1.75/0.60  fof(f274,plain,(
% 1.75/0.60    sK2 = k6_relat_1(sK0) | ~spl14_22),
% 1.75/0.60    inference(avatar_component_clause,[],[f272])).
% 1.75/0.60  fof(f272,plain,(
% 1.75/0.60    spl14_22 <=> sK2 = k6_relat_1(sK0)),
% 1.75/0.60    introduced(avatar_definition,[new_symbols(naming,[spl14_22])])).
% 1.75/0.60  fof(f28,plain,(
% 1.75/0.60    sK2 != k6_relat_1(sK0)),
% 1.75/0.60    inference(cnf_transformation,[],[f10])).
% 1.75/0.60  fof(f10,plain,(
% 1.75/0.60    ? [X0,X1] : (? [X2] : (k6_relat_1(X0) != X2 & k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.75/0.60    inference(flattening,[],[f9])).
% 1.75/0.60  fof(f9,plain,(
% 1.75/0.60    ? [X0,X1] : (? [X2] : ((k6_relat_1(X0) != X2 & (k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0)) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.75/0.60    inference(ennf_transformation,[],[f8])).
% 1.75/0.60  fof(f8,negated_conjecture,(
% 1.75/0.60    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 1.75/0.60    inference(negated_conjecture,[],[f7])).
% 1.75/0.60  fof(f7,conjecture,(
% 1.75/0.60    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 1.75/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_1)).
% 1.75/0.60  fof(f950,plain,(
% 1.75/0.60    ~spl14_4 | ~spl14_9 | ~spl14_11 | ~spl14_12 | ~spl14_19 | spl14_24 | ~spl14_27 | ~spl14_28 | ~spl14_34),
% 1.75/0.60    inference(avatar_contradiction_clause,[],[f949])).
% 1.75/0.60  fof(f949,plain,(
% 1.75/0.60    $false | (~spl14_4 | ~spl14_9 | ~spl14_11 | ~spl14_12 | ~spl14_19 | spl14_24 | ~spl14_27 | ~spl14_28 | ~spl14_34)),
% 1.75/0.60    inference(trivial_inequality_removal,[],[f948])).
% 1.75/0.60  fof(f948,plain,(
% 1.75/0.60    k1_funct_1(sK1,sK3(sK0,sK2)) != k1_funct_1(sK1,sK3(sK0,sK2)) | (~spl14_4 | ~spl14_9 | ~spl14_11 | ~spl14_12 | ~spl14_19 | spl14_24 | ~spl14_27 | ~spl14_28 | ~spl14_34)),
% 1.75/0.60    inference(forward_demodulation,[],[f775,f789])).
% 1.75/0.60  fof(f789,plain,(
% 1.75/0.60    sK3(sK0,sK2) = k1_funct_1(sK2,sK3(sK0,sK2)) | (~spl14_4 | ~spl14_9 | ~spl14_11 | ~spl14_12 | ~spl14_19 | ~spl14_27 | ~spl14_28 | ~spl14_34)),
% 1.75/0.60    inference(unit_resulting_resolution,[],[f245,f390,f387,f761])).
% 1.75/0.60  fof(f761,plain,(
% 1.75/0.60    ( ! [X8,X7] : (~r2_hidden(X8,sK0) | X7 = X8 | k1_funct_1(sK1,X8) != k1_funct_1(sK1,X7) | ~r2_hidden(X7,sK0)) ) | ~spl14_34),
% 1.75/0.60    inference(avatar_component_clause,[],[f760])).
% 1.75/0.60  fof(f760,plain,(
% 1.75/0.60    spl14_34 <=> ! [X7,X8] : (~r2_hidden(X8,sK0) | X7 = X8 | k1_funct_1(sK1,X8) != k1_funct_1(sK1,X7) | ~r2_hidden(X7,sK0))),
% 1.75/0.60    introduced(avatar_definition,[new_symbols(naming,[spl14_34])])).
% 1.75/0.60  fof(f387,plain,(
% 1.75/0.60    k1_funct_1(sK1,sK3(sK0,sK2)) = k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2))) | (~spl14_9 | ~spl14_11 | ~spl14_12 | ~spl14_19 | ~spl14_27 | ~spl14_28)),
% 1.75/0.60    inference(backward_demodulation,[],[f369,f380])).
% 1.75/0.60  fof(f380,plain,(
% 1.75/0.60    k1_funct_1(sK2,sK3(sK0,sK2)) = sK6(sK2,sK1,sK3(sK0,sK2),k1_funct_1(sK1,sK3(sK0,sK2))) | (~spl14_9 | ~spl14_12 | ~spl14_19 | ~spl14_28)),
% 1.75/0.60    inference(unit_resulting_resolution,[],[f276,f365])).
% 1.75/0.60  fof(f365,plain,(
% 1.75/0.60    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | k1_funct_1(sK2,X0) = sK6(sK2,sK1,X0,X1)) ) | (~spl14_9 | ~spl14_28)),
% 1.75/0.60    inference(resolution,[],[f360,f166])).
% 1.75/0.60  fof(f166,plain,(
% 1.75/0.60    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK2) | k1_funct_1(sK2,X2) = X3) ) | ~spl14_9),
% 1.75/0.60    inference(avatar_component_clause,[],[f165])).
% 1.75/0.60  fof(f165,plain,(
% 1.75/0.60    spl14_9 <=> ! [X3,X2] : (k1_funct_1(sK2,X2) = X3 | ~r2_hidden(k4_tarski(X2,X3),sK2))),
% 1.75/0.60    introduced(avatar_definition,[new_symbols(naming,[spl14_9])])).
% 1.75/0.60  fof(f360,plain,(
% 1.75/0.60    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,sK6(sK2,sK1,X0,X1)),sK2) | ~r2_hidden(k4_tarski(X0,X1),sK1)) ) | ~spl14_28),
% 1.75/0.60    inference(avatar_component_clause,[],[f359])).
% 1.75/0.60  fof(f359,plain,(
% 1.75/0.60    spl14_28 <=> ! [X1,X0] : (r2_hidden(k4_tarski(X0,sK6(sK2,sK1,X0,X1)),sK2) | ~r2_hidden(k4_tarski(X0,X1),sK1))),
% 1.75/0.60    introduced(avatar_definition,[new_symbols(naming,[spl14_28])])).
% 1.75/0.60  fof(f276,plain,(
% 1.75/0.60    r2_hidden(k4_tarski(sK3(sK0,sK2),k1_funct_1(sK1,sK3(sK0,sK2))),sK1) | (~spl14_12 | ~spl14_19)),
% 1.75/0.60    inference(unit_resulting_resolution,[],[f245,f190])).
% 1.75/0.60  fof(f190,plain,(
% 1.75/0.60    ( ! [X4] : (r2_hidden(k4_tarski(X4,k1_funct_1(sK1,X4)),sK1) | ~r2_hidden(X4,sK0)) ) | ~spl14_12),
% 1.75/0.60    inference(avatar_component_clause,[],[f189])).
% 1.75/0.60  fof(f189,plain,(
% 1.75/0.60    spl14_12 <=> ! [X4] : (~r2_hidden(X4,sK0) | r2_hidden(k4_tarski(X4,k1_funct_1(sK1,X4)),sK1))),
% 1.75/0.60    introduced(avatar_definition,[new_symbols(naming,[spl14_12])])).
% 1.75/0.60  fof(f369,plain,(
% 1.75/0.60    k1_funct_1(sK1,sK3(sK0,sK2)) = k1_funct_1(sK1,sK6(sK2,sK1,sK3(sK0,sK2),k1_funct_1(sK1,sK3(sK0,sK2)))) | (~spl14_11 | ~spl14_12 | ~spl14_19 | ~spl14_27)),
% 1.75/0.60    inference(unit_resulting_resolution,[],[f276,f347])).
% 1.75/0.60  fof(f347,plain,(
% 1.75/0.60    ( ! [X0,X1] : (k1_funct_1(sK1,sK6(sK2,sK1,X0,X1)) = X1 | ~r2_hidden(k4_tarski(X0,X1),sK1)) ) | (~spl14_11 | ~spl14_27)),
% 1.75/0.60    inference(resolution,[],[f342,f185])).
% 1.75/0.60  fof(f185,plain,(
% 1.75/0.60    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK1) | k1_funct_1(sK1,X2) = X3) ) | ~spl14_11),
% 1.75/0.60    inference(avatar_component_clause,[],[f184])).
% 1.75/0.60  fof(f184,plain,(
% 1.75/0.60    spl14_11 <=> ! [X3,X2] : (k1_funct_1(sK1,X2) = X3 | ~r2_hidden(k4_tarski(X2,X3),sK1))),
% 1.75/0.60    introduced(avatar_definition,[new_symbols(naming,[spl14_11])])).
% 1.75/0.60  fof(f342,plain,(
% 1.75/0.60    ( ! [X2,X3] : (r2_hidden(k4_tarski(sK6(sK2,sK1,X2,X3),X3),sK1) | ~r2_hidden(k4_tarski(X2,X3),sK1)) ) | ~spl14_27),
% 1.75/0.60    inference(avatar_component_clause,[],[f341])).
% 1.75/0.60  fof(f341,plain,(
% 1.75/0.60    spl14_27 <=> ! [X3,X2] : (r2_hidden(k4_tarski(sK6(sK2,sK1,X2,X3),X3),sK1) | ~r2_hidden(k4_tarski(X2,X3),sK1))),
% 1.75/0.60    introduced(avatar_definition,[new_symbols(naming,[spl14_27])])).
% 1.75/0.60  fof(f390,plain,(
% 1.75/0.60    r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),sK0) | (~spl14_4 | ~spl14_9 | ~spl14_12 | ~spl14_19 | ~spl14_27 | ~spl14_28)),
% 1.75/0.60    inference(backward_demodulation,[],[f351,f380])).
% 1.75/0.60  fof(f351,plain,(
% 1.75/0.60    r2_hidden(sK6(sK2,sK1,sK3(sK0,sK2),k1_funct_1(sK1,sK3(sK0,sK2))),sK0) | (~spl14_4 | ~spl14_12 | ~spl14_19 | ~spl14_27)),
% 1.75/0.60    inference(unit_resulting_resolution,[],[f276,f348])).
% 1.75/0.60  fof(f348,plain,(
% 1.75/0.60    ( ! [X2,X3] : (r2_hidden(sK6(sK2,sK1,X2,X3),sK0) | ~r2_hidden(k4_tarski(X2,X3),sK1)) ) | (~spl14_4 | ~spl14_27)),
% 1.75/0.60    inference(resolution,[],[f342,f133])).
% 1.75/0.60  fof(f133,plain,(
% 1.75/0.60    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | r2_hidden(X0,sK0)) ) | ~spl14_4),
% 1.75/0.60    inference(avatar_component_clause,[],[f132])).
% 1.75/0.60  fof(f132,plain,(
% 1.75/0.60    spl14_4 <=> ! [X1,X0] : (r2_hidden(X0,sK0) | ~r2_hidden(k4_tarski(X0,X1),sK1))),
% 1.75/0.60    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).
% 1.75/0.60  fof(f245,plain,(
% 1.75/0.60    r2_hidden(sK3(sK0,sK2),sK0) | ~spl14_19),
% 1.75/0.60    inference(avatar_component_clause,[],[f243])).
% 1.75/0.60  fof(f243,plain,(
% 1.75/0.60    spl14_19 <=> r2_hidden(sK3(sK0,sK2),sK0)),
% 1.75/0.60    introduced(avatar_definition,[new_symbols(naming,[spl14_19])])).
% 1.75/0.60  fof(f775,plain,(
% 1.75/0.60    k1_funct_1(sK1,sK3(sK0,sK2)) != k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2))) | (~spl14_4 | ~spl14_9 | ~spl14_12 | ~spl14_19 | spl14_24 | ~spl14_27 | ~spl14_28 | ~spl14_34)),
% 1.75/0.60    inference(unit_resulting_resolution,[],[f245,f306,f390,f761])).
% 1.75/0.60  fof(f306,plain,(
% 1.75/0.60    sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2)) | spl14_24),
% 1.75/0.60    inference(avatar_component_clause,[],[f304])).
% 1.75/0.60  fof(f304,plain,(
% 1.75/0.60    spl14_24 <=> sK3(sK0,sK2) = k1_funct_1(sK2,sK3(sK0,sK2))),
% 1.75/0.60    introduced(avatar_definition,[new_symbols(naming,[spl14_24])])).
% 1.75/0.60  fof(f771,plain,(
% 1.75/0.60    spl14_33),
% 1.75/0.60    inference(avatar_contradiction_clause,[],[f763])).
% 1.75/0.60  fof(f763,plain,(
% 1.75/0.60    $false | spl14_33),
% 1.75/0.60    inference(unit_resulting_resolution,[],[f26,f758])).
% 1.75/0.60  fof(f758,plain,(
% 1.75/0.60    ~v2_funct_1(sK1) | spl14_33),
% 1.75/0.60    inference(avatar_component_clause,[],[f756])).
% 1.75/0.60  fof(f756,plain,(
% 1.75/0.60    spl14_33 <=> v2_funct_1(sK1)),
% 1.75/0.60    introduced(avatar_definition,[new_symbols(naming,[spl14_33])])).
% 1.75/0.60  fof(f26,plain,(
% 1.75/0.60    v2_funct_1(sK1)),
% 1.75/0.60    inference(cnf_transformation,[],[f10])).
% 1.75/0.60  fof(f762,plain,(
% 1.75/0.60    ~spl14_33 | ~spl14_3 | spl14_34),
% 1.75/0.60    inference(avatar_split_clause,[],[f95,f760,f128,f756])).
% 1.75/0.60  fof(f128,plain,(
% 1.75/0.60    spl14_3 <=> v1_relat_1(sK1)),
% 1.75/0.60    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).
% 1.75/0.60  fof(f95,plain,(
% 1.75/0.60    ( ! [X8,X7] : (~r2_hidden(X8,sK0) | ~r2_hidden(X7,sK0) | ~v1_relat_1(sK1) | k1_funct_1(sK1,X8) != k1_funct_1(sK1,X7) | X7 = X8 | ~v2_funct_1(sK1)) )),
% 1.75/0.60    inference(forward_demodulation,[],[f94,f23])).
% 1.75/0.60  fof(f23,plain,(
% 1.75/0.60    sK0 = k1_relat_1(sK1)),
% 1.75/0.60    inference(cnf_transformation,[],[f10])).
% 1.75/0.60  fof(f94,plain,(
% 1.75/0.60    ( ! [X8,X7] : (~r2_hidden(X7,sK0) | ~v1_relat_1(sK1) | ~r2_hidden(X8,k1_relat_1(sK1)) | k1_funct_1(sK1,X8) != k1_funct_1(sK1,X7) | X7 = X8 | ~v2_funct_1(sK1)) )),
% 1.75/0.60    inference(forward_demodulation,[],[f91,f23])).
% 1.75/0.60  fof(f91,plain,(
% 1.75/0.60    ( ! [X8,X7] : (~v1_relat_1(sK1) | ~r2_hidden(X7,k1_relat_1(sK1)) | ~r2_hidden(X8,k1_relat_1(sK1)) | k1_funct_1(sK1,X8) != k1_funct_1(sK1,X7) | X7 = X8 | ~v2_funct_1(sK1)) )),
% 1.75/0.60    inference(resolution,[],[f30,f41])).
% 1.75/0.60  fof(f41,plain,(
% 1.75/0.60    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~r2_hidden(X2,k1_relat_1(X0)) | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | X1 = X2 | ~v2_funct_1(X0)) )),
% 1.75/0.60    inference(cnf_transformation,[],[f15])).
% 1.75/0.60  fof(f15,plain,(
% 1.75/0.60    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.75/0.60    inference(flattening,[],[f14])).
% 1.75/0.60  fof(f14,plain,(
% 1.75/0.60    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.75/0.60    inference(ennf_transformation,[],[f4])).
% 1.75/0.60  fof(f4,axiom,(
% 1.75/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 1.75/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 1.75/0.60  fof(f30,plain,(
% 1.75/0.60    v1_funct_1(sK1)),
% 1.75/0.60    inference(cnf_transformation,[],[f10])).
% 1.75/0.60  fof(f361,plain,(
% 1.75/0.60    spl14_28 | ~spl14_1 | ~spl14_3),
% 1.75/0.60    inference(avatar_split_clause,[],[f113,f128,f115,f359])).
% 1.75/0.60  fof(f115,plain,(
% 1.75/0.60    spl14_1 <=> v1_relat_1(sK2)),
% 1.75/0.60    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).
% 1.75/0.60  fof(f113,plain,(
% 1.75/0.60    ( ! [X0,X1] : (~v1_relat_1(sK1) | ~v1_relat_1(sK2) | r2_hidden(k4_tarski(X0,sK6(sK2,sK1,X0,X1)),sK2) | ~r2_hidden(k4_tarski(X0,X1),sK1)) )),
% 1.75/0.60    inference(duplicate_literal_removal,[],[f108])).
% 1.75/0.60  fof(f108,plain,(
% 1.75/0.60    ( ! [X0,X1] : (~v1_relat_1(sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(sK2) | r2_hidden(k4_tarski(X0,sK6(sK2,sK1,X0,X1)),sK2) | ~r2_hidden(k4_tarski(X0,X1),sK1)) )),
% 1.75/0.60    inference(superposition,[],[f64,f27])).
% 1.75/0.60  fof(f27,plain,(
% 1.75/0.60    sK1 = k5_relat_1(sK2,sK1)),
% 1.75/0.60    inference(cnf_transformation,[],[f10])).
% 1.75/0.60  fof(f64,plain,(
% 1.75/0.60    ( ! [X4,X0,X3,X1] : (~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(X3,sK6(X0,X1,X3,X4)),X0) | ~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))) )),
% 1.75/0.60    inference(equality_resolution,[],[f38])).
% 1.75/0.60  fof(f38,plain,(
% 1.75/0.60    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(X3,sK6(X0,X1,X3,X4)),X0) | ~r2_hidden(k4_tarski(X3,X4),X2) | k5_relat_1(X0,X1) != X2) )),
% 1.75/0.60    inference(cnf_transformation,[],[f13])).
% 1.75/0.60  fof(f13,plain,(
% 1.75/0.60    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.75/0.60    inference(ennf_transformation,[],[f2])).
% 1.75/0.60  fof(f2,axiom,(
% 1.75/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 1.75/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).
% 1.75/0.60  fof(f343,plain,(
% 1.75/0.60    spl14_27 | ~spl14_1 | ~spl14_3),
% 1.75/0.60    inference(avatar_split_clause,[],[f112,f128,f115,f341])).
% 1.75/0.60  fof(f112,plain,(
% 1.75/0.60    ( ! [X2,X3] : (~v1_relat_1(sK1) | ~v1_relat_1(sK2) | r2_hidden(k4_tarski(sK6(sK2,sK1,X2,X3),X3),sK1) | ~r2_hidden(k4_tarski(X2,X3),sK1)) )),
% 1.75/0.60    inference(duplicate_literal_removal,[],[f109])).
% 1.75/0.60  fof(f109,plain,(
% 1.75/0.60    ( ! [X2,X3] : (~v1_relat_1(sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(sK2) | r2_hidden(k4_tarski(sK6(sK2,sK1,X2,X3),X3),sK1) | ~r2_hidden(k4_tarski(X2,X3),sK1)) )),
% 1.75/0.60    inference(superposition,[],[f63,f27])).
% 1.75/0.60  fof(f63,plain,(
% 1.75/0.60    ( ! [X4,X0,X3,X1] : (~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(sK6(X0,X1,X3,X4),X4),X1) | ~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))) )),
% 1.75/0.60    inference(equality_resolution,[],[f39])).
% 1.75/0.60  fof(f39,plain,(
% 1.75/0.60    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(sK6(X0,X1,X3,X4),X4),X1) | ~r2_hidden(k4_tarski(X3,X4),X2) | k5_relat_1(X0,X1) != X2) )),
% 1.75/0.60    inference(cnf_transformation,[],[f13])).
% 1.75/0.60  fof(f307,plain,(
% 1.75/0.60    spl14_22 | ~spl14_1 | ~spl14_6 | ~spl14_24),
% 1.75/0.60    inference(avatar_split_clause,[],[f107,f304,f145,f115,f272])).
% 1.75/0.60  fof(f145,plain,(
% 1.75/0.60    spl14_6 <=> v1_funct_1(sK2)),
% 1.75/0.60    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).
% 1.75/0.60  fof(f107,plain,(
% 1.75/0.60    sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK2 = k6_relat_1(sK0)),
% 1.75/0.60    inference(superposition,[],[f60,f24])).
% 1.75/0.60  fof(f24,plain,(
% 1.75/0.60    sK0 = k1_relat_1(sK2)),
% 1.75/0.60    inference(cnf_transformation,[],[f10])).
% 1.75/0.60  fof(f60,plain,(
% 1.75/0.60    ( ! [X1] : (sK3(k1_relat_1(X1),X1) != k1_funct_1(X1,sK3(k1_relat_1(X1),X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k6_relat_1(k1_relat_1(X1)) = X1) )),
% 1.75/0.60    inference(equality_resolution,[],[f32])).
% 1.75/0.60  fof(f32,plain,(
% 1.75/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1)) | k6_relat_1(X0) = X1) )),
% 1.75/0.60    inference(cnf_transformation,[],[f12])).
% 1.75/0.60  fof(f12,plain,(
% 1.75/0.60    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.75/0.60    inference(flattening,[],[f11])).
% 1.75/0.60  fof(f11,plain,(
% 1.75/0.60    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.75/0.60    inference(ennf_transformation,[],[f5])).
% 1.75/0.60  fof(f5,axiom,(
% 1.75/0.60    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 1.75/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).
% 1.75/0.60  fof(f275,plain,(
% 1.75/0.60    spl14_22 | ~spl14_1 | ~spl14_6 | spl14_19),
% 1.75/0.60    inference(avatar_split_clause,[],[f106,f243,f145,f115,f272])).
% 1.75/0.60  fof(f106,plain,(
% 1.75/0.60    r2_hidden(sK3(sK0,sK2),sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK2 = k6_relat_1(sK0)),
% 1.75/0.60    inference(superposition,[],[f61,f24])).
% 1.75/0.60  fof(f61,plain,(
% 1.75/0.60    ( ! [X1] : (r2_hidden(sK3(k1_relat_1(X1),X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k6_relat_1(k1_relat_1(X1)) = X1) )),
% 1.75/0.60    inference(equality_resolution,[],[f31])).
% 1.75/0.60  fof(f31,plain,(
% 1.75/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | r2_hidden(sK3(X0,X1),X0) | k6_relat_1(X0) = X1) )),
% 1.75/0.60    inference(cnf_transformation,[],[f12])).
% 1.75/0.60  fof(f191,plain,(
% 1.75/0.60    ~spl14_3 | spl14_12),
% 1.75/0.60    inference(avatar_split_clause,[],[f93,f189,f128])).
% 1.75/0.60  fof(f93,plain,(
% 1.75/0.60    ( ! [X4] : (~r2_hidden(X4,sK0) | ~v1_relat_1(sK1) | r2_hidden(k4_tarski(X4,k1_funct_1(sK1,X4)),sK1)) )),
% 1.75/0.60    inference(forward_demodulation,[],[f88,f23])).
% 1.75/0.60  fof(f88,plain,(
% 1.75/0.60    ( ! [X4] : (~v1_relat_1(sK1) | ~r2_hidden(X4,k1_relat_1(sK1)) | r2_hidden(k4_tarski(X4,k1_funct_1(sK1,X4)),sK1)) )),
% 1.75/0.60    inference(resolution,[],[f30,f69])).
% 1.75/0.60  fof(f69,plain,(
% 1.75/0.60    ( ! [X2,X0] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)) )),
% 1.75/0.60    inference(equality_resolution,[],[f57])).
% 1.75/0.60  fof(f57,plain,(
% 1.75/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | k1_funct_1(X2,X0) != X1 | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 1.75/0.60    inference(cnf_transformation,[],[f20])).
% 1.75/0.60  fof(f20,plain,(
% 1.75/0.60    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.75/0.60    inference(flattening,[],[f19])).
% 1.75/0.60  fof(f19,plain,(
% 1.75/0.60    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.75/0.60    inference(ennf_transformation,[],[f6])).
% 1.75/0.60  fof(f6,axiom,(
% 1.75/0.60    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.75/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 1.75/0.60  fof(f186,plain,(
% 1.75/0.60    spl14_11 | ~spl14_3),
% 1.75/0.60    inference(avatar_split_clause,[],[f87,f128,f184])).
% 1.75/0.60  fof(f87,plain,(
% 1.75/0.60    ( ! [X2,X3] : (~v1_relat_1(sK1) | k1_funct_1(sK1,X2) = X3 | ~r2_hidden(k4_tarski(X2,X3),sK1)) )),
% 1.75/0.60    inference(resolution,[],[f30,f56])).
% 1.75/0.60  fof(f56,plain,(
% 1.75/0.60    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 1.75/0.60    inference(cnf_transformation,[],[f20])).
% 1.75/0.60  fof(f167,plain,(
% 1.75/0.60    spl14_9 | ~spl14_1),
% 1.75/0.60    inference(avatar_split_clause,[],[f74,f115,f165])).
% 1.75/0.60  fof(f74,plain,(
% 1.75/0.60    ( ! [X2,X3] : (~v1_relat_1(sK2) | k1_funct_1(sK2,X2) = X3 | ~r2_hidden(k4_tarski(X2,X3),sK2)) )),
% 1.75/0.60    inference(resolution,[],[f22,f56])).
% 1.75/0.60  fof(f22,plain,(
% 1.75/0.60    v1_funct_1(sK2)),
% 1.75/0.60    inference(cnf_transformation,[],[f10])).
% 1.75/0.60  fof(f156,plain,(
% 1.75/0.60    spl14_6),
% 1.75/0.60    inference(avatar_contradiction_clause,[],[f153])).
% 1.75/0.60  fof(f153,plain,(
% 1.75/0.60    $false | spl14_6),
% 1.75/0.60    inference(unit_resulting_resolution,[],[f22,f147])).
% 1.75/0.60  fof(f147,plain,(
% 1.75/0.60    ~v1_funct_1(sK2) | spl14_6),
% 1.75/0.60    inference(avatar_component_clause,[],[f145])).
% 1.75/0.60  fof(f138,plain,(
% 1.75/0.60    spl14_3),
% 1.75/0.60    inference(avatar_contradiction_clause,[],[f135])).
% 1.75/0.60  fof(f135,plain,(
% 1.75/0.60    $false | spl14_3),
% 1.75/0.60    inference(unit_resulting_resolution,[],[f29,f130])).
% 1.75/0.60  fof(f130,plain,(
% 1.75/0.60    ~v1_relat_1(sK1) | spl14_3),
% 1.75/0.60    inference(avatar_component_clause,[],[f128])).
% 1.75/0.60  fof(f29,plain,(
% 1.75/0.60    v1_relat_1(sK1)),
% 1.75/0.60    inference(cnf_transformation,[],[f10])).
% 1.75/0.60  fof(f134,plain,(
% 1.75/0.60    ~spl14_3 | spl14_4),
% 1.75/0.60    inference(avatar_split_clause,[],[f92,f132,f128])).
% 1.75/0.60  fof(f92,plain,(
% 1.75/0.60    ( ! [X0,X1] : (r2_hidden(X0,sK0) | ~v1_relat_1(sK1) | ~r2_hidden(k4_tarski(X0,X1),sK1)) )),
% 1.75/0.60    inference(forward_demodulation,[],[f86,f23])).
% 1.75/0.60  fof(f86,plain,(
% 1.75/0.60    ( ! [X0,X1] : (~v1_relat_1(sK1) | r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(k4_tarski(X0,X1),sK1)) )),
% 1.75/0.60    inference(resolution,[],[f30,f55])).
% 1.75/0.60  fof(f55,plain,(
% 1.75/0.60    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 1.75/0.60    inference(cnf_transformation,[],[f20])).
% 1.75/0.60  fof(f125,plain,(
% 1.75/0.60    spl14_1),
% 1.75/0.60    inference(avatar_contradiction_clause,[],[f122])).
% 1.75/0.60  fof(f122,plain,(
% 1.75/0.60    $false | spl14_1),
% 1.75/0.60    inference(unit_resulting_resolution,[],[f21,f117])).
% 1.75/0.60  fof(f117,plain,(
% 1.75/0.60    ~v1_relat_1(sK2) | spl14_1),
% 1.75/0.60    inference(avatar_component_clause,[],[f115])).
% 1.75/0.60  fof(f21,plain,(
% 1.75/0.60    v1_relat_1(sK2)),
% 1.75/0.60    inference(cnf_transformation,[],[f10])).
% 1.75/0.60  % SZS output end Proof for theBenchmark
% 1.75/0.60  % (29080)------------------------------
% 1.75/0.60  % (29080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.60  % (29080)Termination reason: Refutation
% 1.75/0.60  
% 1.75/0.60  % (29080)Memory used [KB]: 7036
% 1.75/0.60  % (29080)Time elapsed: 0.173 s
% 1.75/0.60  % (29080)------------------------------
% 1.75/0.60  % (29080)------------------------------
% 1.75/0.60  % (29074)Success in time 0.237 s
%------------------------------------------------------------------------------
