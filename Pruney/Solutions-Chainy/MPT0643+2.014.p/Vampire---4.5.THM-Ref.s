%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 188 expanded)
%              Number of leaves         :   25 (  78 expanded)
%              Depth                    :    9
%              Number of atoms          :  374 ( 850 expanded)
%              Number of equality atoms :   81 ( 261 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f282,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f55,f60,f65,f70,f75,f80,f85,f90,f95,f104,f110,f123,f137,f159,f247,f265,f269,f281])).

fof(f281,plain,
    ( ~ spl5_25
    | ~ spl5_24
    | spl5_3
    | ~ spl5_19
    | ~ spl5_11
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f280,f213,f101,f156,f57,f221,f225])).

fof(f225,plain,
    ( spl5_25
  <=> v1_relat_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f221,plain,
    ( spl5_24
  <=> v1_funct_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f57,plain,
    ( spl5_3
  <=> sK2 = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f156,plain,
    ( spl5_19
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f101,plain,
    ( spl5_11
  <=> sK1 = k5_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f213,plain,
    ( spl5_23
  <=> ! [X0] :
        ( k1_relat_1(X0) != sK0
        | sK2 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | sK1 != k5_relat_1(X0,sK1)
        | ~ r1_tarski(k2_relat_1(X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f280,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK2 = k6_relat_1(sK0)
    | ~ v1_funct_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ spl5_11
    | ~ spl5_23 ),
    inference(forward_demodulation,[],[f279,f30])).

fof(f30,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f279,plain,
    ( sK2 = k6_relat_1(sK0)
    | ~ v1_funct_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ r1_tarski(k2_relat_1(k6_relat_1(sK0)),sK0)
    | ~ spl5_11
    | ~ spl5_23 ),
    inference(trivial_inequality_removal,[],[f278])).

fof(f278,plain,
    ( sK0 != sK0
    | sK2 = k6_relat_1(sK0)
    | ~ v1_funct_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ r1_tarski(k2_relat_1(k6_relat_1(sK0)),sK0)
    | ~ spl5_11
    | ~ spl5_23 ),
    inference(forward_demodulation,[],[f277,f29])).

fof(f29,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f277,plain,
    ( sK2 = k6_relat_1(sK0)
    | ~ v1_funct_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k6_relat_1(sK0))
    | sK0 != k1_relat_1(k6_relat_1(sK0))
    | ~ r1_tarski(k2_relat_1(k6_relat_1(sK0)),sK0)
    | ~ spl5_11
    | ~ spl5_23 ),
    inference(trivial_inequality_removal,[],[f276])).

fof(f276,plain,
    ( sK1 != sK1
    | sK2 = k6_relat_1(sK0)
    | ~ v1_funct_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k6_relat_1(sK0))
    | sK0 != k1_relat_1(k6_relat_1(sK0))
    | ~ r1_tarski(k2_relat_1(k6_relat_1(sK0)),sK0)
    | ~ spl5_11
    | ~ spl5_23 ),
    inference(superposition,[],[f214,f103])).

fof(f103,plain,
    ( sK1 = k5_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f101])).

fof(f214,plain,
    ( ! [X0] :
        ( sK1 != k5_relat_1(X0,sK1)
        | sK2 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) != sK0
        | ~ r1_tarski(k2_relat_1(X0),sK0) )
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f213])).

fof(f269,plain,(
    spl5_25 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | spl5_25 ),
    inference(unit_resulting_resolution,[],[f27,f227])).

fof(f227,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | spl5_25 ),
    inference(avatar_component_clause,[],[f225])).

fof(f27,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f265,plain,(
    spl5_24 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | spl5_24 ),
    inference(unit_resulting_resolution,[],[f28,f223])).

fof(f223,plain,
    ( ~ v1_funct_1(k6_relat_1(sK0))
    | spl5_24 ),
    inference(avatar_component_clause,[],[f221])).

fof(f28,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f247,plain,
    ( ~ spl5_5
    | ~ spl5_2
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_1
    | ~ spl5_6
    | spl5_23
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f246,f82,f77,f62,f213,f72,f47,f92,f87,f52,f67])).

fof(f67,plain,
    ( spl5_5
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f52,plain,
    ( spl5_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f87,plain,
    ( spl5_9
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f92,plain,
    ( spl5_10
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f47,plain,
    ( spl5_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f72,plain,
    ( spl5_6
  <=> r1_tarski(k2_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f62,plain,
    ( spl5_4
  <=> sK1 = k5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f77,plain,
    ( spl5_7
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f82,plain,
    ( spl5_8
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f246,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | ~ r1_tarski(k2_relat_1(sK2),sK0)
        | ~ r1_tarski(k2_relat_1(X0),sK0)
        | sK1 != k5_relat_1(X0,sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK1)
        | sK2 = X0
        | ~ v2_funct_1(sK1) )
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f245,f79])).

fof(f79,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f77])).

fof(f245,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK2),sK0)
        | ~ r1_tarski(k2_relat_1(X0),sK0)
        | sK1 != k5_relat_1(X0,sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(sK2)
        | k1_relat_1(X0) != k1_relat_1(sK2)
        | ~ v1_relat_1(sK1)
        | sK2 = X0
        | ~ v2_funct_1(sK1) )
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f244,f84])).

fof(f84,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f82])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(X0),sK0)
        | sK1 != k5_relat_1(X0,sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ r1_tarski(k2_relat_1(sK2),k1_relat_1(sK1))
        | k1_relat_1(X0) != k1_relat_1(sK2)
        | ~ v1_relat_1(sK1)
        | sK2 = X0
        | ~ v2_funct_1(sK1) )
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f201,f84])).

fof(f201,plain,
    ( ! [X0] :
        ( sK1 != k5_relat_1(X0,sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(sK1))
        | ~ r1_tarski(k2_relat_1(sK2),k1_relat_1(sK1))
        | k1_relat_1(X0) != k1_relat_1(sK2)
        | ~ v1_relat_1(sK1)
        | sK2 = X0
        | ~ v2_funct_1(sK1) )
    | ~ spl5_4 ),
    inference(superposition,[],[f41,f64])).

fof(f64,plain,
    ( sK1 = k5_relat_1(sK2,sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
      | k1_relat_1(X1) != k1_relat_1(X2)
      | ~ v1_relat_1(X0)
      | X1 = X2
      | ~ v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
                | k1_relat_1(X1) != k1_relat_1(X2)
                | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
                | k1_relat_1(X1) != k1_relat_1(X2)
                | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k5_relat_1(X1,X0) = k5_relat_1(X2,X0)
                    & k1_relat_1(X1) = k1_relat_1(X2)
                    & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                    & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) )
                 => X1 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_funct_1)).

fof(f159,plain,
    ( ~ spl5_10
    | ~ spl5_14
    | spl5_19
    | ~ spl5_7
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f152,f135,f77,f156,f120,f92])).

fof(f120,plain,
    ( spl5_14
  <=> r1_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f135,plain,
    ( spl5_15
  <=> ! [X0] :
        ( r1_tarski(sK0,k1_relat_1(X0))
        | ~ r1_tarski(sK2,X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f152,plain,
    ( r1_tarski(sK0,sK0)
    | ~ r1_tarski(sK2,sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_7
    | ~ spl5_15 ),
    inference(superposition,[],[f136,f79])).

fof(f136,plain,
    ( ! [X0] :
        ( r1_tarski(sK0,k1_relat_1(X0))
        | ~ r1_tarski(sK2,X0)
        | ~ v1_relat_1(X0) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f135])).

fof(f137,plain,
    ( ~ spl5_10
    | spl5_15
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f128,f77,f135,f92])).

fof(f128,plain,
    ( ! [X0] :
        ( r1_tarski(sK0,k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(sK2,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl5_7 ),
    inference(superposition,[],[f32,f79])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f123,plain,
    ( ~ spl5_10
    | spl5_14
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f118,f107,f120,f92])).

fof(f107,plain,
    ( spl5_12
  <=> sK2 = k5_relat_1(k6_relat_1(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f118,plain,
    ( r1_tarski(sK2,sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_12 ),
    inference(superposition,[],[f45,f109])).

fof(f109,plain,
    ( sK2 = k5_relat_1(k6_relat_1(sK0),sK2)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f107])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(f110,plain,
    ( spl5_12
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f105,f92,f77,f107])).

fof(f105,plain,
    ( sK2 = k5_relat_1(k6_relat_1(sK0),sK2)
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f97,f79])).

fof(f97,plain,
    ( sK2 = k5_relat_1(k6_relat_1(k1_relat_1(sK2)),sK2)
    | ~ spl5_10 ),
    inference(resolution,[],[f31,f94])).

fof(f94,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f92])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f104,plain,
    ( spl5_11
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f99,f82,f52,f101])).

fof(f99,plain,
    ( sK1 = k5_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f96,f84])).

fof(f96,plain,
    ( sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f31,f54])).

fof(f54,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f95,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f17,f92])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_1)).

fof(f90,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f18,f87])).

fof(f18,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f85,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f19,f82])).

fof(f19,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f80,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f20,f77])).

fof(f20,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f75,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f21,f72])).

fof(f21,plain,(
    r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f70,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f22,f67])).

fof(f22,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f65,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f23,f62])).

fof(f23,plain,(
    sK1 = k5_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f60,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f24,f57])).

fof(f24,plain,(
    sK2 != k6_relat_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f55,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f25,f52])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f50,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f26,f47])).

fof(f26,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:18:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (21802)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.45  % (21809)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.45  % (21802)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f282,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f50,f55,f60,f65,f70,f75,f80,f85,f90,f95,f104,f110,f123,f137,f159,f247,f265,f269,f281])).
% 0.21/0.46  fof(f281,plain,(
% 0.21/0.46    ~spl5_25 | ~spl5_24 | spl5_3 | ~spl5_19 | ~spl5_11 | ~spl5_23),
% 0.21/0.46    inference(avatar_split_clause,[],[f280,f213,f101,f156,f57,f221,f225])).
% 0.21/0.46  fof(f225,plain,(
% 0.21/0.46    spl5_25 <=> v1_relat_1(k6_relat_1(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.46  fof(f221,plain,(
% 0.21/0.46    spl5_24 <=> v1_funct_1(k6_relat_1(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    spl5_3 <=> sK2 = k6_relat_1(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.46  fof(f156,plain,(
% 0.21/0.46    spl5_19 <=> r1_tarski(sK0,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    spl5_11 <=> sK1 = k5_relat_1(k6_relat_1(sK0),sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.46  fof(f213,plain,(
% 0.21/0.46    spl5_23 <=> ! [X0] : (k1_relat_1(X0) != sK0 | sK2 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sK1 != k5_relat_1(X0,sK1) | ~r1_tarski(k2_relat_1(X0),sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.21/0.46  fof(f280,plain,(
% 0.21/0.46    ~r1_tarski(sK0,sK0) | sK2 = k6_relat_1(sK0) | ~v1_funct_1(k6_relat_1(sK0)) | ~v1_relat_1(k6_relat_1(sK0)) | (~spl5_11 | ~spl5_23)),
% 0.21/0.46    inference(forward_demodulation,[],[f279,f30])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.46  fof(f279,plain,(
% 0.21/0.46    sK2 = k6_relat_1(sK0) | ~v1_funct_1(k6_relat_1(sK0)) | ~v1_relat_1(k6_relat_1(sK0)) | ~r1_tarski(k2_relat_1(k6_relat_1(sK0)),sK0) | (~spl5_11 | ~spl5_23)),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f278])).
% 0.21/0.46  fof(f278,plain,(
% 0.21/0.46    sK0 != sK0 | sK2 = k6_relat_1(sK0) | ~v1_funct_1(k6_relat_1(sK0)) | ~v1_relat_1(k6_relat_1(sK0)) | ~r1_tarski(k2_relat_1(k6_relat_1(sK0)),sK0) | (~spl5_11 | ~spl5_23)),
% 0.21/0.46    inference(forward_demodulation,[],[f277,f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f277,plain,(
% 0.21/0.46    sK2 = k6_relat_1(sK0) | ~v1_funct_1(k6_relat_1(sK0)) | ~v1_relat_1(k6_relat_1(sK0)) | sK0 != k1_relat_1(k6_relat_1(sK0)) | ~r1_tarski(k2_relat_1(k6_relat_1(sK0)),sK0) | (~spl5_11 | ~spl5_23)),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f276])).
% 0.21/0.46  fof(f276,plain,(
% 0.21/0.46    sK1 != sK1 | sK2 = k6_relat_1(sK0) | ~v1_funct_1(k6_relat_1(sK0)) | ~v1_relat_1(k6_relat_1(sK0)) | sK0 != k1_relat_1(k6_relat_1(sK0)) | ~r1_tarski(k2_relat_1(k6_relat_1(sK0)),sK0) | (~spl5_11 | ~spl5_23)),
% 0.21/0.46    inference(superposition,[],[f214,f103])).
% 0.21/0.46  fof(f103,plain,(
% 0.21/0.46    sK1 = k5_relat_1(k6_relat_1(sK0),sK1) | ~spl5_11),
% 0.21/0.46    inference(avatar_component_clause,[],[f101])).
% 0.21/0.46  fof(f214,plain,(
% 0.21/0.46    ( ! [X0] : (sK1 != k5_relat_1(X0,sK1) | sK2 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) != sK0 | ~r1_tarski(k2_relat_1(X0),sK0)) ) | ~spl5_23),
% 0.21/0.46    inference(avatar_component_clause,[],[f213])).
% 0.21/0.46  fof(f269,plain,(
% 0.21/0.46    spl5_25),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f266])).
% 0.21/0.46  fof(f266,plain,(
% 0.21/0.46    $false | spl5_25),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f27,f227])).
% 0.21/0.46  fof(f227,plain,(
% 0.21/0.46    ~v1_relat_1(k6_relat_1(sK0)) | spl5_25),
% 0.21/0.46    inference(avatar_component_clause,[],[f225])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.46  fof(f265,plain,(
% 0.21/0.46    spl5_24),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f262])).
% 0.21/0.46  fof(f262,plain,(
% 0.21/0.46    $false | spl5_24),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f28,f223])).
% 0.21/0.46  fof(f223,plain,(
% 0.21/0.46    ~v1_funct_1(k6_relat_1(sK0)) | spl5_24),
% 0.21/0.46    inference(avatar_component_clause,[],[f221])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f247,plain,(
% 0.21/0.46    ~spl5_5 | ~spl5_2 | ~spl5_9 | ~spl5_10 | ~spl5_1 | ~spl5_6 | spl5_23 | ~spl5_4 | ~spl5_7 | ~spl5_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f246,f82,f77,f62,f213,f72,f47,f92,f87,f52,f67])).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    spl5_5 <=> v2_funct_1(sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    spl5_2 <=> v1_relat_1(sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.46  fof(f87,plain,(
% 0.21/0.46    spl5_9 <=> v1_funct_1(sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.46  fof(f92,plain,(
% 0.21/0.46    spl5_10 <=> v1_relat_1(sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    spl5_1 <=> v1_funct_1(sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    spl5_6 <=> r1_tarski(k2_relat_1(sK2),sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    spl5_4 <=> sK1 = k5_relat_1(sK2,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    spl5_7 <=> sK0 = k1_relat_1(sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.46  fof(f82,plain,(
% 0.21/0.46    spl5_8 <=> sK0 = k1_relat_1(sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.46  fof(f246,plain,(
% 0.21/0.46    ( ! [X0] : (k1_relat_1(X0) != sK0 | ~r1_tarski(k2_relat_1(sK2),sK0) | ~r1_tarski(k2_relat_1(X0),sK0) | sK1 != k5_relat_1(X0,sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | sK2 = X0 | ~v2_funct_1(sK1)) ) | (~spl5_4 | ~spl5_7 | ~spl5_8)),
% 0.21/0.46    inference(forward_demodulation,[],[f245,f79])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    sK0 = k1_relat_1(sK2) | ~spl5_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f77])).
% 0.21/0.46  fof(f245,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),sK0) | ~r1_tarski(k2_relat_1(X0),sK0) | sK1 != k5_relat_1(X0,sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k1_relat_1(X0) != k1_relat_1(sK2) | ~v1_relat_1(sK1) | sK2 = X0 | ~v2_funct_1(sK1)) ) | (~spl5_4 | ~spl5_8)),
% 0.21/0.46    inference(forward_demodulation,[],[f244,f84])).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    sK0 = k1_relat_1(sK1) | ~spl5_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f82])).
% 0.21/0.46  fof(f244,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),sK0) | sK1 != k5_relat_1(X0,sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~r1_tarski(k2_relat_1(sK2),k1_relat_1(sK1)) | k1_relat_1(X0) != k1_relat_1(sK2) | ~v1_relat_1(sK1) | sK2 = X0 | ~v2_funct_1(sK1)) ) | (~spl5_4 | ~spl5_8)),
% 0.21/0.46    inference(forward_demodulation,[],[f201,f84])).
% 0.21/0.46  fof(f201,plain,(
% 0.21/0.46    ( ! [X0] : (sK1 != k5_relat_1(X0,sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(sK1)) | ~r1_tarski(k2_relat_1(sK2),k1_relat_1(sK1)) | k1_relat_1(X0) != k1_relat_1(sK2) | ~v1_relat_1(sK1) | sK2 = X0 | ~v2_funct_1(sK1)) ) | ~spl5_4),
% 0.21/0.46    inference(superposition,[],[f41,f64])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    sK1 = k5_relat_1(sK2,sK1) | ~spl5_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f62])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(X2) | ~v1_relat_1(X0) | X1 = X2 | ~v2_funct_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0] : ((v2_funct_1(X0) <=> ! [X1] : (! [X2] : (X1 = X2 | k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(flattening,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0] : ((v2_funct_1(X0) <=> ! [X1] : (! [X2] : ((X1 = X2 | (k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))) => X1 = X2)))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_funct_1)).
% 0.21/0.46  fof(f159,plain,(
% 0.21/0.46    ~spl5_10 | ~spl5_14 | spl5_19 | ~spl5_7 | ~spl5_15),
% 0.21/0.46    inference(avatar_split_clause,[],[f152,f135,f77,f156,f120,f92])).
% 0.21/0.46  fof(f120,plain,(
% 0.21/0.46    spl5_14 <=> r1_tarski(sK2,sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.46  fof(f135,plain,(
% 0.21/0.46    spl5_15 <=> ! [X0] : (r1_tarski(sK0,k1_relat_1(X0)) | ~r1_tarski(sK2,X0) | ~v1_relat_1(X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.46  fof(f152,plain,(
% 0.21/0.46    r1_tarski(sK0,sK0) | ~r1_tarski(sK2,sK2) | ~v1_relat_1(sK2) | (~spl5_7 | ~spl5_15)),
% 0.21/0.46    inference(superposition,[],[f136,f79])).
% 0.21/0.46  fof(f136,plain,(
% 0.21/0.46    ( ! [X0] : (r1_tarski(sK0,k1_relat_1(X0)) | ~r1_tarski(sK2,X0) | ~v1_relat_1(X0)) ) | ~spl5_15),
% 0.21/0.46    inference(avatar_component_clause,[],[f135])).
% 0.21/0.46  fof(f137,plain,(
% 0.21/0.46    ~spl5_10 | spl5_15 | ~spl5_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f128,f77,f135,f92])).
% 0.21/0.46  fof(f128,plain,(
% 0.21/0.46    ( ! [X0] : (r1_tarski(sK0,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~r1_tarski(sK2,X0) | ~v1_relat_1(sK2)) ) | ~spl5_7),
% 0.21/0.46    inference(superposition,[],[f32,f79])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(flattening,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.46  fof(f123,plain,(
% 0.21/0.46    ~spl5_10 | spl5_14 | ~spl5_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f118,f107,f120,f92])).
% 0.21/0.46  fof(f107,plain,(
% 0.21/0.46    spl5_12 <=> sK2 = k5_relat_1(k6_relat_1(sK0),sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.46  fof(f118,plain,(
% 0.21/0.46    r1_tarski(sK2,sK2) | ~v1_relat_1(sK2) | ~spl5_12),
% 0.21/0.46    inference(superposition,[],[f45,f109])).
% 0.21/0.46  fof(f109,plain,(
% 0.21/0.46    sK2 = k5_relat_1(k6_relat_1(sK0),sK2) | ~spl5_12),
% 0.21/0.46    inference(avatar_component_clause,[],[f107])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).
% 0.21/0.46  fof(f110,plain,(
% 0.21/0.46    spl5_12 | ~spl5_7 | ~spl5_10),
% 0.21/0.46    inference(avatar_split_clause,[],[f105,f92,f77,f107])).
% 0.21/0.46  fof(f105,plain,(
% 0.21/0.46    sK2 = k5_relat_1(k6_relat_1(sK0),sK2) | (~spl5_7 | ~spl5_10)),
% 0.21/0.46    inference(forward_demodulation,[],[f97,f79])).
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    sK2 = k5_relat_1(k6_relat_1(k1_relat_1(sK2)),sK2) | ~spl5_10),
% 0.21/0.46    inference(resolution,[],[f31,f94])).
% 0.21/0.46  fof(f94,plain,(
% 0.21/0.46    v1_relat_1(sK2) | ~spl5_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f92])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 0.21/0.46  fof(f104,plain,(
% 0.21/0.46    spl5_11 | ~spl5_2 | ~spl5_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f99,f82,f52,f101])).
% 0.21/0.46  fof(f99,plain,(
% 0.21/0.46    sK1 = k5_relat_1(k6_relat_1(sK0),sK1) | (~spl5_2 | ~spl5_8)),
% 0.21/0.46    inference(forward_demodulation,[],[f96,f84])).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) | ~spl5_2),
% 0.21/0.46    inference(resolution,[],[f31,f54])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    v1_relat_1(sK1) | ~spl5_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f52])).
% 0.21/0.46  fof(f95,plain,(
% 0.21/0.46    spl5_10),
% 0.21/0.46    inference(avatar_split_clause,[],[f17,f92])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    v1_relat_1(sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ? [X0,X1] : (? [X2] : (k6_relat_1(X0) != X2 & k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.46    inference(flattening,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ? [X0,X1] : (? [X2] : ((k6_relat_1(X0) != X2 & (k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0)) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 0.21/0.46    inference(negated_conjecture,[],[f7])).
% 0.21/0.46  fof(f7,conjecture,(
% 0.21/0.46    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_1)).
% 0.21/0.46  fof(f90,plain,(
% 0.21/0.46    spl5_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f18,f87])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    v1_funct_1(sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    spl5_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f19,f82])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    sK0 = k1_relat_1(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f80,plain,(
% 0.21/0.46    spl5_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f20,f77])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    sK0 = k1_relat_1(sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    spl5_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f21,f72])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    r1_tarski(k2_relat_1(sK2),sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    spl5_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f22,f67])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    v2_funct_1(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    spl5_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f23,f62])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    sK1 = k5_relat_1(sK2,sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    ~spl5_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f24,f57])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    sK2 != k6_relat_1(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    spl5_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f25,f52])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    v1_relat_1(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    spl5_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f26,f47])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    v1_funct_1(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (21802)------------------------------
% 0.21/0.46  % (21802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (21802)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (21802)Memory used [KB]: 6268
% 0.21/0.46  % (21802)Time elapsed: 0.056 s
% 0.21/0.46  % (21802)------------------------------
% 0.21/0.46  % (21802)------------------------------
% 0.21/0.46  % (21786)Success in time 0.097 s
%------------------------------------------------------------------------------
