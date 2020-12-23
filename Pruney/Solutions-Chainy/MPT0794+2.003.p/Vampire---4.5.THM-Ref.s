%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 219 expanded)
%              Number of leaves         :   17 (  82 expanded)
%              Depth                    :   12
%              Number of atoms          :  407 (1002 expanded)
%              Number of equality atoms :   45 ( 145 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f169,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f39,f43,f47,f54,f58,f77,f81,f87,f94,f111,f123,f127,f138,f165])).

fof(f165,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | spl8_5
    | ~ spl8_7
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_15 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | spl8_5
    | ~ spl8_7
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f163,f53])).

fof(f53,plain,
    ( sK3 != sK4
    | spl8_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl8_5
  <=> sK3 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f163,plain,
    ( sK3 = sK4
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_7
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_15 ),
    inference(forward_demodulation,[],[f162,f147])).

fof(f147,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK3))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_7
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f146,f34])).

fof(f34,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl8_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f146,plain,
    ( ~ v1_relat_1(sK2)
    | sK3 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK3))
    | ~ spl8_2
    | ~ spl8_7
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f145,f76])).

fof(f76,plain,
    ( v2_funct_1(sK2)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl8_7
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f145,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK3 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK3))
    | ~ spl8_2
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f143,f38])).

fof(f38,plain,
    ( v1_funct_1(sK2)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl8_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f143,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK3 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK3))
    | ~ spl8_14 ),
    inference(resolution,[],[f126,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

fof(f126,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl8_14
  <=> r2_hidden(sK3,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f162,plain,
    ( sK4 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK3))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_7
    | ~ spl8_10
    | ~ spl8_15 ),
    inference(forward_demodulation,[],[f161,f90])).

fof(f90,plain,
    ( k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl8_10
  <=> k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f161,plain,
    ( sK4 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK4))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_7
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f160,f34])).

fof(f160,plain,
    ( ~ v1_relat_1(sK2)
    | sK4 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK4))
    | ~ spl8_2
    | ~ spl8_7
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f159,f76])).

fof(f159,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK4 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK4))
    | ~ spl8_2
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f157,f38])).

fof(f157,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK4 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK4))
    | ~ spl8_15 ),
    inference(resolution,[],[f137,f30])).

fof(f137,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl8_15
  <=> r2_hidden(sK4,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f138,plain,
    ( spl8_15
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f121,f109,f85,f136])).

fof(f85,plain,
    ( spl8_9
  <=> k3_relat_1(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f109,plain,
    ( spl8_13
  <=> sP7(sK4,sK3,sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f121,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(forward_demodulation,[],[f117,f86])).

fof(f86,plain,
    ( k3_relat_1(sK0) = k1_relat_1(sK2)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f85])).

fof(f117,plain,
    ( r2_hidden(sK4,k3_relat_1(sK0))
    | ~ spl8_13 ),
    inference(resolution,[],[f110,f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP7(X4,X3,X2,X1,X0)
      | r2_hidden(X4,k3_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k2_relat_1(X2) = k3_relat_1(X1)
                  & k1_relat_1(X2) = k3_relat_1(X0) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k2_relat_1(X2) = k3_relat_1(X1)
                  & k1_relat_1(X2) = k3_relat_1(X0) ) )
              | ~ v1_funct_1(X2)
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
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k2_relat_1(X2) = k3_relat_1(X1)
                  & k1_relat_1(X2) = k3_relat_1(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_wellord1)).

fof(f110,plain,
    ( sP7(sK4,sK3,sK2,sK1,sK0)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f109])).

fof(f127,plain,
    ( spl8_14
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f120,f109,f85,f125])).

fof(f120,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(forward_demodulation,[],[f116,f86])).

fof(f116,plain,
    ( r2_hidden(sK3,k3_relat_1(sK0))
    | ~ spl8_13 ),
    inference(resolution,[],[f110,f20])).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP7(X4,X3,X2,X1,X0)
      | r2_hidden(X3,k3_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f123,plain,
    ( spl8_11
    | ~ spl8_13 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | spl8_11
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f118,f93])).

fof(f93,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)),sK1)
    | spl8_11 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl8_11
  <=> r2_hidden(k4_tarski(k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f118,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)),sK1)
    | ~ spl8_13 ),
    inference(resolution,[],[f110,f22])).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP7(X4,X3,X2,X1,X0)
      | r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f111,plain,
    ( spl8_13
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f103,f79,f56,f45,f41,f37,f33,f109])).

fof(f41,plain,
    ( spl8_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f45,plain,
    ( spl8_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f56,plain,
    ( spl8_6
  <=> r3_wellord1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f79,plain,
    ( spl8_8
  <=> r2_hidden(k4_tarski(sK3,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f103,plain,
    ( sP7(sK4,sK3,sK2,sK1,sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f102,f42])).

fof(f42,plain,
    ( v1_relat_1(sK1)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f102,plain,
    ( sP7(sK4,sK3,sK2,sK1,sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f101,f38])).

fof(f101,plain,
    ( ~ v1_funct_1(sK2)
    | sP7(sK4,sK3,sK2,sK1,sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f100,f34])).

fof(f100,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | sP7(sK4,sK3,sK2,sK1,sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(resolution,[],[f83,f57])).

fof(f57,plain,
    ( r3_wellord1(sK0,sK1,sK2)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f56])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( ~ r3_wellord1(sK0,X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | sP7(sK4,sK3,X1,X0,sK0)
        | ~ v1_relat_1(X0) )
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f82,f46])).

fof(f46,plain,
    ( v1_relat_1(sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | sP7(sK4,sK3,X1,X0,sK0)
        | ~ v1_relat_1(sK0)
        | ~ r3_wellord1(sK0,X0,X1) )
    | ~ spl8_8 ),
    inference(resolution,[],[f80,f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | sP7(X4,X3,X2,X1,X0)
      | ~ v1_relat_1(X0)
      | ~ r3_wellord1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f80,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),sK0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f79])).

fof(f94,plain,
    ( spl8_10
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f11,f92,f89])).

fof(f11,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)),sK1)
    | k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3,X4] :
                  ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                    | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                  & X3 != X4
                  & r2_hidden(k4_tarski(X3,X4),X0) )
              & r3_wellord1(X0,X1,X2)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3,X4] :
                  ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                    | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                  & X3 != X4
                  & r2_hidden(k4_tarski(X3,X4),X0) )
              & r3_wellord1(X0,X1,X2)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( r3_wellord1(X0,X1,X2)
                 => ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                     => ( ( k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
                          & r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                        | X3 = X4 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
               => ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X0)
                   => ( ( k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
                        & r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                      | X3 = X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_wellord1)).

fof(f87,plain,
    ( spl8_9
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f65,f56,f45,f41,f37,f33,f85])).

fof(f65,plain,
    ( k3_relat_1(sK0) = k1_relat_1(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f64,f46])).

fof(f64,plain,
    ( k3_relat_1(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f63,f38])).

fof(f63,plain,
    ( ~ v1_funct_1(sK2)
    | k3_relat_1(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK0)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f62,f34])).

fof(f62,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k3_relat_1(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK0)
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f59,f42])).

fof(f59,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k3_relat_1(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK0)
    | ~ spl8_6 ),
    inference(resolution,[],[f57,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_wellord1(X0,X1,X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f81,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f12,f79])).

fof(f12,plain,(
    r2_hidden(k4_tarski(sK3,sK4),sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f77,plain,
    ( spl8_7
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f73,f56,f45,f41,f37,f33,f75])).

fof(f73,plain,
    ( v2_funct_1(sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f72,f46])).

fof(f72,plain,
    ( v2_funct_1(sK2)
    | ~ v1_relat_1(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f71,f38])).

fof(f71,plain,
    ( ~ v1_funct_1(sK2)
    | v2_funct_1(sK2)
    | ~ v1_relat_1(sK0)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f70,f34])).

fof(f70,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2)
    | ~ v1_relat_1(sK0)
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f61,f42])).

fof(f61,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2)
    | ~ v1_relat_1(sK0)
    | ~ spl8_6 ),
    inference(resolution,[],[f57,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_wellord1(X0,X1,X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | v2_funct_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f58,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f16,f56])).

fof(f16,plain,(
    r3_wellord1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f54,plain,(
    ~ spl8_5 ),
    inference(avatar_split_clause,[],[f13,f52])).

fof(f13,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f6])).

fof(f47,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f18,f45])).

fof(f18,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f43,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f17,f41])).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f39,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f15,f37])).

fof(f15,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f35,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f14,f33])).

fof(f14,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:49:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (14213)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (14204)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (14219)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (14209)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (14211)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (14204)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f35,f39,f43,f47,f54,f58,f77,f81,f87,f94,f111,f123,f127,f138,f165])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    ~spl8_1 | ~spl8_2 | spl8_5 | ~spl8_7 | ~spl8_10 | ~spl8_14 | ~spl8_15),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f164])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    $false | (~spl8_1 | ~spl8_2 | spl8_5 | ~spl8_7 | ~spl8_10 | ~spl8_14 | ~spl8_15)),
% 0.21/0.50    inference(subsumption_resolution,[],[f163,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    sK3 != sK4 | spl8_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    spl8_5 <=> sK3 = sK4),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    sK3 = sK4 | (~spl8_1 | ~spl8_2 | ~spl8_7 | ~spl8_10 | ~spl8_14 | ~spl8_15)),
% 0.21/0.50    inference(forward_demodulation,[],[f162,f147])).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    sK3 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK3)) | (~spl8_1 | ~spl8_2 | ~spl8_7 | ~spl8_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f146,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    v1_relat_1(sK2) | ~spl8_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    spl8_1 <=> v1_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    ~v1_relat_1(sK2) | sK3 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK3)) | (~spl8_2 | ~spl8_7 | ~spl8_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f145,f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    v2_funct_1(sK2) | ~spl8_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f75])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    spl8_7 <=> v2_funct_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | sK3 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK3)) | (~spl8_2 | ~spl8_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f143,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    v1_funct_1(sK2) | ~spl8_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    spl8_2 <=> v1_funct_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | sK3 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK3)) | ~spl8_14),
% 0.21/0.50    inference(resolution,[],[f126,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~v1_relat_1(X1) | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    r2_hidden(sK3,k1_relat_1(sK2)) | ~spl8_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f125])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    spl8_14 <=> r2_hidden(sK3,k1_relat_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    sK4 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK3)) | (~spl8_1 | ~spl8_2 | ~spl8_7 | ~spl8_10 | ~spl8_15)),
% 0.21/0.50    inference(forward_demodulation,[],[f161,f90])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4) | ~spl8_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f89])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    spl8_10 <=> k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    sK4 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK4)) | (~spl8_1 | ~spl8_2 | ~spl8_7 | ~spl8_15)),
% 0.21/0.50    inference(subsumption_resolution,[],[f160,f34])).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    ~v1_relat_1(sK2) | sK4 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK4)) | (~spl8_2 | ~spl8_7 | ~spl8_15)),
% 0.21/0.50    inference(subsumption_resolution,[],[f159,f76])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | sK4 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK4)) | (~spl8_2 | ~spl8_15)),
% 0.21/0.50    inference(subsumption_resolution,[],[f157,f38])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | sK4 = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK4)) | ~spl8_15),
% 0.21/0.50    inference(resolution,[],[f137,f30])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    r2_hidden(sK4,k1_relat_1(sK2)) | ~spl8_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f136])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    spl8_15 <=> r2_hidden(sK4,k1_relat_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    spl8_15 | ~spl8_9 | ~spl8_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f121,f109,f85,f136])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    spl8_9 <=> k3_relat_1(sK0) = k1_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    spl8_13 <=> sP7(sK4,sK3,sK2,sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    r2_hidden(sK4,k1_relat_1(sK2)) | (~spl8_9 | ~spl8_13)),
% 0.21/0.50    inference(forward_demodulation,[],[f117,f86])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    k3_relat_1(sK0) = k1_relat_1(sK2) | ~spl8_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f85])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    r2_hidden(sK4,k3_relat_1(sK0)) | ~spl8_13),
% 0.21/0.50    inference(resolution,[],[f110,f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (~sP7(X4,X3,X2,X1,X0) | r2_hidden(X4,k3_relat_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r3_wellord1(X0,X1,X2) <=> (! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) <=> (r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0)))) & v2_funct_1(X2) & k2_relat_1(X2) = k3_relat_1(X1) & k1_relat_1(X2) = k3_relat_1(X0))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f7])).
% 0.21/0.50  fof(f7,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r3_wellord1(X0,X1,X2) <=> (! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) <=> (r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0)))) & v2_funct_1(X2) & k2_relat_1(X2) = k3_relat_1(X1) & k1_relat_1(X2) = k3_relat_1(X0))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r3_wellord1(X0,X1,X2) <=> (! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) <=> (r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0)))) & v2_funct_1(X2) & k2_relat_1(X2) = k3_relat_1(X1) & k1_relat_1(X2) = k3_relat_1(X0))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_wellord1)).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    sP7(sK4,sK3,sK2,sK1,sK0) | ~spl8_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f109])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    spl8_14 | ~spl8_9 | ~spl8_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f120,f109,f85,f125])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    r2_hidden(sK3,k1_relat_1(sK2)) | (~spl8_9 | ~spl8_13)),
% 0.21/0.50    inference(forward_demodulation,[],[f116,f86])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    r2_hidden(sK3,k3_relat_1(sK0)) | ~spl8_13),
% 0.21/0.50    inference(resolution,[],[f110,f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (~sP7(X4,X3,X2,X1,X0) | r2_hidden(X3,k3_relat_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    spl8_11 | ~spl8_13),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f122])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    $false | (spl8_11 | ~spl8_13)),
% 0.21/0.50    inference(subsumption_resolution,[],[f118,f93])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    ~r2_hidden(k4_tarski(k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)),sK1) | spl8_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f92])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    spl8_11 <=> r2_hidden(k4_tarski(k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    r2_hidden(k4_tarski(k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)),sK1) | ~spl8_13),
% 0.21/0.50    inference(resolution,[],[f110,f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (~sP7(X4,X3,X2,X1,X0) | r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    spl8_13 | ~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_6 | ~spl8_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f103,f79,f56,f45,f41,f37,f33,f109])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    spl8_3 <=> v1_relat_1(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    spl8_4 <=> v1_relat_1(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    spl8_6 <=> r3_wellord1(sK0,sK1,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    spl8_8 <=> r2_hidden(k4_tarski(sK3,sK4),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    sP7(sK4,sK3,sK2,sK1,sK0) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_6 | ~spl8_8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f102,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    v1_relat_1(sK1) | ~spl8_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f41])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    sP7(sK4,sK3,sK2,sK1,sK0) | ~v1_relat_1(sK1) | (~spl8_1 | ~spl8_2 | ~spl8_4 | ~spl8_6 | ~spl8_8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f101,f38])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    ~v1_funct_1(sK2) | sP7(sK4,sK3,sK2,sK1,sK0) | ~v1_relat_1(sK1) | (~spl8_1 | ~spl8_4 | ~spl8_6 | ~spl8_8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f100,f34])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | sP7(sK4,sK3,sK2,sK1,sK0) | ~v1_relat_1(sK1) | (~spl8_4 | ~spl8_6 | ~spl8_8)),
% 0.21/0.50    inference(resolution,[],[f83,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    r3_wellord1(sK0,sK1,sK2) | ~spl8_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f56])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r3_wellord1(sK0,X0,X1) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | sP7(sK4,sK3,X1,X0,sK0) | ~v1_relat_1(X0)) ) | (~spl8_4 | ~spl8_8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f82,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    v1_relat_1(sK0) | ~spl8_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f45])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | sP7(sK4,sK3,X1,X0,sK0) | ~v1_relat_1(sK0) | ~r3_wellord1(sK0,X0,X1)) ) | ~spl8_8),
% 0.21/0.50    inference(resolution,[],[f80,f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X4),X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | sP7(X4,X3,X2,X1,X0) | ~v1_relat_1(X0) | ~r3_wellord1(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    r2_hidden(k4_tarski(sK3,sK4),sK0) | ~spl8_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f79])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    spl8_10 | ~spl8_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f11,f92,f89])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ~r2_hidden(k4_tarski(k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)),sK1) | k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4)),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3,X4] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),X0)) & r3_wellord1(X0,X1,X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f5])).
% 0.21/0.50  fof(f5,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : ((? [X3,X4] : (((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) & X3 != X4) & r2_hidden(k4_tarski(X3,X4),X0)) & r3_wellord1(X0,X1,X2)) & (v1_funct_1(X2) & v1_relat_1(X2))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r3_wellord1(X0,X1,X2) => ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) => ((k1_funct_1(X2,X3) != k1_funct_1(X2,X4) & r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) | X3 = X4))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f3])).
% 0.21/0.50  fof(f3,conjecture,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r3_wellord1(X0,X1,X2) => ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) => ((k1_funct_1(X2,X3) != k1_funct_1(X2,X4) & r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) | X3 = X4))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_wellord1)).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    spl8_9 | ~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f65,f56,f45,f41,f37,f33,f85])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    k3_relat_1(sK0) = k1_relat_1(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f64,f46])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    k3_relat_1(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK0) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f63,f38])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ~v1_funct_1(sK2) | k3_relat_1(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK0) | (~spl8_1 | ~spl8_3 | ~spl8_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f62,f34])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k3_relat_1(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK0) | (~spl8_3 | ~spl8_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f59,f42])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ~v1_relat_1(sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k3_relat_1(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK0) | ~spl8_6),
% 0.21/0.50    inference(resolution,[],[f57,f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r3_wellord1(X0,X1,X2) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X2) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    spl8_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f12,f79])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    r2_hidden(k4_tarski(sK3,sK4),sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    spl8_7 | ~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f73,f56,f45,f41,f37,f33,f75])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    v2_funct_1(sK2) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f72,f46])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    v2_funct_1(sK2) | ~v1_relat_1(sK0) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f71,f38])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ~v1_funct_1(sK2) | v2_funct_1(sK2) | ~v1_relat_1(sK0) | (~spl8_1 | ~spl8_3 | ~spl8_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f70,f34])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | v2_funct_1(sK2) | ~v1_relat_1(sK0) | (~spl8_3 | ~spl8_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f61,f42])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ~v1_relat_1(sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | v2_funct_1(sK2) | ~v1_relat_1(sK0) | ~spl8_6),
% 0.21/0.50    inference(resolution,[],[f57,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r3_wellord1(X0,X1,X2) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | v2_funct_1(X2) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    spl8_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f16,f56])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    r3_wellord1(sK0,sK1,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ~spl8_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f13,f52])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    sK3 != sK4),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    spl8_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f18,f45])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    v1_relat_1(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    spl8_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f17,f41])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    v1_relat_1(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    spl8_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f15,f37])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    v1_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    spl8_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f14,f33])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    v1_relat_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (14204)------------------------------
% 0.21/0.50  % (14204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (14204)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (14204)Memory used [KB]: 6268
% 0.21/0.50  % (14204)Time elapsed: 0.063 s
% 0.21/0.50  % (14204)------------------------------
% 0.21/0.50  % (14204)------------------------------
% 0.21/0.50  % (14201)Success in time 0.137 s
%------------------------------------------------------------------------------
