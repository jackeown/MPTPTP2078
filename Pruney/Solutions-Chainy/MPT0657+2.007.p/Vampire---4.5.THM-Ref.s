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
% DateTime   : Thu Dec  3 12:53:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 203 expanded)
%              Number of leaves         :   24 (  87 expanded)
%              Depth                    :    9
%              Number of atoms          :  367 ( 949 expanded)
%              Number of equality atoms :   93 ( 300 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f381,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f51,f56,f61,f66,f71,f76,f81,f91,f99,f117,f167,f187,f190,f240,f380])).

fof(f380,plain,
    ( ~ spl2_2
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_12
    | ~ spl2_19
    | ~ spl2_21
    | ~ spl2_22
    | spl2_28 ),
    inference(avatar_contradiction_clause,[],[f379])).

fof(f379,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_12
    | ~ spl2_19
    | ~ spl2_21
    | ~ spl2_22
    | spl2_28 ),
    inference(subsumption_resolution,[],[f378,f50])).

fof(f50,plain,
    ( k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl2_2
  <=> k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f378,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(sK1,sK0)
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_12
    | ~ spl2_19
    | ~ spl2_21
    | ~ spl2_22
    | spl2_28 ),
    inference(forward_demodulation,[],[f377,f177])).

fof(f177,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl2_21
  <=> k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f377,plain,
    ( k5_relat_1(sK1,sK0) != k6_relat_1(k1_relat_1(k4_relat_1(sK0)))
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_12
    | ~ spl2_19
    | ~ spl2_22
    | spl2_28 ),
    inference(unit_resulting_resolution,[],[f70,f65,f80,f75,f166,f186,f110,f239,f41])).

fof(f41,plain,(
    ! [X2,X3,X1] :
      ( k5_relat_1(X2,X3) != k6_relat_1(k2_relat_1(X1))
      | X1 = X3
      | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | k5_relat_1(X2,X3) != k6_relat_1(X0)
      | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
      | k2_relat_1(X1) != X0
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X1 = X3
              | k5_relat_1(X2,X3) != k6_relat_1(X0)
              | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
              | k2_relat_1(X1) != X0
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X1 = X3
              | k5_relat_1(X2,X3) != k6_relat_1(X0)
              | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
              | k2_relat_1(X1) != X0
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
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
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_relat_1(X3) )
             => ( ( k5_relat_1(X2,X3) = k6_relat_1(X0)
                  & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
                  & k2_relat_1(X1) = X0 )
               => X1 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l72_funct_1)).

fof(f239,plain,
    ( sK1 != k4_relat_1(sK0)
    | spl2_28 ),
    inference(avatar_component_clause,[],[f237])).

fof(f237,plain,
    ( spl2_28
  <=> sK1 = k4_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f110,plain,
    ( k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,k4_relat_1(sK0))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl2_12
  <=> k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f186,plain,
    ( v1_funct_1(k4_relat_1(sK0))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl2_22
  <=> v1_funct_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f166,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl2_19
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f75,plain,
    ( v1_funct_1(sK0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl2_7
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f80,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl2_8
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f65,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl2_5
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f70,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl2_6
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f240,plain,
    ( ~ spl2_28
    | spl2_1
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f233,f88,f43,f237])).

fof(f43,plain,
    ( spl2_1
  <=> k2_funct_1(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f88,plain,
    ( spl2_9
  <=> k2_funct_1(sK0) = k4_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f233,plain,
    ( sK1 != k4_relat_1(sK0)
    | spl2_1
    | ~ spl2_9 ),
    inference(superposition,[],[f45,f90])).

fof(f90,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f88])).

fof(f45,plain,
    ( k2_funct_1(sK0) != sK1
    | spl2_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f190,plain,
    ( spl2_21
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f161,f78,f175])).

fof(f161,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))
    | ~ spl2_8 ),
    inference(resolution,[],[f80,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f187,plain,
    ( spl2_22
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f182,f88,f78,f73,f184])).

fof(f182,plain,
    ( v1_funct_1(k4_relat_1(sK0))
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f154,f90])).

fof(f154,plain,
    ( v1_funct_1(k2_funct_1(sK0))
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f75,f80,f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f167,plain,
    ( spl2_19
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f160,f78,f164])).

fof(f160,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f80,f40])).

fof(f40,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f117,plain,
    ( spl2_12
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f115,f96,f88,f108])).

fof(f96,plain,
    ( spl2_10
  <=> k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f115,plain,
    ( k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,k4_relat_1(sK0))
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(backward_demodulation,[],[f98,f90])).

fof(f98,plain,
    ( k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k2_relat_1(sK1))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f96])).

fof(f99,plain,
    ( spl2_10
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f94,f78,f73,f58,f53,f96])).

fof(f53,plain,
    ( spl2_3
  <=> k1_relat_1(sK0) = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f58,plain,
    ( spl2_4
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f94,plain,
    ( k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k2_relat_1(sK1))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f93,f55])).

fof(f55,plain,
    ( k1_relat_1(sK0) = k2_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f93,plain,
    ( k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0))
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f92,f80])).

fof(f92,plain,
    ( k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f83,f75])).

fof(f83,plain,
    ( k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f60,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f60,plain,
    ( v2_funct_1(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f91,plain,
    ( spl2_9
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f86,f78,f73,f58,f88])).

fof(f86,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f85,f80])).

fof(f85,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f82,f75])).

fof(f82,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f60,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f81,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f24,f78])).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k2_funct_1(sK0) != sK1
    & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0)
    & k1_relat_1(sK0) = k2_relat_1(sK1)
    & v2_funct_1(sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_funct_1(X0) != X1
            & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
            & k1_relat_1(X0) = k2_relat_1(X1)
            & v2_funct_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_funct_1(sK0) != X1
          & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(X1,sK0)
          & k2_relat_1(X1) = k1_relat_1(sK0)
          & v2_funct_1(sK0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( k2_funct_1(sK0) != X1
        & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(X1,sK0)
        & k2_relat_1(X1) = k1_relat_1(sK0)
        & v2_funct_1(sK0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_funct_1(sK0) != sK1
      & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0)
      & k1_relat_1(sK0) = k2_relat_1(sK1)
      & v2_funct_1(sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
                & k1_relat_1(X0) = k2_relat_1(X1)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f76,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f25,f73])).

fof(f25,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f26,f68])).

fof(f26,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f27,f63])).

fof(f27,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f28,f58])).

fof(f28,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f29,f53])).

fof(f29,plain,(
    k1_relat_1(sK0) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f30,f48])).

fof(f30,plain,(
    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f46,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f31,f43])).

fof(f31,plain,(
    k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:44:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.21/0.46  % (27042)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (27042)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % (27035)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f381,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f46,f51,f56,f61,f66,f71,f76,f81,f91,f99,f117,f167,f187,f190,f240,f380])).
% 0.21/0.47  fof(f380,plain,(
% 0.21/0.47    ~spl2_2 | ~spl2_5 | ~spl2_6 | ~spl2_7 | ~spl2_8 | ~spl2_12 | ~spl2_19 | ~spl2_21 | ~spl2_22 | spl2_28),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f379])).
% 0.21/0.47  fof(f379,plain,(
% 0.21/0.47    $false | (~spl2_2 | ~spl2_5 | ~spl2_6 | ~spl2_7 | ~spl2_8 | ~spl2_12 | ~spl2_19 | ~spl2_21 | ~spl2_22 | spl2_28)),
% 0.21/0.47    inference(subsumption_resolution,[],[f378,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0) | ~spl2_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    spl2_2 <=> k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.47  fof(f378,plain,(
% 0.21/0.47    k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(sK1,sK0) | (~spl2_5 | ~spl2_6 | ~spl2_7 | ~spl2_8 | ~spl2_12 | ~spl2_19 | ~spl2_21 | ~spl2_22 | spl2_28)),
% 0.21/0.47    inference(forward_demodulation,[],[f377,f177])).
% 0.21/0.47  fof(f177,plain,(
% 0.21/0.47    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) | ~spl2_21),
% 0.21/0.47    inference(avatar_component_clause,[],[f175])).
% 0.21/0.47  fof(f175,plain,(
% 0.21/0.47    spl2_21 <=> k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.21/0.47  fof(f377,plain,(
% 0.21/0.47    k5_relat_1(sK1,sK0) != k6_relat_1(k1_relat_1(k4_relat_1(sK0))) | (~spl2_5 | ~spl2_6 | ~spl2_7 | ~spl2_8 | ~spl2_12 | ~spl2_19 | ~spl2_22 | spl2_28)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f70,f65,f80,f75,f166,f186,f110,f239,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X2,X3,X1] : (k5_relat_1(X2,X3) != k6_relat_1(k2_relat_1(X1)) | X1 = X3 | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(equality_resolution,[],[f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (X1 = X3 | k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (! [X3] : (X1 = X3 | k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (! [X3] : ((X1 = X3 | (k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0)) | (~v1_funct_1(X3) | ~v1_relat_1(X3))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((k5_relat_1(X2,X3) = k6_relat_1(X0) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & k2_relat_1(X1) = X0) => X1 = X3))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l72_funct_1)).
% 0.21/0.47  fof(f239,plain,(
% 0.21/0.47    sK1 != k4_relat_1(sK0) | spl2_28),
% 0.21/0.47    inference(avatar_component_clause,[],[f237])).
% 0.21/0.47  fof(f237,plain,(
% 0.21/0.47    spl2_28 <=> sK1 = k4_relat_1(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,k4_relat_1(sK0)) | ~spl2_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f108])).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    spl2_12 <=> k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,k4_relat_1(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.47  fof(f186,plain,(
% 0.21/0.47    v1_funct_1(k4_relat_1(sK0)) | ~spl2_22),
% 0.21/0.47    inference(avatar_component_clause,[],[f184])).
% 0.21/0.47  fof(f184,plain,(
% 0.21/0.47    spl2_22 <=> v1_funct_1(k4_relat_1(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.21/0.47  fof(f166,plain,(
% 0.21/0.47    v1_relat_1(k4_relat_1(sK0)) | ~spl2_19),
% 0.21/0.47    inference(avatar_component_clause,[],[f164])).
% 0.21/0.47  fof(f164,plain,(
% 0.21/0.47    spl2_19 <=> v1_relat_1(k4_relat_1(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    v1_funct_1(sK0) | ~spl2_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f73])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    spl2_7 <=> v1_funct_1(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    v1_relat_1(sK0) | ~spl2_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f78])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    spl2_8 <=> v1_relat_1(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    v1_funct_1(sK1) | ~spl2_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f63])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    spl2_5 <=> v1_funct_1(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    v1_relat_1(sK1) | ~spl2_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f68])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    spl2_6 <=> v1_relat_1(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.47  fof(f240,plain,(
% 0.21/0.47    ~spl2_28 | spl2_1 | ~spl2_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f233,f88,f43,f237])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    spl2_1 <=> k2_funct_1(sK0) = sK1),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    spl2_9 <=> k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.47  fof(f233,plain,(
% 0.21/0.47    sK1 != k4_relat_1(sK0) | (spl2_1 | ~spl2_9)),
% 0.21/0.47    inference(superposition,[],[f45,f90])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    k2_funct_1(sK0) = k4_relat_1(sK0) | ~spl2_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f88])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    k2_funct_1(sK0) != sK1 | spl2_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f43])).
% 0.21/0.47  fof(f190,plain,(
% 0.21/0.47    spl2_21 | ~spl2_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f161,f78,f175])).
% 0.21/0.47  fof(f161,plain,(
% 0.21/0.47    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) | ~spl2_8),
% 0.21/0.47    inference(resolution,[],[f80,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.21/0.47  fof(f187,plain,(
% 0.21/0.47    spl2_22 | ~spl2_7 | ~spl2_8 | ~spl2_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f182,f88,f78,f73,f184])).
% 0.21/0.47  fof(f182,plain,(
% 0.21/0.47    v1_funct_1(k4_relat_1(sK0)) | (~spl2_7 | ~spl2_8 | ~spl2_9)),
% 0.21/0.47    inference(forward_demodulation,[],[f154,f90])).
% 0.21/0.47  fof(f154,plain,(
% 0.21/0.47    v1_funct_1(k2_funct_1(sK0)) | (~spl2_7 | ~spl2_8)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f75,f80,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.47  fof(f167,plain,(
% 0.21/0.47    spl2_19 | ~spl2_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f160,f78,f164])).
% 0.21/0.47  fof(f160,plain,(
% 0.21/0.47    v1_relat_1(k4_relat_1(sK0)) | ~spl2_8),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f80,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    spl2_12 | ~spl2_9 | ~spl2_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f115,f96,f88,f108])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    spl2_10 <=> k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k2_relat_1(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,k4_relat_1(sK0)) | (~spl2_9 | ~spl2_10)),
% 0.21/0.47    inference(backward_demodulation,[],[f98,f90])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k2_relat_1(sK1)) | ~spl2_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f96])).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    spl2_10 | ~spl2_3 | ~spl2_4 | ~spl2_7 | ~spl2_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f94,f78,f73,f58,f53,f96])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    spl2_3 <=> k1_relat_1(sK0) = k2_relat_1(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    spl2_4 <=> v2_funct_1(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k2_relat_1(sK1)) | (~spl2_3 | ~spl2_4 | ~spl2_7 | ~spl2_8)),
% 0.21/0.47    inference(forward_demodulation,[],[f93,f55])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    k1_relat_1(sK0) = k2_relat_1(sK1) | ~spl2_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f53])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) | (~spl2_4 | ~spl2_7 | ~spl2_8)),
% 0.21/0.47    inference(subsumption_resolution,[],[f92,f80])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl2_4 | ~spl2_7)),
% 0.21/0.47    inference(subsumption_resolution,[],[f83,f75])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl2_4),
% 0.21/0.47    inference(resolution,[],[f60,f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    v2_funct_1(sK0) | ~spl2_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f58])).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    spl2_9 | ~spl2_4 | ~spl2_7 | ~spl2_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f86,f78,f73,f58,f88])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    k2_funct_1(sK0) = k4_relat_1(sK0) | (~spl2_4 | ~spl2_7 | ~spl2_8)),
% 0.21/0.47    inference(subsumption_resolution,[],[f85,f80])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    k2_funct_1(sK0) = k4_relat_1(sK0) | ~v1_relat_1(sK0) | (~spl2_4 | ~spl2_7)),
% 0.21/0.47    inference(subsumption_resolution,[],[f82,f75])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    k2_funct_1(sK0) = k4_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl2_4),
% 0.21/0.47    inference(resolution,[],[f60,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    spl2_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f24,f78])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    v1_relat_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    (k2_funct_1(sK0) != sK1 & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0) & k1_relat_1(sK0) = k2_relat_1(sK1) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f22,f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k2_funct_1(sK0) != X1 & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(X1,sK0) & k2_relat_1(X1) = k1_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ? [X1] : (k2_funct_1(sK0) != X1 & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(X1,sK0) & k2_relat_1(X1) = k1_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(sK0) != sK1 & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0) & k1_relat_1(sK0) = k2_relat_1(sK1) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.21/0.47    inference(negated_conjecture,[],[f7])).
% 0.21/0.47  fof(f7,conjecture,(
% 0.21/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    spl2_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f25,f73])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    v1_funct_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    spl2_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f26,f68])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    v1_relat_1(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    spl2_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f27,f63])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    v1_funct_1(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    spl2_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f28,f58])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    v2_funct_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    spl2_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f29,f53])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    k1_relat_1(sK0) = k2_relat_1(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f30,f48])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ~spl2_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f31,f43])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    k2_funct_1(sK0) != sK1),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (27042)------------------------------
% 0.21/0.47  % (27042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (27042)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (27042)Memory used [KB]: 6396
% 0.21/0.47  % (27042)Time elapsed: 0.055 s
% 0.21/0.47  % (27042)------------------------------
% 0.21/0.47  % (27042)------------------------------
% 0.21/0.47  % (27026)Success in time 0.121 s
%------------------------------------------------------------------------------
