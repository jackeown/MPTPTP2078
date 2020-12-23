%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0581+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:15 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 100 expanded)
%              Number of leaves         :   14 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :  139 ( 374 expanded)
%              Number of equality atoms :   58 ( 203 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f134,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f26,f31,f36,f41,f45,f51,f55,f67,f130])).

fof(f130,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f128,f20])).

fof(f20,plain,
    ( k7_relat_1(sK0,k2_xboole_0(sK2,sK3)) != k7_relat_1(sK1,k2_xboole_0(sK2,sK3))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f18])).

fof(f18,plain,
    ( spl4_1
  <=> k7_relat_1(sK0,k2_xboole_0(sK2,sK3)) = k7_relat_1(sK1,k2_xboole_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f128,plain,
    ( k7_relat_1(sK0,k2_xboole_0(sK2,sK3)) = k7_relat_1(sK1,k2_xboole_0(sK2,sK3))
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f124,f54])).

fof(f54,plain,
    ( ! [X2,X3] : k7_relat_1(sK0,k2_xboole_0(X2,X3)) = k2_xboole_0(k7_relat_1(sK0,X2),k7_relat_1(sK0,X3))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl4_8
  <=> ! [X3,X2] : k7_relat_1(sK0,k2_xboole_0(X2,X3)) = k2_xboole_0(k7_relat_1(sK0,X2),k7_relat_1(sK0,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f124,plain,
    ( k7_relat_1(sK1,k2_xboole_0(sK2,sK3)) = k2_xboole_0(k7_relat_1(sK0,sK2),k7_relat_1(sK0,sK3))
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(superposition,[],[f66,f25])).

fof(f25,plain,
    ( k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f23])).

fof(f23,plain,
    ( spl4_2
  <=> k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f66,plain,
    ( ! [X1] : k7_relat_1(sK1,k2_xboole_0(sK2,X1)) = k2_xboole_0(k7_relat_1(sK0,sK2),k7_relat_1(sK1,X1))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl4_10
  <=> ! [X1] : k7_relat_1(sK1,k2_xboole_0(sK2,X1)) = k2_xboole_0(k7_relat_1(sK0,sK2),k7_relat_1(sK1,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f67,plain,
    ( spl4_10
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f57,f49,f28,f65])).

fof(f28,plain,
    ( spl4_3
  <=> k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f49,plain,
    ( spl4_7
  <=> ! [X1,X0] : k7_relat_1(sK1,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(sK1,X0),k7_relat_1(sK1,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f57,plain,
    ( ! [X1] : k7_relat_1(sK1,k2_xboole_0(sK2,X1)) = k2_xboole_0(k7_relat_1(sK0,sK2),k7_relat_1(sK1,X1))
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(superposition,[],[f50,f30])).

fof(f30,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f28])).

fof(f50,plain,
    ( ! [X0,X1] : k7_relat_1(sK1,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(sK1,X0),k7_relat_1(sK1,X1))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f49])).

fof(f55,plain,
    ( spl4_8
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f47,f43,f38,f53])).

fof(f38,plain,
    ( spl4_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f43,plain,
    ( spl4_6
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f47,plain,
    ( ! [X2,X3] : k7_relat_1(sK0,k2_xboole_0(X2,X3)) = k2_xboole_0(k7_relat_1(sK0,X2),k7_relat_1(sK0,X3))
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(resolution,[],[f44,f40])).

fof(f40,plain,
    ( v1_relat_1(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f38])).

fof(f44,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k7_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f43])).

fof(f51,plain,
    ( spl4_7
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f46,f43,f33,f49])).

fof(f33,plain,
    ( spl4_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f46,plain,
    ( ! [X0,X1] : k7_relat_1(sK1,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(sK1,X0),k7_relat_1(sK1,X1))
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(resolution,[],[f44,f35])).

fof(f35,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f33])).

fof(f45,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f16,f43])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_relat_1)).

fof(f41,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f11,f38])).

fof(f11,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( k7_relat_1(sK0,k2_xboole_0(sK2,sK3)) != k7_relat_1(sK1,k2_xboole_0(sK2,sK3))
    & k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3)
    & k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f9,f8,f7])).

fof(f7,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3] :
                ( k7_relat_1(X0,k2_xboole_0(X2,X3)) != k7_relat_1(X1,k2_xboole_0(X2,X3))
                & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                & k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X3,X2] :
              ( k7_relat_1(X1,k2_xboole_0(X2,X3)) != k7_relat_1(sK0,k2_xboole_0(X2,X3))
              & k7_relat_1(X1,X3) = k7_relat_1(sK0,X3)
              & k7_relat_1(X1,X2) = k7_relat_1(sK0,X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,
    ( ? [X1] :
        ( ? [X3,X2] :
            ( k7_relat_1(X1,k2_xboole_0(X2,X3)) != k7_relat_1(sK0,k2_xboole_0(X2,X3))
            & k7_relat_1(X1,X3) = k7_relat_1(sK0,X3)
            & k7_relat_1(X1,X2) = k7_relat_1(sK0,X2) )
        & v1_relat_1(X1) )
   => ( ? [X3,X2] :
          ( k7_relat_1(sK0,k2_xboole_0(X2,X3)) != k7_relat_1(sK1,k2_xboole_0(X2,X3))
          & k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3)
          & k7_relat_1(sK0,X2) = k7_relat_1(sK1,X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,
    ( ? [X3,X2] :
        ( k7_relat_1(sK0,k2_xboole_0(X2,X3)) != k7_relat_1(sK1,k2_xboole_0(X2,X3))
        & k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3)
        & k7_relat_1(sK0,X2) = k7_relat_1(sK1,X2) )
   => ( k7_relat_1(sK0,k2_xboole_0(sK2,sK3)) != k7_relat_1(sK1,k2_xboole_0(sK2,sK3))
      & k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3)
      & k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( k7_relat_1(X0,k2_xboole_0(X2,X3)) != k7_relat_1(X1,k2_xboole_0(X2,X3))
              & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
              & k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( k7_relat_1(X0,k2_xboole_0(X2,X3)) != k7_relat_1(X1,k2_xboole_0(X2,X3))
              & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
              & k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2,X3] :
                ( ( k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                  & k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
               => k7_relat_1(X0,k2_xboole_0(X2,X3)) = k7_relat_1(X1,k2_xboole_0(X2,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2,X3] :
              ( ( k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                & k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
             => k7_relat_1(X0,k2_xboole_0(X2,X3)) = k7_relat_1(X1,k2_xboole_0(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_relat_1)).

fof(f36,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f12,f33])).

fof(f12,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f31,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f13,f28])).

fof(f13,plain,(
    k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f26,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f14,f23])).

fof(f14,plain,(
    k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f21,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f15,f18])).

fof(f15,plain,(
    k7_relat_1(sK0,k2_xboole_0(sK2,sK3)) != k7_relat_1(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f10])).

%------------------------------------------------------------------------------
