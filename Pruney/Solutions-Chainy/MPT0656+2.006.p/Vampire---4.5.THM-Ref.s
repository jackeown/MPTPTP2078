%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 232 expanded)
%              Number of leaves         :   31 ( 103 expanded)
%              Depth                    :   13
%              Number of atoms          :  472 (1068 expanded)
%              Number of equality atoms :  134 ( 352 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f499,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f77,f81,f85,f89,f93,f97,f101,f112,f120,f128,f159,f185,f336,f412,f433,f486])).

fof(f486,plain,
    ( ~ spl3_7
    | ~ spl3_8
    | ~ spl3_2
    | ~ spl3_33
    | spl3_42 ),
    inference(avatar_split_clause,[],[f485,f429,f334,f75,f99,f95])).

fof(f95,plain,
    ( spl3_7
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f99,plain,
    ( spl3_8
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f75,plain,
    ( spl3_2
  <=> k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f334,plain,
    ( spl3_33
  <=> ! [X0] :
        ( r1_tarski(k2_relat_1(X0),k2_relat_1(sK0))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f429,plain,
    ( spl3_42
  <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f485,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ spl3_2
    | ~ spl3_33
    | spl3_42 ),
    inference(trivial_inequality_removal,[],[f484])).

fof(f484,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ spl3_2
    | ~ spl3_33
    | spl3_42 ),
    inference(forward_demodulation,[],[f483,f103])).

fof(f103,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(global_subsumption,[],[f47,f50,f69])).

fof(f69,plain,(
    ! [X0] :
      ( k1_relat_1(k6_relat_1(X0)) = X0
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | k6_relat_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
            & r2_hidden(sK2(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(f50,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f47,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f483,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k6_relat_1(k1_relat_1(sK0)))
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ spl3_2
    | ~ spl3_33
    | spl3_42 ),
    inference(forward_demodulation,[],[f480,f76])).

fof(f76,plain,
    ( k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f480,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl3_33
    | spl3_42 ),
    inference(resolution,[],[f335,f430])).

fof(f430,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | spl3_42 ),
    inference(avatar_component_clause,[],[f429])).

fof(f335,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(X0),k2_relat_1(sK0))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,sK1)) )
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f334])).

fof(f433,plain,
    ( ~ spl3_6
    | spl3_10
    | ~ spl3_42
    | ~ spl3_3
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f432,f410,f79,f429,f118,f91])).

fof(f91,plain,
    ( spl3_6
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f118,plain,
    ( spl3_10
  <=> sK1 = k4_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f79,plain,
    ( spl3_3
  <=> k2_relat_1(sK0) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f410,plain,
    ( spl3_39
  <=> k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f432,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | sK1 = k4_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl3_3
    | ~ spl3_39 ),
    inference(forward_demodulation,[],[f423,f80])).

fof(f80,plain,
    ( k2_relat_1(sK0) = k1_relat_1(sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f423,plain,
    ( sK1 = k4_relat_1(sK0)
    | ~ r1_tarski(k1_relat_1(sK1),k2_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl3_39 ),
    inference(superposition,[],[f61,f411])).

fof(f411,plain,
    ( k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1)
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f410])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f412,plain,
    ( spl3_39
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f408,f183,f157,f126,f99,f91,f75,f410])).

fof(f126,plain,
    ( spl3_12
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f157,plain,
    ( spl3_14
  <=> k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f183,plain,
    ( spl3_18
  <=> k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k1_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f408,plain,
    ( k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1)
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f407,f184])).

fof(f184,plain,
    ( k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k1_relat_1(sK0)))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f183])).

fof(f407,plain,
    ( k5_relat_1(k4_relat_1(sK0),k6_relat_1(k1_relat_1(sK0))) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1)
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f400,f158])).

fof(f158,plain,
    ( k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),sK0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f157])).

fof(f400,plain,
    ( k5_relat_1(k4_relat_1(sK0),k6_relat_1(k1_relat_1(sK0))) = k5_relat_1(k5_relat_1(k4_relat_1(sK0),sK0),sK1)
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(resolution,[],[f291,f127])).

fof(f127,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f126])).

fof(f291,plain,
    ( ! [X9] :
        ( ~ v1_relat_1(X9)
        | k5_relat_1(k5_relat_1(X9,sK0),sK1) = k5_relat_1(X9,k6_relat_1(k1_relat_1(sK0))) )
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f289,f76])).

fof(f289,plain,
    ( ! [X9] :
        ( k5_relat_1(k5_relat_1(X9,sK0),sK1) = k5_relat_1(X9,k5_relat_1(sK0,sK1))
        | ~ v1_relat_1(X9) )
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(resolution,[],[f231,f100])).

fof(f100,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f99])).

fof(f231,plain,
    ( ! [X17,X16] :
        ( ~ v1_relat_1(X17)
        | k5_relat_1(k5_relat_1(X16,X17),sK1) = k5_relat_1(X16,k5_relat_1(X17,sK1))
        | ~ v1_relat_1(X16) )
    | ~ spl3_6 ),
    inference(resolution,[],[f54,f92])).

fof(f92,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
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
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f336,plain,
    ( ~ spl3_6
    | ~ spl3_5
    | spl3_33
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f329,f79,f334,f87,f91])).

fof(f87,plain,
    ( spl3_5
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f329,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(X0),k2_relat_1(sK0))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,sK1))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl3_3 ),
    inference(superposition,[],[f60,f80])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

fof(f185,plain,
    ( ~ spl3_8
    | spl3_18
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f180,f126,f183,f99])).

fof(f180,plain,
    ( k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k1_relat_1(sK0)))
    | ~ v1_relat_1(sK0)
    | ~ spl3_12 ),
    inference(resolution,[],[f104,f127])).

fof(f104,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k4_relat_1(X0))
      | k4_relat_1(X0) = k5_relat_1(k4_relat_1(X0),k6_relat_1(k1_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f51,f53])).

fof(f53,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f51,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f159,plain,
    ( ~ spl3_8
    | ~ spl3_7
    | spl3_14
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f155,f110,f83,f157,f95,f99])).

fof(f83,plain,
    ( spl3_4
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f110,plain,
    ( spl3_9
  <=> k2_funct_1(sK0) = k4_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f155,plain,
    ( k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f153,f111])).

fof(f111,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f110])).

fof(f153,plain,
    ( k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f59,f84])).

fof(f84,plain,
    ( v2_funct_1(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f128,plain,
    ( ~ spl3_8
    | ~ spl3_7
    | spl3_12
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f116,f110,f126,f95,f99])).

fof(f116,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl3_9 ),
    inference(superposition,[],[f55,f111])).

fof(f55,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f120,plain,
    ( ~ spl3_10
    | spl3_1
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f114,f110,f71,f118])).

fof(f71,plain,
    ( spl3_1
  <=> k2_funct_1(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f114,plain,
    ( sK1 != k4_relat_1(sK0)
    | spl3_1
    | ~ spl3_9 ),
    inference(superposition,[],[f72,f111])).

fof(f72,plain,
    ( k2_funct_1(sK0) != sK1
    | spl3_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f112,plain,
    ( ~ spl3_8
    | ~ spl3_7
    | spl3_9
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f105,f83,f110,f95,f99])).

fof(f105,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f57,f84])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f101,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f39,f99])).

fof(f39,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( k2_funct_1(sK0) != sK1
    & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1)
    & k2_relat_1(sK0) = k1_relat_1(sK1)
    & v2_funct_1(sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_funct_1(X0) != X1
            & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & k2_relat_1(X0) = k1_relat_1(X1)
            & v2_funct_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_funct_1(sK0) != X1
          & k5_relat_1(sK0,X1) = k6_relat_1(k1_relat_1(sK0))
          & k1_relat_1(X1) = k2_relat_1(sK0)
          & v2_funct_1(sK0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( k2_funct_1(sK0) != X1
        & k5_relat_1(sK0,X1) = k6_relat_1(k1_relat_1(sK0))
        & k1_relat_1(X1) = k2_relat_1(sK0)
        & v2_funct_1(sK0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_funct_1(sK0) != sK1
      & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1)
      & k2_relat_1(sK0) = k1_relat_1(sK1)
      & v2_funct_1(sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
                & k2_relat_1(X0) = k1_relat_1(X1)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

fof(f97,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f40,f95])).

fof(f40,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f93,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f41,f91])).

fof(f41,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f89,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f42,f87])).

fof(f42,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f85,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f43,f83])).

fof(f43,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f81,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f44,f79])).

fof(f44,plain,(
    k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f77,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f45,f75])).

fof(f45,plain,(
    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f46,f71])).

fof(f46,plain,(
    k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (27766)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (27774)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.51  % (27772)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (27764)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (27771)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (27773)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  % (27763)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.52  % (27762)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (27765)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.52  % (27760)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (27778)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.53  % (27776)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.54  % (27770)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.54  % (27779)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.54  % (27768)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.54  % (27779)Refutation not found, incomplete strategy% (27779)------------------------------
% 0.21/0.54  % (27779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27779)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27779)Memory used [KB]: 10618
% 0.21/0.54  % (27779)Time elapsed: 0.138 s
% 0.21/0.54  % (27779)------------------------------
% 0.21/0.54  % (27779)------------------------------
% 0.21/0.54  % (27761)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.55  % (27765)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f499,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f73,f77,f81,f85,f89,f93,f97,f101,f112,f120,f128,f159,f185,f336,f412,f433,f486])).
% 0.21/0.55  fof(f486,plain,(
% 0.21/0.55    ~spl3_7 | ~spl3_8 | ~spl3_2 | ~spl3_33 | spl3_42),
% 0.21/0.55    inference(avatar_split_clause,[],[f485,f429,f334,f75,f99,f95])).
% 0.21/0.55  fof(f95,plain,(
% 0.21/0.55    spl3_7 <=> v1_funct_1(sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.55  fof(f99,plain,(
% 0.21/0.55    spl3_8 <=> v1_relat_1(sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    spl3_2 <=> k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.55  fof(f334,plain,(
% 0.21/0.55    spl3_33 <=> ! [X0] : (r1_tarski(k2_relat_1(X0),k2_relat_1(sK0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,sK1)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.21/0.55  fof(f429,plain,(
% 0.21/0.55    spl3_42 <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.21/0.55  fof(f485,plain,(
% 0.21/0.55    ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | (~spl3_2 | ~spl3_33 | spl3_42)),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f484])).
% 0.21/0.55  fof(f484,plain,(
% 0.21/0.55    k1_relat_1(sK0) != k1_relat_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | (~spl3_2 | ~spl3_33 | spl3_42)),
% 0.21/0.55    inference(forward_demodulation,[],[f483,f103])).
% 0.21/0.55  fof(f103,plain,(
% 0.21/0.55    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.55    inference(global_subsumption,[],[f47,f50,f69])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0 | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.55    inference(equality_resolution,[],[f62])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | k6_relat_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(rectify,[],[f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(flattening,[],[f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(nnf_transformation,[],[f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(flattening,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.21/0.55  fof(f483,plain,(
% 0.21/0.55    k1_relat_1(sK0) != k1_relat_1(k6_relat_1(k1_relat_1(sK0))) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | (~spl3_2 | ~spl3_33 | spl3_42)),
% 0.21/0.55    inference(forward_demodulation,[],[f480,f76])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) | ~spl3_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f75])).
% 0.21/0.55  fof(f480,plain,(
% 0.21/0.55    ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,sK1)) | (~spl3_33 | spl3_42)),
% 0.21/0.55    inference(resolution,[],[f335,f430])).
% 0.21/0.55  fof(f430,plain,(
% 0.21/0.55    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | spl3_42),
% 0.21/0.55    inference(avatar_component_clause,[],[f429])).
% 0.21/0.55  fof(f335,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(k2_relat_1(X0),k2_relat_1(sK0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,sK1))) ) | ~spl3_33),
% 0.21/0.55    inference(avatar_component_clause,[],[f334])).
% 0.21/0.55  fof(f433,plain,(
% 0.21/0.55    ~spl3_6 | spl3_10 | ~spl3_42 | ~spl3_3 | ~spl3_39),
% 0.21/0.55    inference(avatar_split_clause,[],[f432,f410,f79,f429,f118,f91])).
% 0.21/0.55  fof(f91,plain,(
% 0.21/0.55    spl3_6 <=> v1_relat_1(sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.55  fof(f118,plain,(
% 0.21/0.55    spl3_10 <=> sK1 = k4_relat_1(sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    spl3_3 <=> k2_relat_1(sK0) = k1_relat_1(sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.55  fof(f410,plain,(
% 0.21/0.55    spl3_39 <=> k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.21/0.55  fof(f432,plain,(
% 0.21/0.55    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | sK1 = k4_relat_1(sK0) | ~v1_relat_1(sK1) | (~spl3_3 | ~spl3_39)),
% 0.21/0.55    inference(forward_demodulation,[],[f423,f80])).
% 0.21/0.55  fof(f80,plain,(
% 0.21/0.55    k2_relat_1(sK0) = k1_relat_1(sK1) | ~spl3_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f79])).
% 0.21/0.55  fof(f423,plain,(
% 0.21/0.55    sK1 = k4_relat_1(sK0) | ~r1_tarski(k1_relat_1(sK1),k2_relat_1(sK0)) | ~v1_relat_1(sK1) | ~spl3_39),
% 0.21/0.55    inference(superposition,[],[f61,f411])).
% 0.21/0.55  fof(f411,plain,(
% 0.21/0.55    k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) | ~spl3_39),
% 0.21/0.55    inference(avatar_component_clause,[],[f410])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(flattening,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 0.21/0.55  fof(f412,plain,(
% 0.21/0.55    spl3_39 | ~spl3_2 | ~spl3_6 | ~spl3_8 | ~spl3_12 | ~spl3_14 | ~spl3_18),
% 0.21/0.55    inference(avatar_split_clause,[],[f408,f183,f157,f126,f99,f91,f75,f410])).
% 0.21/0.55  fof(f126,plain,(
% 0.21/0.55    spl3_12 <=> v1_relat_1(k4_relat_1(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.55  fof(f157,plain,(
% 0.21/0.55    spl3_14 <=> k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.55  fof(f183,plain,(
% 0.21/0.55    spl3_18 <=> k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k1_relat_1(sK0)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.55  fof(f408,plain,(
% 0.21/0.55    k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) | (~spl3_2 | ~spl3_6 | ~spl3_8 | ~spl3_12 | ~spl3_14 | ~spl3_18)),
% 0.21/0.55    inference(forward_demodulation,[],[f407,f184])).
% 0.21/0.55  fof(f184,plain,(
% 0.21/0.55    k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k1_relat_1(sK0))) | ~spl3_18),
% 0.21/0.55    inference(avatar_component_clause,[],[f183])).
% 0.21/0.55  fof(f407,plain,(
% 0.21/0.55    k5_relat_1(k4_relat_1(sK0),k6_relat_1(k1_relat_1(sK0))) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) | (~spl3_2 | ~spl3_6 | ~spl3_8 | ~spl3_12 | ~spl3_14)),
% 0.21/0.55    inference(forward_demodulation,[],[f400,f158])).
% 0.21/0.55  fof(f158,plain,(
% 0.21/0.55    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),sK0) | ~spl3_14),
% 0.21/0.55    inference(avatar_component_clause,[],[f157])).
% 0.21/0.55  fof(f400,plain,(
% 0.21/0.55    k5_relat_1(k4_relat_1(sK0),k6_relat_1(k1_relat_1(sK0))) = k5_relat_1(k5_relat_1(k4_relat_1(sK0),sK0),sK1) | (~spl3_2 | ~spl3_6 | ~spl3_8 | ~spl3_12)),
% 0.21/0.55    inference(resolution,[],[f291,f127])).
% 0.21/0.55  fof(f127,plain,(
% 0.21/0.55    v1_relat_1(k4_relat_1(sK0)) | ~spl3_12),
% 0.21/0.55    inference(avatar_component_clause,[],[f126])).
% 0.21/0.55  fof(f291,plain,(
% 0.21/0.55    ( ! [X9] : (~v1_relat_1(X9) | k5_relat_1(k5_relat_1(X9,sK0),sK1) = k5_relat_1(X9,k6_relat_1(k1_relat_1(sK0)))) ) | (~spl3_2 | ~spl3_6 | ~spl3_8)),
% 0.21/0.55    inference(forward_demodulation,[],[f289,f76])).
% 0.21/0.55  fof(f289,plain,(
% 0.21/0.55    ( ! [X9] : (k5_relat_1(k5_relat_1(X9,sK0),sK1) = k5_relat_1(X9,k5_relat_1(sK0,sK1)) | ~v1_relat_1(X9)) ) | (~spl3_6 | ~spl3_8)),
% 0.21/0.55    inference(resolution,[],[f231,f100])).
% 0.21/0.55  fof(f100,plain,(
% 0.21/0.55    v1_relat_1(sK0) | ~spl3_8),
% 0.21/0.55    inference(avatar_component_clause,[],[f99])).
% 0.21/0.55  fof(f231,plain,(
% 0.21/0.55    ( ! [X17,X16] : (~v1_relat_1(X17) | k5_relat_1(k5_relat_1(X16,X17),sK1) = k5_relat_1(X16,k5_relat_1(X17,sK1)) | ~v1_relat_1(X16)) ) | ~spl3_6),
% 0.21/0.55    inference(resolution,[],[f54,f92])).
% 0.21/0.55  fof(f92,plain,(
% 0.21/0.55    v1_relat_1(sK1) | ~spl3_6),
% 0.21/0.55    inference(avatar_component_clause,[],[f91])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 0.21/0.55  fof(f336,plain,(
% 0.21/0.55    ~spl3_6 | ~spl3_5 | spl3_33 | ~spl3_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f329,f79,f334,f87,f91])).
% 0.21/0.55  fof(f87,plain,(
% 0.21/0.55    spl3_5 <=> v1_funct_1(sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.56  fof(f329,plain,(
% 0.21/0.56    ( ! [X0] : (r1_tarski(k2_relat_1(X0),k2_relat_1(sK0)) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,sK1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | ~spl3_3),
% 0.21/0.56    inference(superposition,[],[f60,f80])).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(flattening,[],[f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).
% 0.21/0.56  fof(f185,plain,(
% 0.21/0.56    ~spl3_8 | spl3_18 | ~spl3_12),
% 0.21/0.56    inference(avatar_split_clause,[],[f180,f126,f183,f99])).
% 0.21/0.56  fof(f180,plain,(
% 0.21/0.56    k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(k1_relat_1(sK0))) | ~v1_relat_1(sK0) | ~spl3_12),
% 0.21/0.56    inference(resolution,[],[f104,f127])).
% 0.21/0.56  fof(f104,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_relat_1(k4_relat_1(X0)) | k4_relat_1(X0) = k5_relat_1(k4_relat_1(X0),k6_relat_1(k1_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(superposition,[],[f51,f53])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.21/0.56  fof(f51,plain,(
% 0.21/0.56    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 0.21/0.56  fof(f159,plain,(
% 0.21/0.56    ~spl3_8 | ~spl3_7 | spl3_14 | ~spl3_4 | ~spl3_9),
% 0.21/0.56    inference(avatar_split_clause,[],[f155,f110,f83,f157,f95,f99])).
% 0.21/0.56  fof(f83,plain,(
% 0.21/0.56    spl3_4 <=> v2_funct_1(sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.56  fof(f110,plain,(
% 0.21/0.56    spl3_9 <=> k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.56  fof(f155,plain,(
% 0.21/0.56    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (~spl3_4 | ~spl3_9)),
% 0.21/0.56    inference(forward_demodulation,[],[f153,f111])).
% 0.21/0.56  fof(f111,plain,(
% 0.21/0.56    k2_funct_1(sK0) = k4_relat_1(sK0) | ~spl3_9),
% 0.21/0.56    inference(avatar_component_clause,[],[f110])).
% 0.21/0.56  fof(f153,plain,(
% 0.21/0.56    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl3_4),
% 0.21/0.56    inference(resolution,[],[f59,f84])).
% 0.21/0.56  fof(f84,plain,(
% 0.21/0.56    v2_funct_1(sK0) | ~spl3_4),
% 0.21/0.56    inference(avatar_component_clause,[],[f83])).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    ( ! [X0] : (~v2_funct_1(X0) | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(flattening,[],[f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,axiom,(
% 0.21/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.21/0.56  fof(f128,plain,(
% 0.21/0.56    ~spl3_8 | ~spl3_7 | spl3_12 | ~spl3_9),
% 0.21/0.56    inference(avatar_split_clause,[],[f116,f110,f126,f95,f99])).
% 0.21/0.56  fof(f116,plain,(
% 0.21/0.56    v1_relat_1(k4_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl3_9),
% 0.21/0.56    inference(superposition,[],[f55,f111])).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f20])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(flattening,[],[f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.56  fof(f120,plain,(
% 0.21/0.56    ~spl3_10 | spl3_1 | ~spl3_9),
% 0.21/0.56    inference(avatar_split_clause,[],[f114,f110,f71,f118])).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    spl3_1 <=> k2_funct_1(sK0) = sK1),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.56  fof(f114,plain,(
% 0.21/0.56    sK1 != k4_relat_1(sK0) | (spl3_1 | ~spl3_9)),
% 0.21/0.56    inference(superposition,[],[f72,f111])).
% 0.21/0.56  fof(f72,plain,(
% 0.21/0.56    k2_funct_1(sK0) != sK1 | spl3_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f71])).
% 0.21/0.56  fof(f112,plain,(
% 0.21/0.56    ~spl3_8 | ~spl3_7 | spl3_9 | ~spl3_4),
% 0.21/0.56    inference(avatar_split_clause,[],[f105,f83,f110,f95,f99])).
% 0.21/0.56  fof(f105,plain,(
% 0.21/0.56    k2_funct_1(sK0) = k4_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl3_4),
% 0.21/0.56    inference(resolution,[],[f57,f84])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(flattening,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.21/0.56  fof(f101,plain,(
% 0.21/0.56    spl3_8),
% 0.21/0.56    inference(avatar_split_clause,[],[f39,f99])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    v1_relat_1(sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    (k2_funct_1(sK0) != sK1 & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) & k2_relat_1(sK0) = k1_relat_1(sK1) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f32,f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k2_funct_1(sK0) != X1 & k5_relat_1(sK0,X1) = k6_relat_1(k1_relat_1(sK0)) & k1_relat_1(X1) = k2_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ? [X1] : (k2_funct_1(sK0) != X1 & k5_relat_1(sK0,X1) = k6_relat_1(k1_relat_1(sK0)) & k1_relat_1(X1) = k2_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(sK0) != sK1 & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) & k2_relat_1(sK0) = k1_relat_1(sK1) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f15,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.56    inference(flattening,[],[f14])).
% 0.21/0.56  fof(f14,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,negated_conjecture,(
% 0.21/0.56    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.21/0.56    inference(negated_conjecture,[],[f12])).
% 0.21/0.56  fof(f12,conjecture,(
% 0.21/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).
% 0.21/0.56  fof(f97,plain,(
% 0.21/0.56    spl3_7),
% 0.21/0.56    inference(avatar_split_clause,[],[f40,f95])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    v1_funct_1(sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  fof(f93,plain,(
% 0.21/0.56    spl3_6),
% 0.21/0.56    inference(avatar_split_clause,[],[f41,f91])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    v1_relat_1(sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  fof(f89,plain,(
% 0.21/0.56    spl3_5),
% 0.21/0.56    inference(avatar_split_clause,[],[f42,f87])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    v1_funct_1(sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  fof(f85,plain,(
% 0.21/0.56    spl3_4),
% 0.21/0.56    inference(avatar_split_clause,[],[f43,f83])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    v2_funct_1(sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  fof(f81,plain,(
% 0.21/0.56    spl3_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f44,f79])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    k2_relat_1(sK0) = k1_relat_1(sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  fof(f77,plain,(
% 0.21/0.56    spl3_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f45,f75])).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  fof(f73,plain,(
% 0.21/0.56    ~spl3_1),
% 0.21/0.56    inference(avatar_split_clause,[],[f46,f71])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    k2_funct_1(sK0) != sK1),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (27765)------------------------------
% 0.21/0.56  % (27765)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (27765)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (27765)Memory used [KB]: 11129
% 0.21/0.56  % (27765)Time elapsed: 0.039 s
% 0.21/0.56  % (27765)------------------------------
% 0.21/0.56  % (27765)------------------------------
% 0.21/0.56  % (27777)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.61/0.56  % (27758)Success in time 0.203 s
%------------------------------------------------------------------------------
