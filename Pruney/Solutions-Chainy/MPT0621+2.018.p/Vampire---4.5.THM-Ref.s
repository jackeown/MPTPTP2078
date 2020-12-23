%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 124 expanded)
%              Number of leaves         :   16 (  45 expanded)
%              Depth                    :   17
%              Number of atoms          :  257 ( 519 expanded)
%              Number of equality atoms :  107 ( 211 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f154,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f53,f69,f81,f111,f149])).

fof(f149,plain,
    ( spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f144,f45])).

fof(f45,plain,
    ( k1_xboole_0 != sK0
    | spl4_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f144,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(condensation,[],[f118])).

fof(f118,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = sK0 )
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(superposition,[],[f68,f110])).

fof(f110,plain,
    ( ! [X5] : k1_funct_1(sK2(sK0),sK1(sK0)) = X5
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl4_6
  <=> ! [X5] : k1_funct_1(sK2(sK0),sK1(sK0)) = X5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f68,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_funct_1(sK2(X0),sK1(X0))
        | k1_xboole_0 = X0 )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl4_4
  <=> ! [X0] :
        ( k1_xboole_0 = k1_funct_1(sK2(X0),sK1(X0))
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f111,plain,
    ( spl4_6
    | spl4_2
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f102,f79,f43,f109])).

fof(f79,plain,
    ( spl4_5
  <=> ! [X1,X0] :
        ( k1_funct_1(sK3(X0,X1),sK1(X0)) = X1
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f102,plain,
    ( ! [X5] : k1_funct_1(sK2(sK0),sK1(sK0)) = X5
    | spl4_2
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f98,f45])).

fof(f98,plain,
    ( ! [X5] :
        ( k1_funct_1(sK2(sK0),sK1(sK0)) = X5
        | k1_xboole_0 = sK0 )
    | ~ spl4_5 ),
    inference(superposition,[],[f80,f94])).

fof(f94,plain,(
    ! [X0] : sK2(sK0) = sK3(sK0,X0) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK2(X0) = sK3(sK0,X1) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X1
      | sK0 != X0
      | sK2(X0) = sK3(X1,X2) ) ),
    inference(superposition,[],[f76,f30])).

fof(f30,plain,(
    ! [X0] : k1_relat_1(sK2(X0)) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK2(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK2(X0)) = X0
      & v1_funct_1(sK2(X0))
      & v1_relat_1(sK2(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK2(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK2(X0)) = X0
        & v1_funct_1(sK2(X0))
        & v1_relat_1(sK2(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( sK0 != k1_relat_1(sK2(X0))
      | sK0 != X1
      | sK2(X0) = sK3(X1,X2) ) ),
    inference(subsumption_resolution,[],[f74,f28])).

fof(f28,plain,(
    ! [X0] : v1_relat_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( sK0 != k1_relat_1(sK2(X0))
      | sK0 != X1
      | ~ v1_relat_1(sK2(X0))
      | sK2(X0) = sK3(X1,X2) ) ),
    inference(resolution,[],[f61,f29])).

fof(f29,plain,(
    ! [X0] : v1_funct_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f61,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_funct_1(X2)
      | k1_relat_1(X2) != sK0
      | sK0 != X3
      | ~ v1_relat_1(X2)
      | sK3(X3,X4) = X2 ) ),
    inference(forward_demodulation,[],[f60,f35])).

fof(f35,plain,(
    ! [X0,X1] : k1_relat_1(sK3(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK3(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK3(X0,X1)) = X0
      & v1_funct_1(sK3(X0,X1))
      & v1_relat_1(sK3(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK3(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK3(X0,X1)) = X0
        & v1_funct_1(sK3(X0,X1))
        & v1_relat_1(sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f60,plain,(
    ! [X4,X2,X3] :
      ( k1_relat_1(X2) != sK0
      | sK0 != k1_relat_1(sK3(X3,X4))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | sK3(X3,X4) = X2 ) ),
    inference(subsumption_resolution,[],[f57,f33])).

fof(f33,plain,(
    ! [X0,X1] : v1_relat_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,(
    ! [X4,X2,X3] :
      ( k1_relat_1(X2) != sK0
      | sK0 != k1_relat_1(sK3(X3,X4))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | sK3(X3,X4) = X2
      | ~ v1_relat_1(sK3(X3,X4)) ) ),
    inference(resolution,[],[f23,f34])).

fof(f34,plain,(
    ! [X0,X1] : v1_funct_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f23,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X1)
      | k1_relat_1(X2) != sK0
      | k1_relat_1(X1) != sK0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | X1 = X2
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k1_xboole_0 != sK0
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK0
            | k1_relat_1(X1) != sK0
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k1_relat_1(X2) != X0
                | k1_relat_1(X1) != X0
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
   => ( k1_xboole_0 != sK0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK0
              | k1_relat_1(X1) != sK0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k1_relat_1(X2) = X0
                    & k1_relat_1(X1) = X0 )
                 => X1 = X2 ) ) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( k1_relat_1(X2) = X0
                  & k1_relat_1(X1) = X0 )
               => X1 = X2 ) ) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).

fof(f80,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK3(X0,X1),sK1(X0)) = X1
        | k1_xboole_0 = X0 )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f81,plain,
    ( spl4_5
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f64,f51,f79])).

fof(f51,plain,
    ( spl4_3
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK3(X0,X1),sK1(X0)) = X1
        | k1_xboole_0 = X0 )
    | ~ spl4_3 ),
    inference(resolution,[],[f54,f52])).

fof(f52,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | k1_funct_1(sK3(X0,X1),sK1(X0)) = X1 ) ),
    inference(resolution,[],[f36,f27])).

fof(f27,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | k1_funct_1(sK3(X0,X1),X3) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,
    ( spl4_4
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f62,f51,f67])).

fof(f62,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_funct_1(sK2(X0),sK1(X0))
        | k1_xboole_0 = X0 )
    | ~ spl4_3 ),
    inference(resolution,[],[f49,f52])).

fof(f49,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | k1_xboole_0 = k1_funct_1(sK2(X0),sK1(X0)) ) ),
    inference(resolution,[],[f31,f27])).

fof(f31,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | k1_xboole_0 = k1_funct_1(sK2(X0),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,
    ( spl4_3
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f48,f38,f51])).

fof(f38,plain,
    ( spl4_1
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f48,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl4_1 ),
    inference(resolution,[],[f32,f40])).

fof(f40,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f46,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f24,f43])).

fof(f24,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).

fof(f41,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f25,f38])).

fof(f25,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:32:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (21712)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.45  % (21712)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f154,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f41,f46,f53,f69,f81,f111,f149])).
% 0.21/0.45  fof(f149,plain,(
% 0.21/0.45    spl4_2 | ~spl4_4 | ~spl4_6),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f148])).
% 0.21/0.45  fof(f148,plain,(
% 0.21/0.45    $false | (spl4_2 | ~spl4_4 | ~spl4_6)),
% 0.21/0.45    inference(subsumption_resolution,[],[f144,f45])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    k1_xboole_0 != sK0 | spl4_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f43])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    spl4_2 <=> k1_xboole_0 = sK0),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.45  fof(f144,plain,(
% 0.21/0.45    k1_xboole_0 = sK0 | (~spl4_4 | ~spl4_6)),
% 0.21/0.45    inference(condensation,[],[f118])).
% 0.21/0.45  fof(f118,plain,(
% 0.21/0.45    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = sK0) ) | (~spl4_4 | ~spl4_6)),
% 0.21/0.45    inference(superposition,[],[f68,f110])).
% 0.21/0.45  fof(f110,plain,(
% 0.21/0.45    ( ! [X5] : (k1_funct_1(sK2(sK0),sK1(sK0)) = X5) ) | ~spl4_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f109])).
% 0.21/0.45  fof(f109,plain,(
% 0.21/0.45    spl4_6 <=> ! [X5] : k1_funct_1(sK2(sK0),sK1(sK0)) = X5),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.45  fof(f68,plain,(
% 0.21/0.45    ( ! [X0] : (k1_xboole_0 = k1_funct_1(sK2(X0),sK1(X0)) | k1_xboole_0 = X0) ) | ~spl4_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f67])).
% 0.21/0.45  fof(f67,plain,(
% 0.21/0.45    spl4_4 <=> ! [X0] : (k1_xboole_0 = k1_funct_1(sK2(X0),sK1(X0)) | k1_xboole_0 = X0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.45  fof(f111,plain,(
% 0.21/0.45    spl4_6 | spl4_2 | ~spl4_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f102,f79,f43,f109])).
% 0.21/0.45  fof(f79,plain,(
% 0.21/0.45    spl4_5 <=> ! [X1,X0] : (k1_funct_1(sK3(X0,X1),sK1(X0)) = X1 | k1_xboole_0 = X0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.45  fof(f102,plain,(
% 0.21/0.45    ( ! [X5] : (k1_funct_1(sK2(sK0),sK1(sK0)) = X5) ) | (spl4_2 | ~spl4_5)),
% 0.21/0.45    inference(subsumption_resolution,[],[f98,f45])).
% 0.21/0.45  fof(f98,plain,(
% 0.21/0.45    ( ! [X5] : (k1_funct_1(sK2(sK0),sK1(sK0)) = X5 | k1_xboole_0 = sK0) ) | ~spl4_5),
% 0.21/0.45    inference(superposition,[],[f80,f94])).
% 0.21/0.45  fof(f94,plain,(
% 0.21/0.45    ( ! [X0] : (sK2(sK0) = sK3(sK0,X0)) )),
% 0.21/0.45    inference(equality_resolution,[],[f92])).
% 0.21/0.45  fof(f92,plain,(
% 0.21/0.45    ( ! [X0,X1] : (sK0 != X0 | sK2(X0) = sK3(sK0,X1)) )),
% 0.21/0.45    inference(equality_resolution,[],[f91])).
% 0.21/0.45  fof(f91,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (sK0 != X1 | sK0 != X0 | sK2(X0) = sK3(X1,X2)) )),
% 0.21/0.45    inference(superposition,[],[f76,f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ( ! [X0] : (k1_relat_1(sK2(X0)) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK2(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK2(X0)) = X0 & v1_funct_1(sK2(X0)) & v1_relat_1(sK2(X0)))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK2(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK2(X0)) = X0 & v1_funct_1(sK2(X0)) & v1_relat_1(sK2(X0))))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 0.21/0.45  fof(f76,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (sK0 != k1_relat_1(sK2(X0)) | sK0 != X1 | sK2(X0) = sK3(X1,X2)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f74,f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ( ! [X0] : (v1_relat_1(sK2(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f74,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (sK0 != k1_relat_1(sK2(X0)) | sK0 != X1 | ~v1_relat_1(sK2(X0)) | sK2(X0) = sK3(X1,X2)) )),
% 0.21/0.45    inference(resolution,[],[f61,f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ( ! [X0] : (v1_funct_1(sK2(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    ( ! [X4,X2,X3] : (~v1_funct_1(X2) | k1_relat_1(X2) != sK0 | sK0 != X3 | ~v1_relat_1(X2) | sK3(X3,X4) = X2) )),
% 0.21/0.45    inference(forward_demodulation,[],[f60,f35])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_relat_1(sK3(X0,X1)) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ! [X0,X1] : (! [X3] : (k1_funct_1(sK3(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK3(X0,X1)) = X0 & v1_funct_1(sK3(X0,X1)) & v1_relat_1(sK3(X0,X1)))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK3(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK3(X0,X1)) = X0 & v1_funct_1(sK3(X0,X1)) & v1_relat_1(sK3(X0,X1))))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.45    inference(ennf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 0.21/0.45  fof(f60,plain,(
% 0.21/0.45    ( ! [X4,X2,X3] : (k1_relat_1(X2) != sK0 | sK0 != k1_relat_1(sK3(X3,X4)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | sK3(X3,X4) = X2) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f57,f33])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v1_relat_1(sK3(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f22])).
% 0.21/0.45  fof(f57,plain,(
% 0.21/0.45    ( ! [X4,X2,X3] : (k1_relat_1(X2) != sK0 | sK0 != k1_relat_1(sK3(X3,X4)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | sK3(X3,X4) = X2 | ~v1_relat_1(sK3(X3,X4))) )),
% 0.21/0.45    inference(resolution,[],[f23,f34])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v1_funct_1(sK3(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f22])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ( ! [X2,X1] : (~v1_funct_1(X1) | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | X1 = X2 | ~v1_relat_1(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.45    inference(flattening,[],[f8])).
% 0.21/0.45  fof(f8,plain,(
% 0.21/0.45    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,negated_conjecture,(
% 0.21/0.45    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.21/0.45    inference(negated_conjecture,[],[f6])).
% 0.21/0.45  fof(f6,conjecture,(
% 0.21/0.45    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_funct_1(sK3(X0,X1),sK1(X0)) = X1 | k1_xboole_0 = X0) ) | ~spl4_5),
% 0.21/0.45    inference(avatar_component_clause,[],[f79])).
% 0.21/0.45  fof(f81,plain,(
% 0.21/0.45    spl4_5 | ~spl4_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f64,f51,f79])).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    spl4_3 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_funct_1(sK3(X0,X1),sK1(X0)) = X1 | k1_xboole_0 = X0) ) | ~spl4_3),
% 0.21/0.45    inference(resolution,[],[f54,f52])).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl4_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f51])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v1_xboole_0(X0) | k1_funct_1(sK3(X0,X1),sK1(X0)) = X1) )),
% 0.21/0.45    inference(resolution,[],[f36,f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.45    inference(rectify,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.45    inference(nnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | k1_funct_1(sK3(X0,X1),X3) = X1) )),
% 0.21/0.45    inference(cnf_transformation,[],[f22])).
% 0.21/0.45  fof(f69,plain,(
% 0.21/0.45    spl4_4 | ~spl4_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f62,f51,f67])).
% 0.21/0.45  fof(f62,plain,(
% 0.21/0.45    ( ! [X0] : (k1_xboole_0 = k1_funct_1(sK2(X0),sK1(X0)) | k1_xboole_0 = X0) ) | ~spl4_3),
% 0.21/0.45    inference(resolution,[],[f49,f52])).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    ( ! [X0] : (v1_xboole_0(X0) | k1_xboole_0 = k1_funct_1(sK2(X0),sK1(X0))) )),
% 0.21/0.45    inference(resolution,[],[f31,f27])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ( ! [X2,X0] : (~r2_hidden(X2,X0) | k1_xboole_0 = k1_funct_1(sK2(X0),X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    spl4_3 | ~spl4_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f48,f38,f51])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    spl4_1 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) ) | ~spl4_1),
% 0.21/0.45    inference(resolution,[],[f32,f40])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    v1_xboole_0(k1_xboole_0) | ~spl4_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f38])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    ~spl4_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f24,f43])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    k1_xboole_0 != sK0),
% 0.21/0.45    inference(cnf_transformation,[],[f14])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    spl4_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f25,f38])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    v1_xboole_0(k1_xboole_0)),
% 0.21/0.45    inference(cnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    v1_xboole_0(k1_xboole_0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (21712)------------------------------
% 0.21/0.45  % (21712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (21712)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (21712)Memory used [KB]: 6140
% 0.21/0.45  % (21712)Time elapsed: 0.059 s
% 0.21/0.45  % (21712)------------------------------
% 0.21/0.45  % (21712)------------------------------
% 0.21/0.45  % (21701)Success in time 0.096 s
%------------------------------------------------------------------------------
