%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:53 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 370 expanded)
%              Number of leaves         :   20 ( 125 expanded)
%              Depth                    :   25
%              Number of atoms          :  466 (1872 expanded)
%              Number of equality atoms :  168 ( 755 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f987,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f74,f79,f84,f223,f229,f503,f954,f986])).

fof(f986,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_12
    | spl7_13 ),
    inference(avatar_contradiction_clause,[],[f985])).

fof(f985,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_12
    | spl7_13 ),
    inference(subsumption_resolution,[],[f978,f60])).

fof(f60,plain,
    ( k1_xboole_0 != sK0
    | spl7_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl7_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f978,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_12
    | spl7_13 ),
    inference(resolution,[],[f957,f504])).

fof(f504,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(k1_xboole_0,X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_12 ),
    inference(backward_demodulation,[],[f359,f502])).

fof(f502,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f500])).

fof(f500,plain,
    ( spl7_12
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f359,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(k1_xboole_0,X0),X0)
        | k2_relat_1(k1_xboole_0) = X0 )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f358,f83])).

fof(f83,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl7_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f358,plain,
    ( ! [X0] :
        ( k2_relat_1(k1_xboole_0) = X0
        | r2_hidden(sK3(k1_xboole_0,X0),X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f357,f78])).

fof(f78,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl7_3
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f357,plain,
    ( ! [X0] :
        ( k2_relat_1(k1_xboole_0) = X0
        | r2_hidden(sK3(k1_xboole_0,X0),X0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f355,f144])).

fof(f144,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl7_5
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f355,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(k1_xboole_0,X0),k1_xboole_0)
        | k2_relat_1(k1_xboole_0) = X0
        | r2_hidden(sK3(k1_xboole_0,X0),X0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl7_2 ),
    inference(superposition,[],[f40,f73])).

fof(f73,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl7_2
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | k2_relat_1(X0) = X1
      | r2_hidden(sK3(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK3(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK3(X0,X1),X1) )
              & ( ( sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1))
                  & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK3(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK5(X0,X5)) = X5
                    & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f23,f26,f25,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK3(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK3(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK3(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X5)) = X5
        & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f957,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | spl7_13 ),
    inference(resolution,[],[f953,f90])).

% (32680)Refutation not found, incomplete strategy% (32680)------------------------------
% (32680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (32680)Termination reason: Refutation not found, incomplete strategy

% (32680)Memory used [KB]: 6268
% (32680)Time elapsed: 0.139 s
% (32680)------------------------------
% (32680)------------------------------
fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X1,k2_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(X2,X0) ) ),
    inference(forward_demodulation,[],[f88,f47])).

% (32673)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
fof(f47,plain,(
    ! [X0,X1] : k1_relat_1(sK6(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f29])).

% (32673)Refutation not found, incomplete strategy% (32673)------------------------------
% (32673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (32673)Termination reason: Refutation not found, incomplete strategy

% (32673)Memory used [KB]: 1663
% (32673)Time elapsed: 0.139 s
% (32673)------------------------------
% (32673)------------------------------
fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK6(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK6(X0,X1)) = X0
      & v1_funct_1(sK6(X0,X1))
      & v1_relat_1(sK6(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f14,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK6(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK6(X0,X1)) = X0
        & v1_funct_1(sK6(X0,X1))
        & v1_relat_1(sK6(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(X2,k1_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(X2,X0) ) ),
    inference(subsumption_resolution,[],[f87,f45])).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(X2,k1_relat_1(sK6(X0,X1)))
      | ~ v1_relat_1(sK6(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(subsumption_resolution,[],[f86,f46])).

fof(f46,plain,(
    ! [X0,X1] : v1_funct_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(X2,k1_relat_1(sK6(X0,X1)))
      | ~ v1_funct_1(sK6(X0,X1))
      | ~ v1_relat_1(sK6(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f54,f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK6(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f953,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(sK6(sK0,sK1)))
    | spl7_13 ),
    inference(avatar_component_clause,[],[f951])).

fof(f951,plain,
    ( spl7_13
  <=> r2_hidden(sK1,k2_relat_1(sK6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f954,plain,(
    ~ spl7_13 ),
    inference(avatar_split_clause,[],[f949,f951])).

fof(f949,plain,(
    ~ r2_hidden(sK1,k2_relat_1(sK6(sK0,sK1))) ),
    inference(equality_resolution,[],[f907])).

fof(f907,plain,(
    ! [X0] :
      ( sK0 != X0
      | ~ r2_hidden(sK1,k2_relat_1(sK6(X0,sK1))) ) ),
    inference(equality_resolution,[],[f889])).

fof(f889,plain,(
    ! [X50,X51] :
      ( k1_tarski(sK1) != k1_tarski(X51)
      | sK0 != X50
      | ~ r2_hidden(X51,k2_relat_1(sK6(X50,X51))) ) ),
    inference(forward_demodulation,[],[f888,f47])).

fof(f888,plain,(
    ! [X50,X51] :
      ( k1_tarski(sK1) != k1_tarski(X51)
      | sK0 != k1_relat_1(sK6(X50,X51))
      | ~ r2_hidden(X51,k2_relat_1(sK6(X50,X51))) ) ),
    inference(subsumption_resolution,[],[f887,f45])).

fof(f887,plain,(
    ! [X50,X51] :
      ( k1_tarski(sK1) != k1_tarski(X51)
      | sK0 != k1_relat_1(sK6(X50,X51))
      | ~ v1_relat_1(sK6(X50,X51))
      | ~ r2_hidden(X51,k2_relat_1(sK6(X50,X51))) ) ),
    inference(subsumption_resolution,[],[f878,f46])).

fof(f878,plain,(
    ! [X50,X51] :
      ( k1_tarski(sK1) != k1_tarski(X51)
      | sK0 != k1_relat_1(sK6(X50,X51))
      | ~ v1_funct_1(sK6(X50,X51))
      | ~ v1_relat_1(sK6(X50,X51))
      | ~ r2_hidden(X51,k2_relat_1(sK6(X50,X51))) ) ),
    inference(superposition,[],[f31,f846])).

fof(f846,plain,(
    ! [X2,X3] :
      ( k1_tarski(X2) = k2_relat_1(sK6(X3,X2))
      | ~ r2_hidden(X2,k2_relat_1(sK6(X3,X2))) ) ),
    inference(trivial_inequality_removal,[],[f845])).

fof(f845,plain,(
    ! [X2,X3] :
      ( X2 != X2
      | k1_tarski(X2) = k2_relat_1(sK6(X3,X2))
      | ~ r2_hidden(X2,k2_relat_1(sK6(X3,X2))) ) ),
    inference(duplicate_literal_removal,[],[f843])).

fof(f843,plain,(
    ! [X2,X3] :
      ( X2 != X2
      | k1_tarski(X2) = k2_relat_1(sK6(X3,X2))
      | ~ r2_hidden(X2,k2_relat_1(sK6(X3,X2)))
      | k1_tarski(X2) = k2_relat_1(sK6(X3,X2)) ) ),
    inference(superposition,[],[f35,f841])).

fof(f841,plain,(
    ! [X0,X1] :
      ( sK2(X0,k2_relat_1(sK6(X1,X0))) = X0
      | k1_tarski(X0) = k2_relat_1(sK6(X1,X0)) ) ),
    inference(equality_resolution,[],[f715])).

fof(f715,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | sK2(X0,k2_relat_1(sK6(X1,X2))) = X2
      | k1_tarski(X0) = k2_relat_1(sK6(X1,X2)) ) ),
    inference(equality_factoring,[],[f410])).

fof(f410,plain,(
    ! [X6,X8,X7] :
      ( sK2(X7,k2_relat_1(sK6(X8,X6))) = X7
      | sK2(X7,k2_relat_1(sK6(X8,X6))) = X6
      | k1_tarski(X7) = k2_relat_1(sK6(X8,X6)) ) ),
    inference(resolution,[],[f344,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | sK2(X0,X1) = X0
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f344,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_relat_1(sK6(X0,X1)))
      | X1 = X2 ) ),
    inference(subsumption_resolution,[],[f343,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(sK6(X0,X1),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(sK6(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f92,f45])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(sK6(X0,X1),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(sK6(X0,X1)))
      | ~ v1_relat_1(sK6(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f91,f46])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(sK6(X0,X1),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(sK6(X0,X1)))
      | ~ v1_funct_1(sK6(X0,X1))
      | ~ v1_relat_1(sK6(X0,X1)) ) ),
    inference(superposition,[],[f56,f47])).

fof(f56,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f343,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(X2,k2_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(sK5(sK6(X0,X1),X2),X0) ) ),
    inference(subsumption_resolution,[],[f342,f45])).

fof(f342,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(X2,k2_relat_1(sK6(X0,X1)))
      | ~ v1_relat_1(sK6(X0,X1))
      | ~ r2_hidden(sK5(sK6(X0,X1),X2),X0) ) ),
    inference(subsumption_resolution,[],[f338,f46])).

% (32665)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
fof(f338,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(X2,k2_relat_1(sK6(X0,X1)))
      | ~ v1_funct_1(sK6(X0,X1))
      | ~ v1_relat_1(sK6(X0,X1))
      | ~ r2_hidden(sK5(sK6(X0,X1),X2),X0) ) ),
    inference(superposition,[],[f55,f48])).

fof(f55,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f35,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X0
      | k1_tarski(X0) = X1
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f31,plain,(
    ! [X2] :
      ( k2_relat_1(X2) != k1_tarski(sK1)
      | k1_relat_1(X2) != sK0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ! [X2] :
        ( k2_relat_1(X2) != k1_tarski(sK1)
        | k1_relat_1(X2) != sK0
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
          ! [X2] :
            ( k2_relat_1(X2) != k1_tarski(X1)
            | k1_relat_1(X2) != X0
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & k1_xboole_0 != X0 )
   => ( ? [X1] :
        ! [X2] :
          ( k2_relat_1(X2) != k1_tarski(X1)
          | k1_relat_1(X2) != sK0
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
      ! [X2] :
        ( k2_relat_1(X2) != k1_tarski(X1)
        | k1_relat_1(X2) != sK0
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
   => ! [X2] :
        ( k2_relat_1(X2) != k1_tarski(sK1)
        | k1_relat_1(X2) != sK0
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
        ! [X2] :
          ( k2_relat_1(X2) != k1_tarski(X1)
          | k1_relat_1(X2) != X0
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( k1_xboole_0 != X0
       => ! [X1] :
          ? [X2] :
            ( k2_relat_1(X2) = k1_tarski(X1)
            & k1_relat_1(X2) = X0
            & v1_funct_1(X2)
            & v1_relat_1(X2) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(f503,plain,
    ( spl7_12
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f495,f143,f81,f76,f71,f500])).

fof(f495,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(resolution,[],[f359,f144])).

fof(f229,plain,
    ( spl7_5
    | spl7_9 ),
    inference(avatar_split_clause,[],[f228,f170,f143])).

fof(f170,plain,
    ( spl7_9
  <=> ! [X0] :
        ( k1_relat_1(X0) != sK0
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f228,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != sK0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f227,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k1_xboole_0,X1) = X0
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f48,f65])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = sK6(k1_xboole_0,X0) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = sK6(X0,X1) ) ),
    inference(subsumption_resolution,[],[f63,f45])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = sK6(X0,X1)
      | ~ v1_relat_1(sK6(X0,X1)) ) ),
    inference(superposition,[],[f43,f47])).

fof(f43,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != k1_xboole_0
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f227,plain,(
    ! [X0,X1] :
      ( k1_tarski(sK1) != k1_funct_1(k1_xboole_0,X1)
      | k1_relat_1(X0) != sK0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f31,f66])).

fof(f223,plain,(
    ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | ~ spl7_9 ),
    inference(unit_resulting_resolution,[],[f46,f45,f47,f171])).

fof(f171,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0) )
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f170])).

fof(f84,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f69,f81])).

fof(f69,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f45,f65])).

fof(f79,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f68,f76])).

fof(f68,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f46,f65])).

fof(f74,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f67,f71])).

fof(f67,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f47,f65])).

fof(f61,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f30,f58])).

fof(f30,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:01:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (32668)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.49  % (32676)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.50  % (32659)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (32684)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (32684)Refutation not found, incomplete strategy% (32684)------------------------------
% 0.21/0.52  % (32684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (32684)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (32684)Memory used [KB]: 1663
% 0.21/0.52  % (32684)Time elapsed: 0.110 s
% 0.21/0.52  % (32684)------------------------------
% 0.21/0.52  % (32684)------------------------------
% 0.21/0.52  % (32674)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (32680)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.52  % (32657)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (32669)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (32669)Refutation not found, incomplete strategy% (32669)------------------------------
% 0.21/0.52  % (32669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (32669)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (32669)Memory used [KB]: 1663
% 0.21/0.52  % (32669)Time elapsed: 0.082 s
% 0.21/0.52  % (32669)------------------------------
% 0.21/0.52  % (32669)------------------------------
% 0.21/0.52  % (32667)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (32656)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (32667)Refutation not found, incomplete strategy% (32667)------------------------------
% 0.21/0.53  % (32667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (32656)Refutation not found, incomplete strategy% (32656)------------------------------
% 0.21/0.53  % (32656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (32656)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (32656)Memory used [KB]: 1663
% 0.21/0.53  % (32656)Time elapsed: 0.115 s
% 0.21/0.53  % (32656)------------------------------
% 0.21/0.53  % (32656)------------------------------
% 0.21/0.53  % (32661)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (32667)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (32667)Memory used [KB]: 10618
% 0.21/0.53  % (32667)Time elapsed: 0.116 s
% 0.21/0.53  % (32667)------------------------------
% 0.21/0.53  % (32667)------------------------------
% 1.36/0.53  % (32660)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.36/0.53  % (32676)Refutation found. Thanks to Tanya!
% 1.36/0.53  % SZS status Theorem for theBenchmark
% 1.36/0.53  % (32682)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.36/0.53  % (32681)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.36/0.53  % (32682)Refutation not found, incomplete strategy% (32682)------------------------------
% 1.36/0.53  % (32682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.53  % (32682)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.53  
% 1.36/0.53  % (32682)Memory used [KB]: 6140
% 1.36/0.53  % (32682)Time elapsed: 0.132 s
% 1.36/0.53  % (32682)------------------------------
% 1.36/0.53  % (32682)------------------------------
% 1.36/0.53  % (32681)Refutation not found, incomplete strategy% (32681)------------------------------
% 1.36/0.53  % (32681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.53  % (32681)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.53  
% 1.36/0.53  % (32681)Memory used [KB]: 6140
% 1.36/0.53  % (32681)Time elapsed: 0.129 s
% 1.36/0.53  % (32681)------------------------------
% 1.36/0.53  % (32681)------------------------------
% 1.36/0.53  % (32679)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.36/0.53  % (32666)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.36/0.53  % (32683)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.36/0.53  % (32658)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.36/0.53  % (32666)Refutation not found, incomplete strategy% (32666)------------------------------
% 1.36/0.53  % (32666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.53  % (32666)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.53  
% 1.36/0.53  % (32666)Memory used [KB]: 6268
% 1.36/0.53  % (32666)Time elapsed: 0.134 s
% 1.36/0.53  % (32666)------------------------------
% 1.36/0.53  % (32666)------------------------------
% 1.36/0.53  % (32679)Refutation not found, incomplete strategy% (32679)------------------------------
% 1.36/0.53  % (32679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.53  % (32679)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.53  
% 1.36/0.53  % (32679)Memory used [KB]: 10618
% 1.36/0.53  % (32679)Time elapsed: 0.128 s
% 1.36/0.53  % (32679)------------------------------
% 1.36/0.53  % (32679)------------------------------
% 1.36/0.53  % (32672)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.36/0.53  % (32678)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.36/0.53  % (32672)Refutation not found, incomplete strategy% (32672)------------------------------
% 1.36/0.53  % (32672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.53  % (32672)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.53  
% 1.36/0.53  % (32672)Memory used [KB]: 1663
% 1.36/0.53  % (32672)Time elapsed: 0.100 s
% 1.36/0.53  % (32672)------------------------------
% 1.36/0.53  % (32672)------------------------------
% 1.36/0.54  % (32664)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.36/0.54  % (32671)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.36/0.54  % (32675)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.36/0.54  % (32655)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.36/0.54  % (32677)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.36/0.54  % (32671)Refutation not found, incomplete strategy% (32671)------------------------------
% 1.36/0.54  % (32671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (32671)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (32671)Memory used [KB]: 10618
% 1.36/0.54  % (32671)Time elapsed: 0.129 s
% 1.36/0.54  % (32671)------------------------------
% 1.36/0.54  % (32671)------------------------------
% 1.36/0.54  % (32663)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.36/0.54  % SZS output start Proof for theBenchmark
% 1.36/0.54  fof(f987,plain,(
% 1.36/0.54    $false),
% 1.36/0.54    inference(avatar_sat_refutation,[],[f61,f74,f79,f84,f223,f229,f503,f954,f986])).
% 1.36/0.54  fof(f986,plain,(
% 1.36/0.54    spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_12 | spl7_13),
% 1.36/0.54    inference(avatar_contradiction_clause,[],[f985])).
% 1.36/0.54  fof(f985,plain,(
% 1.36/0.54    $false | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_12 | spl7_13)),
% 1.36/0.54    inference(subsumption_resolution,[],[f978,f60])).
% 1.36/0.54  fof(f60,plain,(
% 1.36/0.54    k1_xboole_0 != sK0 | spl7_1),
% 1.36/0.54    inference(avatar_component_clause,[],[f58])).
% 1.36/0.54  fof(f58,plain,(
% 1.36/0.54    spl7_1 <=> k1_xboole_0 = sK0),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.36/0.54  fof(f978,plain,(
% 1.36/0.54    k1_xboole_0 = sK0 | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_12 | spl7_13)),
% 1.36/0.54    inference(resolution,[],[f957,f504])).
% 1.36/0.54  fof(f504,plain,(
% 1.36/0.54    ( ! [X0] : (r2_hidden(sK3(k1_xboole_0,X0),X0) | k1_xboole_0 = X0) ) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_12)),
% 1.36/0.54    inference(backward_demodulation,[],[f359,f502])).
% 1.36/0.54  fof(f502,plain,(
% 1.36/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl7_12),
% 1.36/0.54    inference(avatar_component_clause,[],[f500])).
% 1.36/0.54  fof(f500,plain,(
% 1.36/0.54    spl7_12 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 1.36/0.54  fof(f359,plain,(
% 1.36/0.54    ( ! [X0] : (r2_hidden(sK3(k1_xboole_0,X0),X0) | k2_relat_1(k1_xboole_0) = X0) ) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 1.36/0.54    inference(subsumption_resolution,[],[f358,f83])).
% 1.36/0.54  fof(f83,plain,(
% 1.36/0.54    v1_relat_1(k1_xboole_0) | ~spl7_4),
% 1.36/0.54    inference(avatar_component_clause,[],[f81])).
% 1.36/0.54  fof(f81,plain,(
% 1.36/0.54    spl7_4 <=> v1_relat_1(k1_xboole_0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.36/0.54  fof(f358,plain,(
% 1.36/0.54    ( ! [X0] : (k2_relat_1(k1_xboole_0) = X0 | r2_hidden(sK3(k1_xboole_0,X0),X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl7_2 | ~spl7_3 | ~spl7_5)),
% 1.36/0.54    inference(subsumption_resolution,[],[f357,f78])).
% 1.36/0.54  fof(f78,plain,(
% 1.36/0.54    v1_funct_1(k1_xboole_0) | ~spl7_3),
% 1.36/0.54    inference(avatar_component_clause,[],[f76])).
% 1.36/0.54  fof(f76,plain,(
% 1.36/0.54    spl7_3 <=> v1_funct_1(k1_xboole_0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.36/0.54  fof(f357,plain,(
% 1.36/0.54    ( ! [X0] : (k2_relat_1(k1_xboole_0) = X0 | r2_hidden(sK3(k1_xboole_0,X0),X0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl7_2 | ~spl7_5)),
% 1.36/0.54    inference(subsumption_resolution,[],[f355,f144])).
% 1.36/0.54  fof(f144,plain,(
% 1.36/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl7_5),
% 1.36/0.54    inference(avatar_component_clause,[],[f143])).
% 1.36/0.54  fof(f143,plain,(
% 1.36/0.54    spl7_5 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.36/0.54  fof(f355,plain,(
% 1.36/0.54    ( ! [X0] : (r2_hidden(sK4(k1_xboole_0,X0),k1_xboole_0) | k2_relat_1(k1_xboole_0) = X0 | r2_hidden(sK3(k1_xboole_0,X0),X0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl7_2),
% 1.36/0.54    inference(superposition,[],[f40,f73])).
% 1.36/0.54  fof(f73,plain,(
% 1.36/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl7_2),
% 1.36/0.54    inference(avatar_component_clause,[],[f71])).
% 1.36/0.54  fof(f71,plain,(
% 1.36/0.54    spl7_2 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.36/0.54  fof(f40,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | k2_relat_1(X0) = X1 | r2_hidden(sK3(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f27])).
% 1.36/0.54  fof(f27,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & ((sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f23,f26,f25,f24])).
% 1.36/0.54  fof(f24,plain,(
% 1.36/0.54    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1))))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f25,plain,(
% 1.36/0.54    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f26,plain,(
% 1.36/0.54    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f23,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.54    inference(rectify,[],[f22])).
% 1.36/0.54  fof(f22,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.54    inference(nnf_transformation,[],[f11])).
% 1.36/0.54  fof(f11,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.54    inference(flattening,[],[f10])).
% 1.36/0.54  fof(f10,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.54    inference(ennf_transformation,[],[f5])).
% 1.36/0.54  fof(f5,axiom,(
% 1.36/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 1.36/0.54  fof(f957,plain,(
% 1.36/0.54    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | spl7_13),
% 1.36/0.54    inference(resolution,[],[f953,f90])).
% 1.36/0.54  % (32680)Refutation not found, incomplete strategy% (32680)------------------------------
% 1.36/0.54  % (32680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (32680)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (32680)Memory used [KB]: 6268
% 1.36/0.54  % (32680)Time elapsed: 0.139 s
% 1.36/0.54  % (32680)------------------------------
% 1.36/0.54  % (32680)------------------------------
% 1.36/0.54  fof(f90,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(sK6(X0,X1))) | ~r2_hidden(X2,X0)) )),
% 1.36/0.54    inference(duplicate_literal_removal,[],[f89])).
% 1.36/0.54  fof(f89,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X1,k2_relat_1(sK6(X0,X1))) | ~r2_hidden(X2,X0)) )),
% 1.36/0.54    inference(forward_demodulation,[],[f88,f47])).
% 1.36/0.54  % (32673)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.36/0.54  fof(f47,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k1_relat_1(sK6(X0,X1)) = X0) )),
% 1.36/0.54    inference(cnf_transformation,[],[f29])).
% 1.36/0.54  % (32673)Refutation not found, incomplete strategy% (32673)------------------------------
% 1.36/0.54  % (32673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (32673)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (32673)Memory used [KB]: 1663
% 1.36/0.54  % (32673)Time elapsed: 0.139 s
% 1.36/0.54  % (32673)------------------------------
% 1.36/0.54  % (32673)------------------------------
% 1.36/0.54  fof(f29,plain,(
% 1.36/0.54    ! [X0,X1] : (! [X3] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK6(X0,X1)) = X0 & v1_funct_1(sK6(X0,X1)) & v1_relat_1(sK6(X0,X1)))),
% 1.36/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f14,f28])).
% 1.36/0.54  fof(f28,plain,(
% 1.36/0.54    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK6(X0,X1)) = X0 & v1_funct_1(sK6(X0,X1)) & v1_relat_1(sK6(X0,X1))))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f14,plain,(
% 1.36/0.54    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.36/0.54    inference(ennf_transformation,[],[f6])).
% 1.36/0.54  fof(f6,axiom,(
% 1.36/0.54    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 1.36/0.54  fof(f88,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(sK6(X0,X1))) | ~r2_hidden(X2,k1_relat_1(sK6(X0,X1))) | ~r2_hidden(X2,X0)) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f87,f45])).
% 1.36/0.54  fof(f45,plain,(
% 1.36/0.54    ( ! [X0,X1] : (v1_relat_1(sK6(X0,X1))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f29])).
% 1.36/0.54  fof(f87,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(sK6(X0,X1))) | ~r2_hidden(X2,k1_relat_1(sK6(X0,X1))) | ~v1_relat_1(sK6(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f86,f46])).
% 1.36/0.54  fof(f46,plain,(
% 1.36/0.54    ( ! [X0,X1] : (v1_funct_1(sK6(X0,X1))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f29])).
% 1.36/0.54  fof(f86,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(sK6(X0,X1))) | ~r2_hidden(X2,k1_relat_1(sK6(X0,X1))) | ~v1_funct_1(sK6(X0,X1)) | ~v1_relat_1(sK6(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 1.36/0.54    inference(superposition,[],[f54,f48])).
% 1.36/0.54  fof(f48,plain,(
% 1.36/0.54    ( ! [X0,X3,X1] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f29])).
% 1.36/0.54  fof(f54,plain,(
% 1.36/0.54    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.54    inference(equality_resolution,[],[f53])).
% 1.36/0.54  fof(f53,plain,(
% 1.36/0.54    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.54    inference(equality_resolution,[],[f39])).
% 1.36/0.54  fof(f39,plain,(
% 1.36/0.54    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f27])).
% 1.36/0.54  fof(f953,plain,(
% 1.36/0.54    ~r2_hidden(sK1,k2_relat_1(sK6(sK0,sK1))) | spl7_13),
% 1.36/0.54    inference(avatar_component_clause,[],[f951])).
% 1.36/0.54  fof(f951,plain,(
% 1.36/0.54    spl7_13 <=> r2_hidden(sK1,k2_relat_1(sK6(sK0,sK1)))),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 1.36/0.54  fof(f954,plain,(
% 1.36/0.54    ~spl7_13),
% 1.36/0.54    inference(avatar_split_clause,[],[f949,f951])).
% 1.36/0.54  fof(f949,plain,(
% 1.36/0.54    ~r2_hidden(sK1,k2_relat_1(sK6(sK0,sK1)))),
% 1.36/0.54    inference(equality_resolution,[],[f907])).
% 1.36/0.54  fof(f907,plain,(
% 1.36/0.54    ( ! [X0] : (sK0 != X0 | ~r2_hidden(sK1,k2_relat_1(sK6(X0,sK1)))) )),
% 1.36/0.54    inference(equality_resolution,[],[f889])).
% 1.36/0.54  fof(f889,plain,(
% 1.36/0.54    ( ! [X50,X51] : (k1_tarski(sK1) != k1_tarski(X51) | sK0 != X50 | ~r2_hidden(X51,k2_relat_1(sK6(X50,X51)))) )),
% 1.36/0.54    inference(forward_demodulation,[],[f888,f47])).
% 1.36/0.54  fof(f888,plain,(
% 1.36/0.54    ( ! [X50,X51] : (k1_tarski(sK1) != k1_tarski(X51) | sK0 != k1_relat_1(sK6(X50,X51)) | ~r2_hidden(X51,k2_relat_1(sK6(X50,X51)))) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f887,f45])).
% 1.36/0.54  fof(f887,plain,(
% 1.36/0.54    ( ! [X50,X51] : (k1_tarski(sK1) != k1_tarski(X51) | sK0 != k1_relat_1(sK6(X50,X51)) | ~v1_relat_1(sK6(X50,X51)) | ~r2_hidden(X51,k2_relat_1(sK6(X50,X51)))) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f878,f46])).
% 1.36/0.54  fof(f878,plain,(
% 1.36/0.54    ( ! [X50,X51] : (k1_tarski(sK1) != k1_tarski(X51) | sK0 != k1_relat_1(sK6(X50,X51)) | ~v1_funct_1(sK6(X50,X51)) | ~v1_relat_1(sK6(X50,X51)) | ~r2_hidden(X51,k2_relat_1(sK6(X50,X51)))) )),
% 1.36/0.54    inference(superposition,[],[f31,f846])).
% 1.36/0.54  fof(f846,plain,(
% 1.36/0.54    ( ! [X2,X3] : (k1_tarski(X2) = k2_relat_1(sK6(X3,X2)) | ~r2_hidden(X2,k2_relat_1(sK6(X3,X2)))) )),
% 1.36/0.54    inference(trivial_inequality_removal,[],[f845])).
% 1.36/0.54  fof(f845,plain,(
% 1.36/0.54    ( ! [X2,X3] : (X2 != X2 | k1_tarski(X2) = k2_relat_1(sK6(X3,X2)) | ~r2_hidden(X2,k2_relat_1(sK6(X3,X2)))) )),
% 1.36/0.54    inference(duplicate_literal_removal,[],[f843])).
% 1.36/0.54  fof(f843,plain,(
% 1.36/0.54    ( ! [X2,X3] : (X2 != X2 | k1_tarski(X2) = k2_relat_1(sK6(X3,X2)) | ~r2_hidden(X2,k2_relat_1(sK6(X3,X2))) | k1_tarski(X2) = k2_relat_1(sK6(X3,X2))) )),
% 1.36/0.54    inference(superposition,[],[f35,f841])).
% 1.36/0.54  fof(f841,plain,(
% 1.36/0.54    ( ! [X0,X1] : (sK2(X0,k2_relat_1(sK6(X1,X0))) = X0 | k1_tarski(X0) = k2_relat_1(sK6(X1,X0))) )),
% 1.36/0.54    inference(equality_resolution,[],[f715])).
% 1.36/0.54  fof(f715,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (X0 != X2 | sK2(X0,k2_relat_1(sK6(X1,X2))) = X2 | k1_tarski(X0) = k2_relat_1(sK6(X1,X2))) )),
% 1.36/0.54    inference(equality_factoring,[],[f410])).
% 1.36/0.54  fof(f410,plain,(
% 1.36/0.54    ( ! [X6,X8,X7] : (sK2(X7,k2_relat_1(sK6(X8,X6))) = X7 | sK2(X7,k2_relat_1(sK6(X8,X6))) = X6 | k1_tarski(X7) = k2_relat_1(sK6(X8,X6))) )),
% 1.36/0.54    inference(resolution,[],[f344,f34])).
% 1.36/0.54  fof(f34,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | sK2(X0,X1) = X0 | k1_tarski(X0) = X1) )),
% 1.36/0.54    inference(cnf_transformation,[],[f21])).
% 1.36/0.54  fof(f21,plain,(
% 1.36/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.36/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f20])).
% 1.36/0.54  fof(f20,plain,(
% 1.36/0.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f19,plain,(
% 1.36/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.36/0.54    inference(rectify,[],[f18])).
% 1.36/0.54  fof(f18,plain,(
% 1.36/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.36/0.54    inference(nnf_transformation,[],[f1])).
% 1.36/0.54  fof(f1,axiom,(
% 1.36/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.36/0.54  fof(f344,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_relat_1(sK6(X0,X1))) | X1 = X2) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f343,f93])).
% 1.36/0.54  fof(f93,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK5(sK6(X0,X1),X2),X0) | ~r2_hidden(X2,k2_relat_1(sK6(X0,X1)))) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f92,f45])).
% 1.36/0.54  fof(f92,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK5(sK6(X0,X1),X2),X0) | ~r2_hidden(X2,k2_relat_1(sK6(X0,X1))) | ~v1_relat_1(sK6(X0,X1))) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f91,f46])).
% 1.36/0.54  fof(f91,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK5(sK6(X0,X1),X2),X0) | ~r2_hidden(X2,k2_relat_1(sK6(X0,X1))) | ~v1_funct_1(sK6(X0,X1)) | ~v1_relat_1(sK6(X0,X1))) )),
% 1.36/0.54    inference(superposition,[],[f56,f47])).
% 1.36/0.54  fof(f56,plain,(
% 1.36/0.54    ( ! [X0,X5] : (r2_hidden(sK5(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.54    inference(equality_resolution,[],[f37])).
% 1.36/0.54  fof(f37,plain,(
% 1.36/0.54    ( ! [X0,X5,X1] : (r2_hidden(sK5(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f27])).
% 1.36/0.54  fof(f343,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (X1 = X2 | ~r2_hidden(X2,k2_relat_1(sK6(X0,X1))) | ~r2_hidden(sK5(sK6(X0,X1),X2),X0)) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f342,f45])).
% 1.36/0.54  fof(f342,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (X1 = X2 | ~r2_hidden(X2,k2_relat_1(sK6(X0,X1))) | ~v1_relat_1(sK6(X0,X1)) | ~r2_hidden(sK5(sK6(X0,X1),X2),X0)) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f338,f46])).
% 1.36/0.54  % (32665)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.36/0.54  fof(f338,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (X1 = X2 | ~r2_hidden(X2,k2_relat_1(sK6(X0,X1))) | ~v1_funct_1(sK6(X0,X1)) | ~v1_relat_1(sK6(X0,X1)) | ~r2_hidden(sK5(sK6(X0,X1),X2),X0)) )),
% 1.36/0.54    inference(superposition,[],[f55,f48])).
% 1.36/0.54  fof(f55,plain,(
% 1.36/0.54    ( ! [X0,X5] : (k1_funct_1(X0,sK5(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.54    inference(equality_resolution,[],[f38])).
% 1.36/0.54  fof(f38,plain,(
% 1.36/0.54    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK5(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f27])).
% 1.36/0.54  fof(f35,plain,(
% 1.36/0.54    ( ! [X0,X1] : (sK2(X0,X1) != X0 | k1_tarski(X0) = X1 | ~r2_hidden(sK2(X0,X1),X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f21])).
% 1.36/0.54  fof(f31,plain,(
% 1.36/0.54    ( ! [X2] : (k2_relat_1(X2) != k1_tarski(sK1) | k1_relat_1(X2) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f17])).
% 1.36/0.54  fof(f17,plain,(
% 1.36/0.54    ! [X2] : (k2_relat_1(X2) != k1_tarski(sK1) | k1_relat_1(X2) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & k1_xboole_0 != sK0),
% 1.36/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f16,f15])).
% 1.36/0.54  fof(f15,plain,(
% 1.36/0.54    ? [X0] : (? [X1] : ! [X2] : (k2_relat_1(X2) != k1_tarski(X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & k1_xboole_0 != X0) => (? [X1] : ! [X2] : (k2_relat_1(X2) != k1_tarski(X1) | k1_relat_1(X2) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & k1_xboole_0 != sK0)),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f16,plain,(
% 1.36/0.54    ? [X1] : ! [X2] : (k2_relat_1(X2) != k1_tarski(X1) | k1_relat_1(X2) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) => ! [X2] : (k2_relat_1(X2) != k1_tarski(sK1) | k1_relat_1(X2) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f9,plain,(
% 1.36/0.54    ? [X0] : (? [X1] : ! [X2] : (k2_relat_1(X2) != k1_tarski(X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & k1_xboole_0 != X0)),
% 1.36/0.54    inference(ennf_transformation,[],[f8])).
% 1.36/0.54  fof(f8,negated_conjecture,(
% 1.36/0.54    ~! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.36/0.54    inference(negated_conjecture,[],[f7])).
% 1.36/0.54  fof(f7,conjecture,(
% 1.36/0.54    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 1.36/0.54  fof(f503,plain,(
% 1.36/0.54    spl7_12 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5),
% 1.36/0.54    inference(avatar_split_clause,[],[f495,f143,f81,f76,f71,f500])).
% 1.36/0.54  fof(f495,plain,(
% 1.36/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 1.36/0.54    inference(resolution,[],[f359,f144])).
% 1.36/0.54  fof(f229,plain,(
% 1.36/0.54    spl7_5 | spl7_9),
% 1.36/0.54    inference(avatar_split_clause,[],[f228,f170,f143])).
% 1.36/0.54  fof(f170,plain,(
% 1.36/0.54    spl7_9 <=> ! [X0] : (k1_relat_1(X0) != sK0 | ~v1_relat_1(X0) | ~v1_funct_1(X0))),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.36/0.54  fof(f228,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k1_relat_1(X0) != sK0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f227,f66])).
% 1.36/0.54  fof(f66,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k1_funct_1(k1_xboole_0,X1) = X0 | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.36/0.54    inference(superposition,[],[f48,f65])).
% 1.36/0.54  fof(f65,plain,(
% 1.36/0.54    ( ! [X0] : (k1_xboole_0 = sK6(k1_xboole_0,X0)) )),
% 1.36/0.54    inference(equality_resolution,[],[f64])).
% 1.36/0.54  fof(f64,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = sK6(X0,X1)) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f63,f45])).
% 1.36/0.54  fof(f63,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = sK6(X0,X1) | ~v1_relat_1(sK6(X0,X1))) )),
% 1.36/0.54    inference(superposition,[],[f43,f47])).
% 1.36/0.54  fof(f43,plain,(
% 1.36/0.54    ( ! [X0] : (k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f13])).
% 1.36/0.54  fof(f13,plain,(
% 1.36/0.54    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 1.36/0.54    inference(flattening,[],[f12])).
% 1.36/0.54  fof(f12,plain,(
% 1.36/0.54    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 1.36/0.54    inference(ennf_transformation,[],[f4])).
% 1.36/0.54  fof(f4,axiom,(
% 1.36/0.54    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.36/0.54  fof(f227,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k1_tarski(sK1) != k1_funct_1(k1_xboole_0,X1) | k1_relat_1(X0) != sK0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.36/0.54    inference(superposition,[],[f31,f66])).
% 1.53/0.54  fof(f223,plain,(
% 1.53/0.54    ~spl7_9),
% 1.53/0.54    inference(avatar_contradiction_clause,[],[f219])).
% 1.53/0.54  fof(f219,plain,(
% 1.53/0.54    $false | ~spl7_9),
% 1.53/0.54    inference(unit_resulting_resolution,[],[f46,f45,f47,f171])).
% 1.53/0.54  fof(f171,plain,(
% 1.53/0.54    ( ! [X0] : (k1_relat_1(X0) != sK0 | ~v1_relat_1(X0) | ~v1_funct_1(X0)) ) | ~spl7_9),
% 1.53/0.54    inference(avatar_component_clause,[],[f170])).
% 1.53/0.54  fof(f84,plain,(
% 1.53/0.54    spl7_4),
% 1.53/0.54    inference(avatar_split_clause,[],[f69,f81])).
% 1.53/0.54  fof(f69,plain,(
% 1.53/0.54    v1_relat_1(k1_xboole_0)),
% 1.53/0.54    inference(superposition,[],[f45,f65])).
% 1.53/0.54  fof(f79,plain,(
% 1.53/0.54    spl7_3),
% 1.53/0.54    inference(avatar_split_clause,[],[f68,f76])).
% 1.53/0.54  fof(f68,plain,(
% 1.53/0.54    v1_funct_1(k1_xboole_0)),
% 1.53/0.54    inference(superposition,[],[f46,f65])).
% 1.53/0.54  fof(f74,plain,(
% 1.53/0.54    spl7_2),
% 1.53/0.54    inference(avatar_split_clause,[],[f67,f71])).
% 1.53/0.54  fof(f67,plain,(
% 1.53/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.53/0.54    inference(superposition,[],[f47,f65])).
% 1.53/0.54  fof(f61,plain,(
% 1.53/0.54    ~spl7_1),
% 1.53/0.54    inference(avatar_split_clause,[],[f30,f58])).
% 1.53/0.54  fof(f30,plain,(
% 1.53/0.54    k1_xboole_0 != sK0),
% 1.53/0.54    inference(cnf_transformation,[],[f17])).
% 1.53/0.54  % SZS output end Proof for theBenchmark
% 1.53/0.54  % (32676)------------------------------
% 1.53/0.54  % (32676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.54  % (32676)Termination reason: Refutation
% 1.53/0.54  
% 1.53/0.54  % (32676)Memory used [KB]: 6652
% 1.53/0.54  % (32676)Time elapsed: 0.114 s
% 1.53/0.54  % (32676)------------------------------
% 1.53/0.54  % (32676)------------------------------
% 1.53/0.55  % (32654)Success in time 0.186 s
%------------------------------------------------------------------------------
