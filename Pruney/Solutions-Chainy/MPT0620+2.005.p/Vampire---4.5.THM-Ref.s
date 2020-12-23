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
% DateTime   : Thu Dec  3 12:51:54 EST 2020

% Result     : Theorem 4.38s
% Output     : Refutation 4.38s
% Verified   : 
% Statistics : Number of formulae       :  210 (2405 expanded)
%              Number of leaves         :   29 ( 812 expanded)
%              Depth                    :   26
%              Number of atoms          :  815 (13740 expanded)
%              Number of equality atoms :  273 (5179 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3232,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f566,f664,f988,f1238,f1253,f1336,f1348,f1370,f1663,f2011,f2356,f2671,f2705,f2711,f2993,f3219])).

fof(f3219,plain,
    ( spl7_44
    | ~ spl7_2
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f3199,f984,f125,f1223])).

fof(f1223,plain,
    ( spl7_44
  <=> ! [X0] : r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f125,plain,
    ( spl7_2
  <=> ! [X0] : ~ r2_hidden(X0,k1_tarski(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f984,plain,
    ( spl7_26
  <=> ! [X81,X80] : r2_hidden(X81,k2_relat_1(sK6(X80,X81))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f3199,plain,
    ( ! [X81] : r2_hidden(X81,k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_26 ),
    inference(backward_demodulation,[],[f985,f3172])).

fof(f3172,plain,
    ( ! [X37,X36] : k1_xboole_0 = k2_relat_1(sK6(X36,X37))
    | ~ spl7_2
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f3160,f126])).

fof(f126,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_tarski(X0))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f125])).

fof(f3160,plain,
    ( ! [X37,X36] :
        ( r2_hidden(X37,k1_tarski(X37))
        | k1_xboole_0 = k2_relat_1(sK6(X36,X37)) )
    | ~ spl7_26 ),
    inference(superposition,[],[f985,f262])).

fof(f262,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK6(X0,X1))
      | k1_xboole_0 = k2_relat_1(sK6(X0,X1)) ) ),
    inference(equality_resolution,[],[f198])).

fof(f198,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | k1_xboole_0 = k2_relat_1(sK6(X0,X1))
      | k2_relat_1(sK6(X0,X1)) = k1_tarski(X2) ) ),
    inference(duplicate_literal_removal,[],[f195])).

fof(f195,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | k1_xboole_0 = k2_relat_1(sK6(X0,X1))
      | k2_relat_1(sK6(X0,X1)) = k1_tarski(X2)
      | k1_xboole_0 = k2_relat_1(sK6(X0,X1))
      | k2_relat_1(sK6(X0,X1)) = k1_tarski(X2) ) ),
    inference(superposition,[],[f43,f110])).

fof(f110,plain,(
    ! [X12,X10,X11] :
      ( sK5(k2_relat_1(sK6(X11,X10)),X12) = X10
      | k1_xboole_0 = k2_relat_1(sK6(X11,X10))
      | k2_relat_1(sK6(X11,X10)) = k1_tarski(X12) ) ),
    inference(resolution,[],[f106,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( sK5(X0,X1) != X1
        & r2_hidden(sK5(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f17,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK5(X0,X1) != X1
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_relat_1(sK6(X0,X1)))
      | X1 = X2 ) ),
    inference(subsumption_resolution,[],[f72,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(sK6(X0,X1),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(sK6(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f65,f45])).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK6(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK6(X0,X1)) = X0
      & v1_funct_1(sK6(X0,X1))
      & v1_relat_1(sK6(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f18,f30])).

fof(f30,plain,(
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

fof(f18,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(sK6(X0,X1),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(sK6(X0,X1)))
      | ~ v1_relat_1(sK6(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f64,f46])).

fof(f46,plain,(
    ! [X0,X1] : v1_funct_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(sK6(X0,X1),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(sK6(X0,X1)))
      | ~ v1_funct_1(sK6(X0,X1))
      | ~ v1_relat_1(sK6(X0,X1)) ) ),
    inference(superposition,[],[f53,f47])).

fof(f47,plain,(
    ! [X0,X1] : k1_relat_1(sK6(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK2(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ( sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
                  & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK4(X0,X5)) = X5
                    & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f26,f25,f24])).

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
              ( k1_funct_1(X0,X3) != sK2(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK2(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK2(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(X2,k2_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(sK4(sK6(X0,X1),X2),X0) ) ),
    inference(subsumption_resolution,[],[f71,f45])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(X2,k2_relat_1(sK6(X0,X1)))
      | ~ v1_relat_1(sK6(X0,X1))
      | ~ r2_hidden(sK4(sK6(X0,X1),X2),X0) ) ),
    inference(subsumption_resolution,[],[f67,f46])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(X2,k2_relat_1(sK6(X0,X1)))
      | ~ v1_funct_1(sK6(X0,X1))
      | ~ v1_relat_1(sK6(X0,X1))
      | ~ r2_hidden(sK4(sK6(X0,X1),X2),X0) ) ),
    inference(superposition,[],[f52,f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK6(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f985,plain,
    ( ! [X80,X81] : r2_hidden(X81,k2_relat_1(sK6(X80,X81)))
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f984])).

fof(f2993,plain,
    ( spl7_2
    | spl7_63
    | ~ spl7_14
    | ~ spl7_16
    | spl7_21 ),
    inference(avatar_split_clause,[],[f2992,f661,f630,f563,f2256,f125])).

fof(f2256,plain,
    ( spl7_63
  <=> ! [X2] : ~ r2_hidden(X2,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f563,plain,
    ( spl7_14
  <=> k1_xboole_0 = k2_relat_1(sK6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f630,plain,
    ( spl7_16
  <=> r2_hidden(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f661,plain,
    ( spl7_21
  <=> k1_xboole_0 = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f2992,plain,
    ( ! [X28,X29] :
        ( ~ r2_hidden(X29,k1_tarski(sK1))
        | ~ r2_hidden(X28,k1_tarski(X28)) )
    | ~ spl7_14
    | ~ spl7_16
    | spl7_21 ),
    inference(subsumption_resolution,[],[f2767,f663])).

fof(f663,plain,
    ( k1_xboole_0 != k1_tarski(sK1)
    | spl7_21 ),
    inference(avatar_component_clause,[],[f661])).

fof(f2767,plain,
    ( ! [X28,X29] :
        ( ~ r2_hidden(X29,k1_tarski(sK1))
        | k1_xboole_0 = k1_tarski(sK1)
        | ~ r2_hidden(X28,k1_tarski(X28)) )
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(superposition,[],[f1829,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK6(k1_tarski(X0),X1))
      | ~ r2_hidden(X0,k1_tarski(X0)) ) ),
    inference(superposition,[],[f81,f48])).

fof(f81,plain,(
    ! [X0,X1] : k2_relat_1(sK6(k1_tarski(X0),X1)) = k1_tarski(k1_funct_1(sK6(k1_tarski(X0),X1),X0)) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X2) != X0
      | k2_relat_1(sK6(X0,X1)) = k1_tarski(k1_funct_1(sK6(X0,X1),X2)) ) ),
    inference(subsumption_resolution,[],[f76,f45])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X2) != X0
      | k2_relat_1(sK6(X0,X1)) = k1_tarski(k1_funct_1(sK6(X0,X1),X2))
      | ~ v1_relat_1(sK6(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f75,f46])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X2) != X0
      | k2_relat_1(sK6(X0,X1)) = k1_tarski(k1_funct_1(sK6(X0,X1),X2))
      | ~ v1_funct_1(sK6(X0,X1))
      | ~ v1_relat_1(sK6(X0,X1)) ) ),
    inference(superposition,[],[f34,f47])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k1_relat_1(X1)
      | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f1829,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK6(X0,sK1)))
        | k1_xboole_0 = k2_relat_1(sK6(X0,sK1)) )
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f1828,f106])).

fof(f1828,plain,
    ( ! [X0,X1] :
        ( sK1 != X1
        | k1_xboole_0 = k2_relat_1(sK6(X0,sK1))
        | ~ r2_hidden(X1,k2_relat_1(sK6(X0,sK1))) )
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f1827,f45])).

fof(f1827,plain,
    ( ! [X0,X1] :
        ( sK1 != X1
        | k1_xboole_0 = k2_relat_1(sK6(X0,sK1))
        | ~ v1_relat_1(sK6(X0,sK1))
        | ~ r2_hidden(X1,k2_relat_1(sK6(X0,sK1))) )
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f1826,f46])).

fof(f1826,plain,
    ( ! [X0,X1] :
        ( sK1 != X1
        | k1_xboole_0 = k2_relat_1(sK6(X0,sK1))
        | ~ v1_funct_1(sK6(X0,sK1))
        | ~ v1_relat_1(sK6(X0,sK1))
        | ~ r2_hidden(X1,k2_relat_1(sK6(X0,sK1))) )
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f1825,f632])).

fof(f632,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f630])).

fof(f1825,plain,
    ( ! [X0,X1] :
        ( sK1 != X1
        | k1_xboole_0 = k2_relat_1(sK6(X0,sK1))
        | ~ r2_hidden(sK1,k1_xboole_0)
        | ~ v1_funct_1(sK6(X0,sK1))
        | ~ v1_relat_1(sK6(X0,sK1))
        | ~ r2_hidden(X1,k2_relat_1(sK6(X0,sK1))) )
    | ~ spl7_14 ),
    inference(duplicate_literal_removal,[],[f1823])).

fof(f1823,plain,
    ( ! [X0,X1] :
        ( sK1 != X1
        | k1_xboole_0 = k2_relat_1(sK6(X0,sK1))
        | ~ r2_hidden(sK1,k1_xboole_0)
        | ~ v1_funct_1(sK6(X0,sK1))
        | ~ v1_relat_1(sK6(X0,sK1))
        | ~ r2_hidden(X1,k2_relat_1(sK6(X0,sK1)))
        | k1_xboole_0 = k2_relat_1(sK6(X0,sK1)) )
    | ~ spl7_14 ),
    inference(superposition,[],[f100,f619])).

fof(f619,plain,
    ( ! [X23] :
        ( sK1 = sK2(sK6(X23,sK1),k1_xboole_0)
        | k1_xboole_0 = k2_relat_1(sK6(X23,sK1)) )
    | ~ spl7_14 ),
    inference(superposition,[],[f327,f565])).

fof(f565,plain,
    ( k1_xboole_0 = k2_relat_1(sK6(sK0,sK1))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f563])).

fof(f327,plain,(
    ! [X2,X0,X1] :
      ( sK2(sK6(X0,X1),k2_relat_1(sK6(X2,X1))) = X1
      | k2_relat_1(sK6(X0,X1)) = k2_relat_1(sK6(X2,X1)) ) ),
    inference(equality_resolution,[],[f212])).

fof(f212,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | sK2(sK6(X0,X1),k2_relat_1(sK6(X2,X3))) = X1
      | k2_relat_1(sK6(X0,X1)) = k2_relat_1(sK6(X2,X3)) ) ),
    inference(equality_factoring,[],[f162])).

fof(f162,plain,(
    ! [X2,X0,X3,X1] :
      ( sK2(sK6(X0,X1),k2_relat_1(sK6(X2,X3))) = X3
      | sK2(sK6(X0,X1),k2_relat_1(sK6(X2,X3))) = X1
      | k2_relat_1(sK6(X0,X1)) = k2_relat_1(sK6(X2,X3)) ) ),
    inference(resolution,[],[f159,f106])).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(sK6(X0,X1),X2),X2)
      | k2_relat_1(sK6(X0,X1)) = X2
      | sK2(sK6(X0,X1),X2) = X1 ) ),
    inference(subsumption_resolution,[],[f87,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(sK6(X0,X1),X2),X0)
      | k2_relat_1(sK6(X0,X1)) = X2
      | r2_hidden(sK2(sK6(X0,X1),X2),X2) ) ),
    inference(subsumption_resolution,[],[f79,f45])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(sK6(X0,X1),X2),X0)
      | k2_relat_1(sK6(X0,X1)) = X2
      | r2_hidden(sK2(sK6(X0,X1),X2),X2)
      | ~ v1_relat_1(sK6(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f78,f46])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(sK6(X0,X1),X2),X0)
      | k2_relat_1(sK6(X0,X1)) = X2
      | r2_hidden(sK2(sK6(X0,X1),X2),X2)
      | ~ v1_funct_1(sK6(X0,X1))
      | ~ v1_relat_1(sK6(X0,X1)) ) ),
    inference(superposition,[],[f39,f47])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | k2_relat_1(X0) = X1
      | r2_hidden(sK2(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( sK2(sK6(X0,X1),X2) = X1
      | k2_relat_1(sK6(X0,X1)) = X2
      | r2_hidden(sK2(sK6(X0,X1),X2),X2)
      | ~ r2_hidden(sK3(sK6(X0,X1),X2),X0) ) ),
    inference(subsumption_resolution,[],[f86,f45])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( sK2(sK6(X0,X1),X2) = X1
      | k2_relat_1(sK6(X0,X1)) = X2
      | r2_hidden(sK2(sK6(X0,X1),X2),X2)
      | ~ v1_relat_1(sK6(X0,X1))
      | ~ r2_hidden(sK3(sK6(X0,X1),X2),X0) ) ),
    inference(subsumption_resolution,[],[f82,f46])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( sK2(sK6(X0,X1),X2) = X1
      | k2_relat_1(sK6(X0,X1)) = X2
      | r2_hidden(sK2(sK6(X0,X1),X2),X2)
      | ~ v1_funct_1(sK6(X0,X1))
      | ~ v1_relat_1(sK6(X0,X1))
      | ~ r2_hidden(sK3(sK6(X0,X1),X2),X0) ) ),
    inference(superposition,[],[f40,f48])).

fof(f40,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
      | k2_relat_1(X0) = X1
      | r2_hidden(sK2(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f100,plain,(
    ! [X6,X4,X5] :
      ( sK2(X4,X6) != X5
      | k2_relat_1(X4) = X6
      | ~ r2_hidden(sK2(X4,X6),X6)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ r2_hidden(X5,k2_relat_1(X4)) ) ),
    inference(subsumption_resolution,[],[f95,f53])).

fof(f95,plain,(
    ! [X6,X4,X5] :
      ( sK2(X4,X6) != X5
      | k2_relat_1(X4) = X6
      | ~ r2_hidden(sK4(X4,X5),k1_relat_1(X4))
      | ~ r2_hidden(sK2(X4,X6),X6)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ r2_hidden(X5,k2_relat_1(X4)) ) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X6,X4,X5] :
      ( sK2(X4,X6) != X5
      | k2_relat_1(X4) = X6
      | ~ r2_hidden(sK4(X4,X5),k1_relat_1(X4))
      | ~ r2_hidden(sK2(X4,X6),X6)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ r2_hidden(X5,k2_relat_1(X4))
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f41,f52])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X0,X3) != sK2(X0,X1)
      | k2_relat_1(X0) = X1
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(sK2(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2711,plain,
    ( k1_xboole_0 != k2_relat_1(sK6(sK0,sK1))
    | ~ r2_hidden(sK1,k2_relat_1(sK6(sK0,sK1)))
    | r2_hidden(sK1,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2705,plain,
    ( ~ spl7_15
    | spl7_21
    | ~ spl7_63 ),
    inference(avatar_contradiction_clause,[],[f2704])).

fof(f2704,plain,
    ( $false
    | ~ spl7_15
    | spl7_21
    | ~ spl7_63 ),
    inference(subsumption_resolution,[],[f2697,f2427])).

fof(f2427,plain,
    ( ! [X0] : k1_tarski(X0) != sK0
    | spl7_21
    | ~ spl7_63 ),
    inference(superposition,[],[f2423,f47])).

fof(f2423,plain,
    ( ! [X45,X46] : sK0 != k1_relat_1(sK6(k1_tarski(X45),X46))
    | spl7_21
    | ~ spl7_63 ),
    inference(subsumption_resolution,[],[f2422,f45])).

fof(f2422,plain,
    ( ! [X45,X46] :
        ( sK0 != k1_relat_1(sK6(k1_tarski(X45),X46))
        | ~ v1_relat_1(sK6(k1_tarski(X45),X46)) )
    | spl7_21
    | ~ spl7_63 ),
    inference(subsumption_resolution,[],[f2402,f46])).

fof(f2402,plain,
    ( ! [X45,X46] :
        ( sK0 != k1_relat_1(sK6(k1_tarski(X45),X46))
        | ~ v1_funct_1(sK6(k1_tarski(X45),X46))
        | ~ v1_relat_1(sK6(k1_tarski(X45),X46)) )
    | spl7_21
    | ~ spl7_63 ),
    inference(trivial_inequality_removal,[],[f2401])).

fof(f2401,plain,
    ( ! [X45,X46] :
        ( k1_tarski(sK1) != k1_tarski(sK1)
        | sK0 != k1_relat_1(sK6(k1_tarski(X45),X46))
        | ~ v1_funct_1(sK6(k1_tarski(X45),X46))
        | ~ v1_relat_1(sK6(k1_tarski(X45),X46)) )
    | spl7_21
    | ~ spl7_63 ),
    inference(superposition,[],[f33,f2292])).

fof(f2292,plain,
    ( ! [X0,X1] : k1_tarski(sK1) = k2_relat_1(sK6(k1_tarski(X0),X1))
    | spl7_21
    | ~ spl7_63 ),
    inference(backward_demodulation,[],[f81,f2272])).

fof(f2272,plain,
    ( ! [X9] : k1_tarski(sK1) = k1_tarski(X9)
    | spl7_21
    | ~ spl7_63 ),
    inference(subsumption_resolution,[],[f2271,f663])).

fof(f2271,plain,
    ( ! [X9] :
        ( k1_xboole_0 = k1_tarski(sK1)
        | k1_tarski(sK1) = k1_tarski(X9) )
    | ~ spl7_63 ),
    inference(resolution,[],[f2257,f42])).

fof(f2257,plain,
    ( ! [X2] : ~ r2_hidden(X2,k1_tarski(sK1))
    | ~ spl7_63 ),
    inference(avatar_component_clause,[],[f2256])).

fof(f33,plain,(
    ! [X2] :
      ( k2_relat_1(X2) != k1_tarski(sK1)
      | k1_relat_1(X2) != sK0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ! [X2] :
        ( k2_relat_1(X2) != k1_tarski(sK1)
        | k1_relat_1(X2) != sK0
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
          ! [X2] :
            ( k1_tarski(X1) != k2_relat_1(X2)
            | k1_relat_1(X2) != X0
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & k1_xboole_0 != X0 )
   => ( ? [X1] :
        ! [X2] :
          ( k1_tarski(X1) != k2_relat_1(X2)
          | k1_relat_1(X2) != sK0
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
      ! [X2] :
        ( k1_tarski(X1) != k2_relat_1(X2)
        | k1_relat_1(X2) != sK0
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
   => ! [X2] :
        ( k2_relat_1(X2) != k1_tarski(sK1)
        | k1_relat_1(X2) != sK0
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
        ! [X2] :
          ( k1_tarski(X1) != k2_relat_1(X2)
          | k1_relat_1(X2) != X0
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( k1_xboole_0 != X0
       => ! [X1] :
          ? [X2] :
            ( k1_tarski(X1) = k2_relat_1(X2)
            & k1_relat_1(X2) = X0
            & v1_funct_1(X2)
            & v1_relat_1(X2) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(f2697,plain,
    ( sK0 = k1_tarski(sK1)
    | ~ spl7_15
    | spl7_21
    | ~ spl7_63 ),
    inference(resolution,[],[f628,f2416])).

fof(f2416,plain,
    ( ! [X39,X41,X40] :
        ( r2_hidden(sK2(sK6(k1_tarski(X39),X40),X41),X41)
        | k1_tarski(sK1) = X41 )
    | spl7_21
    | ~ spl7_63 ),
    inference(subsumption_resolution,[],[f2415,f45])).

fof(f2415,plain,
    ( ! [X39,X41,X40] :
        ( ~ v1_relat_1(sK6(k1_tarski(X39),X40))
        | k1_tarski(sK1) = X41
        | r2_hidden(sK2(sK6(k1_tarski(X39),X40),X41),X41) )
    | spl7_21
    | ~ spl7_63 ),
    inference(subsumption_resolution,[],[f2414,f46])).

fof(f2414,plain,
    ( ! [X39,X41,X40] :
        ( ~ v1_funct_1(sK6(k1_tarski(X39),X40))
        | ~ v1_relat_1(sK6(k1_tarski(X39),X40))
        | k1_tarski(sK1) = X41
        | r2_hidden(sK2(sK6(k1_tarski(X39),X40),X41),X41) )
    | spl7_21
    | ~ spl7_63 ),
    inference(subsumption_resolution,[],[f2399,f2257])).

fof(f2399,plain,
    ( ! [X39,X41,X40] :
        ( r2_hidden(sK2(sK6(k1_tarski(X39),X40),X41),k1_tarski(sK1))
        | ~ v1_funct_1(sK6(k1_tarski(X39),X40))
        | ~ v1_relat_1(sK6(k1_tarski(X39),X40))
        | k1_tarski(sK1) = X41
        | r2_hidden(sK2(sK6(k1_tarski(X39),X40),X41),X41) )
    | spl7_21
    | ~ spl7_63 ),
    inference(superposition,[],[f90,f2292])).

fof(f90,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK2(X3,X4),k2_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | k2_relat_1(X3) = X4
      | r2_hidden(sK2(X3,X4),X4) ) ),
    inference(subsumption_resolution,[],[f85,f39])).

fof(f85,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK2(X3,X4),k2_relat_1(X3))
      | ~ r2_hidden(sK3(X3,X4),k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | k2_relat_1(X3) = X4
      | r2_hidden(sK2(X3,X4),X4) ) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK2(X3,X4),k2_relat_1(X3))
      | ~ r2_hidden(sK3(X3,X4),k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | k2_relat_1(X3) = X4
      | r2_hidden(sK2(X3,X4),X4)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f35,f40])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(f628,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f627])).

fof(f627,plain,
    ( spl7_15
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f2671,plain,
    ( spl7_15
    | spl7_44
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f2654,f2204,f1223,f627])).

fof(f2204,plain,
    ( spl7_62
  <=> ! [X25,X28] :
        ( sK0 != X28
        | k1_xboole_0 = k2_relat_1(sK6(X28,X25)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f2654,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k1_xboole_0)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl7_62 ),
    inference(superposition,[],[f63,f2650])).

fof(f2650,plain,
    ( ! [X0] : k1_xboole_0 = k2_relat_1(sK6(sK0,X0))
    | ~ spl7_62 ),
    inference(equality_resolution,[],[f2205])).

fof(f2205,plain,
    ( ! [X28,X25] :
        ( sK0 != X28
        | k1_xboole_0 = k2_relat_1(sK6(X28,X25)) )
    | ~ spl7_62 ),
    inference(avatar_component_clause,[],[f2204])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X1,k2_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(X2,X0) ) ),
    inference(forward_demodulation,[],[f61,f47])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(X2,k1_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(X2,X0) ) ),
    inference(subsumption_resolution,[],[f60,f45])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(X2,k1_relat_1(sK6(X0,X1)))
      | ~ v1_relat_1(sK6(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(subsumption_resolution,[],[f59,f46])).

% (651)Time limit reached!
% (651)------------------------------
% (651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(X2,k1_relat_1(sK6(X0,X1)))
      | ~ v1_funct_1(sK6(X0,X1))
      | ~ v1_relat_1(sK6(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f35,f48])).

% (651)Termination reason: Time limit

fof(f2356,plain,
    ( spl7_62
    | spl7_21
    | ~ spl7_63 ),
    inference(avatar_split_clause,[],[f2355,f2256,f661,f2204])).

% (651)Memory used [KB]: 8827
% (651)Time elapsed: 0.526 s
% (651)------------------------------
% (651)------------------------------
fof(f2355,plain,
    ( ! [X17,X15] :
        ( sK0 != X17
        | k1_xboole_0 = k2_relat_1(sK6(X17,X15)) )
    | spl7_21
    | ~ spl7_63 ),
    inference(subsumption_resolution,[],[f2342,f2295])).

fof(f2295,plain,
    ( ! [X0,X1] : k1_tarski(X0) = k1_tarski(X1)
    | spl7_21
    | ~ spl7_63 ),
    inference(superposition,[],[f2272,f2272])).

fof(f2342,plain,
    ( ! [X17,X15,X16] :
        ( k1_tarski(sK1) != k1_tarski(X16)
        | sK0 != X17
        | k1_xboole_0 = k2_relat_1(sK6(X17,X15)) )
    | spl7_21
    | ~ spl7_63 ),
    inference(superposition,[],[f539,f2295])).

fof(f539,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) != k1_tarski(sK1)
      | sK0 != X0
      | k1_xboole_0 = k2_relat_1(sK6(X0,X1)) ) ),
    inference(superposition,[],[f538,f47])).

fof(f538,plain,(
    ! [X83,X84] :
      ( sK0 != k1_relat_1(sK6(X83,X84))
      | k1_tarski(sK1) != k1_tarski(X84)
      | k1_xboole_0 = k2_relat_1(sK6(X83,X84)) ) ),
    inference(subsumption_resolution,[],[f537,f45])).

fof(f537,plain,(
    ! [X83,X84] :
      ( k1_tarski(sK1) != k1_tarski(X84)
      | sK0 != k1_relat_1(sK6(X83,X84))
      | ~ v1_relat_1(sK6(X83,X84))
      | k1_xboole_0 = k2_relat_1(sK6(X83,X84)) ) ),
    inference(subsumption_resolution,[],[f523,f46])).

fof(f523,plain,(
    ! [X83,X84] :
      ( k1_tarski(sK1) != k1_tarski(X84)
      | sK0 != k1_relat_1(sK6(X83,X84))
      | ~ v1_funct_1(sK6(X83,X84))
      | ~ v1_relat_1(sK6(X83,X84))
      | k1_xboole_0 = k2_relat_1(sK6(X83,X84)) ) ),
    inference(superposition,[],[f33,f262])).

fof(f2011,plain,
    ( spl7_55
    | spl7_12
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f718,f563,f320,f2003])).

fof(f2003,plain,
    ( spl7_55
  <=> r2_hidden(sK1,k2_relat_1(sK6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f320,plain,
    ( spl7_12
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k2_relat_1(sK6(X0,X1))
        | r2_hidden(X1,k2_relat_1(sK6(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f718,plain,
    ( ! [X161,X160] :
        ( k1_xboole_0 = k2_relat_1(sK6(X160,X161))
        | r2_hidden(X161,k2_relat_1(sK6(X160,X161)))
        | r2_hidden(sK1,k2_relat_1(sK6(sK0,sK1))) )
    | ~ spl7_14 ),
    inference(superposition,[],[f565,f392])).

fof(f392,plain,(
    ! [X39,X37,X38,X40] :
      ( k2_relat_1(sK6(X39,X40)) = k2_relat_1(sK6(X37,X38))
      | r2_hidden(X38,k2_relat_1(sK6(X37,X38)))
      | r2_hidden(X40,k2_relat_1(sK6(X39,X40))) ) ),
    inference(subsumption_resolution,[],[f391,f236])).

fof(f236,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_relat_1(sK6(X1,X0)))
      | r2_hidden(X0,k2_relat_1(sK6(X1,X0))) ) ),
    inference(resolution,[],[f177,f63])).

fof(f177,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_relat_1(sK6(k2_relat_1(sK6(X0,X1)),X2)))
      | r2_hidden(X1,k2_relat_1(sK6(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f172])).

fof(f172,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,k2_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(X3,k2_relat_1(sK6(k2_relat_1(sK6(X0,X1)),X2)))
      | ~ r2_hidden(X3,k2_relat_1(sK6(k2_relat_1(sK6(X0,X1)),X2))) ) ),
    inference(superposition,[],[f66,f109])).

fof(f109,plain,(
    ! [X6,X8,X7,X9] :
      ( sK4(sK6(k2_relat_1(sK6(X7,X6)),X8),X9) = X6
      | ~ r2_hidden(X9,k2_relat_1(sK6(k2_relat_1(sK6(X7,X6)),X8))) ) ),
    inference(resolution,[],[f106,f66])).

fof(f391,plain,(
    ! [X39,X37,X38,X40] :
      ( r2_hidden(X38,k2_relat_1(sK6(X37,X38)))
      | k2_relat_1(sK6(X39,X40)) = k2_relat_1(sK6(X37,X38))
      | r2_hidden(X38,k2_relat_1(sK6(X39,X40)))
      | r2_hidden(X40,k2_relat_1(sK6(X39,X40))) ) ),
    inference(subsumption_resolution,[],[f390,f45])).

fof(f390,plain,(
    ! [X39,X37,X38,X40] :
      ( r2_hidden(X38,k2_relat_1(sK6(X37,X38)))
      | ~ v1_relat_1(sK6(X37,X38))
      | k2_relat_1(sK6(X39,X40)) = k2_relat_1(sK6(X37,X38))
      | r2_hidden(X38,k2_relat_1(sK6(X39,X40)))
      | r2_hidden(X40,k2_relat_1(sK6(X39,X40))) ) ),
    inference(subsumption_resolution,[],[f377,f46])).

fof(f377,plain,(
    ! [X39,X37,X38,X40] :
      ( r2_hidden(X38,k2_relat_1(sK6(X37,X38)))
      | ~ v1_funct_1(sK6(X37,X38))
      | ~ v1_relat_1(sK6(X37,X38))
      | k2_relat_1(sK6(X39,X40)) = k2_relat_1(sK6(X37,X38))
      | r2_hidden(X38,k2_relat_1(sK6(X39,X40)))
      | r2_hidden(X40,k2_relat_1(sK6(X39,X40))) ) ),
    inference(duplicate_literal_removal,[],[f374])).

fof(f374,plain,(
    ! [X39,X37,X38,X40] :
      ( r2_hidden(X38,k2_relat_1(sK6(X37,X38)))
      | ~ v1_funct_1(sK6(X37,X38))
      | ~ v1_relat_1(sK6(X37,X38))
      | k2_relat_1(sK6(X39,X40)) = k2_relat_1(sK6(X37,X38))
      | r2_hidden(X38,k2_relat_1(sK6(X39,X40)))
      | k2_relat_1(sK6(X39,X40)) = k2_relat_1(sK6(X37,X38))
      | r2_hidden(X40,k2_relat_1(sK6(X39,X40))) ) ),
    inference(superposition,[],[f90,f363])).

fof(f363,plain,(
    ! [X2,X0,X3,X1] :
      ( sK2(sK6(X0,X1),k2_relat_1(sK6(X2,X3))) = X1
      | k2_relat_1(sK6(X0,X1)) = k2_relat_1(sK6(X2,X3))
      | r2_hidden(X3,k2_relat_1(sK6(X2,X3))) ) ),
    inference(subsumption_resolution,[],[f221,f212])).

fof(f221,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,k2_relat_1(sK6(X2,X3)))
      | k2_relat_1(sK6(X0,X1)) = k2_relat_1(sK6(X2,X3))
      | X1 = X3
      | sK2(sK6(X0,X1),k2_relat_1(sK6(X2,X3))) = X1 ) ),
    inference(duplicate_literal_removal,[],[f203])).

fof(f203,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,k2_relat_1(sK6(X2,X3)))
      | k2_relat_1(sK6(X0,X1)) = k2_relat_1(sK6(X2,X3))
      | X1 = X3
      | sK2(sK6(X0,X1),k2_relat_1(sK6(X2,X3))) = X1
      | k2_relat_1(sK6(X0,X1)) = k2_relat_1(sK6(X2,X3)) ) ),
    inference(superposition,[],[f159,f162])).

fof(f1663,plain,
    ( ~ spl7_14
    | spl7_21
    | ~ spl7_44 ),
    inference(avatar_contradiction_clause,[],[f1662])).

fof(f1662,plain,
    ( $false
    | ~ spl7_14
    | spl7_21
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f1603,f1554])).

fof(f1554,plain,
    ( ! [X0] : sK1 = X0
    | ~ spl7_14
    | ~ spl7_44 ),
    inference(resolution,[],[f1224,f606])).

fof(f606,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | sK1 = X1 )
    | ~ spl7_14 ),
    inference(superposition,[],[f106,f565])).

fof(f1224,plain,
    ( ! [X0] : r2_hidden(X0,k1_xboole_0)
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f1223])).

fof(f1603,plain,
    ( k1_xboole_0 != sK1
    | ~ spl7_14
    | spl7_21
    | ~ spl7_44 ),
    inference(superposition,[],[f663,f1554])).

fof(f1370,plain,
    ( spl7_22
    | spl7_23 ),
    inference(avatar_split_clause,[],[f1369,f772,f769])).

fof(f769,plain,
    ( spl7_22
  <=> ! [X179,X180] :
        ( k1_tarski(sK1) != k2_relat_1(sK6(X179,X180))
        | r2_hidden(X180,k2_relat_1(sK6(X179,X180))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f772,plain,
    ( spl7_23
  <=> ! [X178,X177] :
        ( sK0 != X177
        | r2_hidden(X178,k2_relat_1(sK6(X177,X178))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f1369,plain,(
    ! [X14,X12,X15,X13] :
      ( sK0 != X12
      | k1_tarski(sK1) != k2_relat_1(sK6(X14,X15))
      | r2_hidden(X15,k2_relat_1(sK6(X14,X15)))
      | r2_hidden(X13,k2_relat_1(sK6(X12,X13))) ) ),
    inference(forward_demodulation,[],[f1368,f47])).

fof(f1368,plain,(
    ! [X14,X12,X15,X13] :
      ( k1_tarski(sK1) != k2_relat_1(sK6(X14,X15))
      | sK0 != k1_relat_1(sK6(X12,X13))
      | r2_hidden(X15,k2_relat_1(sK6(X14,X15)))
      | r2_hidden(X13,k2_relat_1(sK6(X12,X13))) ) ),
    inference(subsumption_resolution,[],[f1367,f45])).

fof(f1367,plain,(
    ! [X14,X12,X15,X13] :
      ( k1_tarski(sK1) != k2_relat_1(sK6(X14,X15))
      | sK0 != k1_relat_1(sK6(X12,X13))
      | ~ v1_relat_1(sK6(X12,X13))
      | r2_hidden(X15,k2_relat_1(sK6(X14,X15)))
      | r2_hidden(X13,k2_relat_1(sK6(X12,X13))) ) ),
    inference(subsumption_resolution,[],[f1356,f46])).

fof(f1356,plain,(
    ! [X14,X12,X15,X13] :
      ( k1_tarski(sK1) != k2_relat_1(sK6(X14,X15))
      | sK0 != k1_relat_1(sK6(X12,X13))
      | ~ v1_funct_1(sK6(X12,X13))
      | ~ v1_relat_1(sK6(X12,X13))
      | r2_hidden(X15,k2_relat_1(sK6(X14,X15)))
      | r2_hidden(X13,k2_relat_1(sK6(X12,X13))) ) ),
    inference(superposition,[],[f33,f392])).

fof(f1348,plain,
    ( spl7_15
    | spl7_16
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f1123,f563,f630,f627])).

fof(f1123,plain,
    ( ! [X0] :
        ( r2_hidden(sK1,k1_xboole_0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl7_14 ),
    inference(superposition,[],[f63,f565])).

fof(f1336,plain,
    ( spl7_1
    | ~ spl7_12
    | ~ spl7_15 ),
    inference(avatar_contradiction_clause,[],[f1335])).

fof(f1335,plain,
    ( $false
    | spl7_1
    | ~ spl7_12
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f1334,f57])).

fof(f57,plain,
    ( k1_xboole_0 != sK0
    | spl7_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl7_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f1334,plain,
    ( k1_xboole_0 = sK0
    | spl7_1
    | ~ spl7_12
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f1307,f628])).

fof(f1307,plain,
    ( ! [X37] :
        ( r2_hidden(X37,sK0)
        | k1_xboole_0 = sK0 )
    | spl7_1
    | ~ spl7_12
    | ~ spl7_15 ),
    inference(superposition,[],[f321,f1283])).

fof(f1283,plain,
    ( ! [X1] : sK0 = k2_relat_1(sK6(sK0,X1))
    | spl7_1
    | ~ spl7_15 ),
    inference(forward_demodulation,[],[f1268,f1244])).

fof(f1244,plain,
    ( ! [X9] : sK0 = k1_tarski(X9)
    | spl7_1
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f1243,f57])).

fof(f1243,plain,
    ( ! [X9] :
        ( k1_xboole_0 = sK0
        | sK0 = k1_tarski(X9) )
    | ~ spl7_15 ),
    inference(resolution,[],[f628,f42])).

fof(f1268,plain,
    ( ! [X0,X1] : k2_relat_1(sK6(sK0,X1)) = k1_tarski(k1_funct_1(sK6(sK0,X1),X0))
    | spl7_1
    | ~ spl7_15 ),
    inference(backward_demodulation,[],[f81,f1244])).

fof(f321,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X1,k2_relat_1(sK6(X0,X1)))
        | k1_xboole_0 = k2_relat_1(sK6(X0,X1)) )
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f320])).

fof(f1253,plain,
    ( ~ spl7_16
    | ~ spl7_18 ),
    inference(avatar_contradiction_clause,[],[f1245])).

fof(f1245,plain,
    ( $false
    | ~ spl7_16
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f632,f640])).

fof(f640,plain,
    ( ! [X19] : ~ r2_hidden(X19,k1_xboole_0)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f639])).

fof(f639,plain,
    ( spl7_18
  <=> ! [X19] : ~ r2_hidden(X19,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f1238,plain,
    ( spl7_44
    | ~ spl7_2
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f1188,f772,f125,f1223])).

fof(f1188,plain,
    ( ! [X0] : r2_hidden(X0,k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_23 ),
    inference(backward_demodulation,[],[f1162,f1171])).

fof(f1171,plain,
    ( ! [X12] : k1_xboole_0 = k2_relat_1(sK6(sK0,X12))
    | ~ spl7_2
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f1169,f126])).

fof(f1169,plain,
    ( ! [X12] :
        ( r2_hidden(X12,k1_tarski(X12))
        | k1_xboole_0 = k2_relat_1(sK6(sK0,X12)) )
    | ~ spl7_23 ),
    inference(superposition,[],[f1162,f262])).

fof(f1162,plain,
    ( ! [X0] : r2_hidden(X0,k2_relat_1(sK6(sK0,X0)))
    | ~ spl7_23 ),
    inference(equality_resolution,[],[f773])).

fof(f773,plain,
    ( ! [X177,X178] :
        ( sK0 != X177
        | r2_hidden(X178,k2_relat_1(sK6(X177,X178))) )
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f772])).

fof(f988,plain,
    ( spl7_26
    | spl7_18
    | ~ spl7_2
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f969,f769,f125,f639,f984])).

fof(f969,plain,
    ( ! [X90,X88,X87] :
        ( ~ r2_hidden(X90,k1_xboole_0)
        | r2_hidden(X88,k2_relat_1(sK6(X87,X88))) )
    | ~ spl7_2
    | ~ spl7_22 ),
    inference(superposition,[],[f242,f930])).

fof(f930,plain,
    ( ! [X0] : k1_xboole_0 = k2_relat_1(sK6(X0,sK1))
    | ~ spl7_2
    | ~ spl7_22 ),
    inference(equality_resolution,[],[f927])).

fof(f927,plain,
    ( ! [X17,X16] :
        ( k1_tarski(sK1) != k1_tarski(X17)
        | k1_xboole_0 = k2_relat_1(sK6(X16,X17)) )
    | ~ spl7_2
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f925,f126])).

fof(f925,plain,
    ( ! [X17,X16] :
        ( k1_tarski(sK1) != k1_tarski(X17)
        | r2_hidden(X17,k1_tarski(X17))
        | k1_xboole_0 = k2_relat_1(sK6(X16,X17)) )
    | ~ spl7_22 ),
    inference(superposition,[],[f770,f262])).

fof(f770,plain,
    ( ! [X180,X179] :
        ( k1_tarski(sK1) != k2_relat_1(sK6(X179,X180))
        | r2_hidden(X180,k2_relat_1(sK6(X179,X180))) )
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f769])).

fof(f242,plain,(
    ! [X30,X28,X31,X29,X27] :
      ( ~ r2_hidden(X29,k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(X28,X27)),X30)),X31)))
      | r2_hidden(X27,k2_relat_1(sK6(X28,X27))) ) ),
    inference(resolution,[],[f177,f66])).

fof(f664,plain,
    ( ~ spl7_21
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f659,f563,f661])).

fof(f659,plain,
    ( k1_xboole_0 != k1_tarski(sK1)
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f658,f45])).

fof(f658,plain,
    ( k1_xboole_0 != k1_tarski(sK1)
    | ~ v1_relat_1(sK6(sK0,sK1))
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f657,f46])).

fof(f657,plain,
    ( k1_xboole_0 != k1_tarski(sK1)
    | ~ v1_funct_1(sK6(sK0,sK1))
    | ~ v1_relat_1(sK6(sK0,sK1))
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f625,f47])).

fof(f625,plain,
    ( k1_xboole_0 != k1_tarski(sK1)
    | sK0 != k1_relat_1(sK6(sK0,sK1))
    | ~ v1_funct_1(sK6(sK0,sK1))
    | ~ v1_relat_1(sK6(sK0,sK1))
    | ~ spl7_14 ),
    inference(superposition,[],[f33,f565])).

fof(f566,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f561,f563])).

fof(f561,plain,(
    k1_xboole_0 = k2_relat_1(sK6(sK0,sK1)) ),
    inference(equality_resolution,[],[f560])).

fof(f560,plain,(
    ! [X0] :
      ( sK0 != X0
      | k1_xboole_0 = k2_relat_1(sK6(X0,sK1)) ) ),
    inference(equality_resolution,[],[f539])).

fof(f58,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f32,f55])).

fof(f32,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:42:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (676)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (692)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (671)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (677)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (671)Refutation not found, incomplete strategy% (671)------------------------------
% 0.21/0.51  % (671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (671)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (671)Memory used [KB]: 6140
% 0.21/0.51  % (671)Time elapsed: 0.108 s
% 0.21/0.51  % (671)------------------------------
% 0.21/0.51  % (671)------------------------------
% 0.21/0.51  % (676)Refutation not found, incomplete strategy% (676)------------------------------
% 0.21/0.51  % (676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (676)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (676)Memory used [KB]: 10618
% 0.21/0.51  % (676)Time elapsed: 0.102 s
% 0.21/0.51  % (676)------------------------------
% 0.21/0.51  % (676)------------------------------
% 0.21/0.52  % (684)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (690)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (650)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (670)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (682)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (669)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (669)Refutation not found, incomplete strategy% (669)------------------------------
% 0.21/0.53  % (669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (669)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (669)Memory used [KB]: 10618
% 0.21/0.53  % (669)Time elapsed: 0.113 s
% 0.21/0.53  % (669)------------------------------
% 0.21/0.53  % (669)------------------------------
% 0.21/0.53  % (674)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (651)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (680)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (697)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (695)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (679)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (696)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (679)Refutation not found, incomplete strategy% (679)------------------------------
% 0.21/0.54  % (679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (679)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (679)Memory used [KB]: 10618
% 0.21/0.54  % (679)Time elapsed: 0.138 s
% 0.21/0.54  % (679)------------------------------
% 0.21/0.54  % (679)------------------------------
% 0.21/0.54  % (690)Refutation not found, incomplete strategy% (690)------------------------------
% 0.21/0.54  % (690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (690)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (690)Memory used [KB]: 10618
% 0.21/0.54  % (690)Time elapsed: 0.083 s
% 0.21/0.54  % (690)------------------------------
% 0.21/0.54  % (690)------------------------------
% 0.21/0.54  % (672)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (689)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (673)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (689)Refutation not found, incomplete strategy% (689)------------------------------
% 0.21/0.54  % (689)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (689)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (689)Memory used [KB]: 1663
% 0.21/0.54  % (689)Time elapsed: 0.140 s
% 0.21/0.54  % (689)------------------------------
% 0.21/0.54  % (689)------------------------------
% 0.21/0.54  % (694)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (688)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (688)Refutation not found, incomplete strategy% (688)------------------------------
% 0.21/0.55  % (688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (688)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (688)Memory used [KB]: 10746
% 0.21/0.55  % (688)Time elapsed: 0.137 s
% 0.21/0.55  % (688)------------------------------
% 0.21/0.55  % (688)------------------------------
% 0.21/0.55  % (694)Refutation not found, incomplete strategy% (694)------------------------------
% 0.21/0.55  % (694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (694)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (694)Memory used [KB]: 10746
% 0.21/0.55  % (694)Time elapsed: 0.138 s
% 0.21/0.55  % (694)------------------------------
% 0.21/0.55  % (694)------------------------------
% 0.21/0.55  % (685)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (687)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (685)Refutation not found, incomplete strategy% (685)------------------------------
% 0.21/0.55  % (685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (685)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (685)Memory used [KB]: 10618
% 0.21/0.55  % (685)Time elapsed: 0.149 s
% 0.21/0.55  % (685)------------------------------
% 0.21/0.55  % (685)------------------------------
% 0.21/0.55  % (686)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (683)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (683)Refutation not found, incomplete strategy% (683)------------------------------
% 0.21/0.55  % (683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (683)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (683)Memory used [KB]: 6140
% 0.21/0.55  % (683)Time elapsed: 0.146 s
% 0.21/0.55  % (683)------------------------------
% 0.21/0.55  % (683)------------------------------
% 0.21/0.55  % (678)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (678)Refutation not found, incomplete strategy% (678)------------------------------
% 0.21/0.56  % (678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (678)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (678)Memory used [KB]: 10618
% 0.21/0.56  % (678)Time elapsed: 0.150 s
% 0.21/0.56  % (678)------------------------------
% 0.21/0.56  % (678)------------------------------
% 0.21/0.56  % (681)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (693)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (691)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.56  % (693)Refutation not found, incomplete strategy% (693)------------------------------
% 0.21/0.56  % (693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (693)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (693)Memory used [KB]: 6268
% 0.21/0.56  % (693)Time elapsed: 0.120 s
% 0.21/0.56  % (693)------------------------------
% 0.21/0.56  % (693)------------------------------
% 2.10/0.66  % (698)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.10/0.66  % (699)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.10/0.67  % (700)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.10/0.68  % (701)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.10/0.68  % (705)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.10/0.68  % (704)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.10/0.69  % (708)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.10/0.69  % (703)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.66/0.70  % (710)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 2.66/0.71  % (702)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.66/0.71  % (706)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.66/0.71  % (706)Refutation not found, incomplete strategy% (706)------------------------------
% 2.66/0.71  % (706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.66/0.71  % (706)Termination reason: Refutation not found, incomplete strategy
% 2.66/0.71  
% 2.66/0.71  % (706)Memory used [KB]: 1791
% 2.66/0.71  % (706)Time elapsed: 0.139 s
% 2.66/0.71  % (706)------------------------------
% 2.66/0.71  % (706)------------------------------
% 2.66/0.73  % (709)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 3.21/0.82  % (672)Time limit reached!
% 3.21/0.82  % (672)------------------------------
% 3.21/0.82  % (672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.21/0.82  % (672)Termination reason: Time limit
% 3.21/0.82  
% 3.21/0.82  % (672)Memory used [KB]: 7675
% 3.21/0.82  % (672)Time elapsed: 0.416 s
% 3.21/0.82  % (672)------------------------------
% 3.21/0.82  % (672)------------------------------
% 3.21/0.85  % (711)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 4.14/0.91  % (650)Time limit reached!
% 4.14/0.91  % (650)------------------------------
% 4.14/0.91  % (650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.14/0.91  % (650)Termination reason: Time limit
% 4.14/0.91  
% 4.14/0.91  % (650)Memory used [KB]: 3582
% 4.14/0.91  % (650)Time elapsed: 0.501 s
% 4.14/0.91  % (650)------------------------------
% 4.14/0.91  % (650)------------------------------
% 4.38/0.94  % (680)Time limit reached!
% 4.38/0.94  % (680)------------------------------
% 4.38/0.94  % (680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.38/0.94  % (680)Termination reason: Time limit
% 4.38/0.94  % (680)Termination phase: Saturation
% 4.38/0.94  
% 4.38/0.94  % (680)Memory used [KB]: 8443
% 4.38/0.94  % (680)Time elapsed: 0.500 s
% 4.38/0.94  % (680)------------------------------
% 4.38/0.94  % (680)------------------------------
% 4.38/0.94  % (700)Refutation found. Thanks to Tanya!
% 4.38/0.94  % SZS status Theorem for theBenchmark
% 4.38/0.94  % SZS output start Proof for theBenchmark
% 4.38/0.94  fof(f3232,plain,(
% 4.38/0.94    $false),
% 4.38/0.94    inference(avatar_sat_refutation,[],[f58,f566,f664,f988,f1238,f1253,f1336,f1348,f1370,f1663,f2011,f2356,f2671,f2705,f2711,f2993,f3219])).
% 4.38/0.94  fof(f3219,plain,(
% 4.38/0.94    spl7_44 | ~spl7_2 | ~spl7_26),
% 4.38/0.94    inference(avatar_split_clause,[],[f3199,f984,f125,f1223])).
% 4.38/0.94  fof(f1223,plain,(
% 4.38/0.94    spl7_44 <=> ! [X0] : r2_hidden(X0,k1_xboole_0)),
% 4.38/0.94    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 4.38/0.94  fof(f125,plain,(
% 4.38/0.94    spl7_2 <=> ! [X0] : ~r2_hidden(X0,k1_tarski(X0))),
% 4.38/0.94    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 4.38/0.94  fof(f984,plain,(
% 4.38/0.94    spl7_26 <=> ! [X81,X80] : r2_hidden(X81,k2_relat_1(sK6(X80,X81)))),
% 4.38/0.94    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 4.38/0.94  fof(f3199,plain,(
% 4.38/0.94    ( ! [X81] : (r2_hidden(X81,k1_xboole_0)) ) | (~spl7_2 | ~spl7_26)),
% 4.38/0.94    inference(backward_demodulation,[],[f985,f3172])).
% 4.38/0.94  fof(f3172,plain,(
% 4.38/0.94    ( ! [X37,X36] : (k1_xboole_0 = k2_relat_1(sK6(X36,X37))) ) | (~spl7_2 | ~spl7_26)),
% 4.38/0.94    inference(subsumption_resolution,[],[f3160,f126])).
% 4.38/0.94  fof(f126,plain,(
% 4.38/0.94    ( ! [X0] : (~r2_hidden(X0,k1_tarski(X0))) ) | ~spl7_2),
% 4.38/0.94    inference(avatar_component_clause,[],[f125])).
% 4.38/0.94  fof(f3160,plain,(
% 4.38/0.94    ( ! [X37,X36] : (r2_hidden(X37,k1_tarski(X37)) | k1_xboole_0 = k2_relat_1(sK6(X36,X37))) ) | ~spl7_26),
% 4.38/0.94    inference(superposition,[],[f985,f262])).
% 4.38/0.94  fof(f262,plain,(
% 4.38/0.94    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK6(X0,X1)) | k1_xboole_0 = k2_relat_1(sK6(X0,X1))) )),
% 4.38/0.94    inference(equality_resolution,[],[f198])).
% 4.38/0.94  fof(f198,plain,(
% 4.38/0.94    ( ! [X2,X0,X1] : (X1 != X2 | k1_xboole_0 = k2_relat_1(sK6(X0,X1)) | k2_relat_1(sK6(X0,X1)) = k1_tarski(X2)) )),
% 4.38/0.94    inference(duplicate_literal_removal,[],[f195])).
% 4.38/0.94  fof(f195,plain,(
% 4.38/0.94    ( ! [X2,X0,X1] : (X1 != X2 | k1_xboole_0 = k2_relat_1(sK6(X0,X1)) | k2_relat_1(sK6(X0,X1)) = k1_tarski(X2) | k1_xboole_0 = k2_relat_1(sK6(X0,X1)) | k2_relat_1(sK6(X0,X1)) = k1_tarski(X2)) )),
% 4.38/0.94    inference(superposition,[],[f43,f110])).
% 4.38/0.94  fof(f110,plain,(
% 4.38/0.94    ( ! [X12,X10,X11] : (sK5(k2_relat_1(sK6(X11,X10)),X12) = X10 | k1_xboole_0 = k2_relat_1(sK6(X11,X10)) | k2_relat_1(sK6(X11,X10)) = k1_tarski(X12)) )),
% 4.38/0.94    inference(resolution,[],[f106,f42])).
% 4.38/0.94  fof(f42,plain,(
% 4.38/0.94    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 4.38/0.94    inference(cnf_transformation,[],[f29])).
% 4.38/0.94  fof(f29,plain,(
% 4.38/0.94    ! [X0,X1] : ((sK5(X0,X1) != X1 & r2_hidden(sK5(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 4.38/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f17,f28])).
% 4.38/0.94  fof(f28,plain,(
% 4.38/0.94    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK5(X0,X1) != X1 & r2_hidden(sK5(X0,X1),X0)))),
% 4.38/0.94    introduced(choice_axiom,[])).
% 4.38/0.94  fof(f17,plain,(
% 4.38/0.94    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 4.38/0.94    inference(ennf_transformation,[],[f3])).
% 4.38/0.94  fof(f3,axiom,(
% 4.38/0.94    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 4.38/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).
% 4.38/0.94  fof(f106,plain,(
% 4.38/0.94    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_relat_1(sK6(X0,X1))) | X1 = X2) )),
% 4.38/0.94    inference(subsumption_resolution,[],[f72,f66])).
% 4.38/0.94  fof(f66,plain,(
% 4.38/0.94    ( ! [X2,X0,X1] : (r2_hidden(sK4(sK6(X0,X1),X2),X0) | ~r2_hidden(X2,k2_relat_1(sK6(X0,X1)))) )),
% 4.38/0.94    inference(subsumption_resolution,[],[f65,f45])).
% 4.38/0.94  fof(f45,plain,(
% 4.38/0.94    ( ! [X0,X1] : (v1_relat_1(sK6(X0,X1))) )),
% 4.38/0.94    inference(cnf_transformation,[],[f31])).
% 4.38/0.94  fof(f31,plain,(
% 4.38/0.94    ! [X0,X1] : (! [X3] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK6(X0,X1)) = X0 & v1_funct_1(sK6(X0,X1)) & v1_relat_1(sK6(X0,X1)))),
% 4.38/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f18,f30])).
% 4.38/0.94  fof(f30,plain,(
% 4.38/0.94    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK6(X0,X1)) = X0 & v1_funct_1(sK6(X0,X1)) & v1_relat_1(sK6(X0,X1))))),
% 4.38/0.94    introduced(choice_axiom,[])).
% 4.38/0.94  fof(f18,plain,(
% 4.38/0.94    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 4.38/0.94    inference(ennf_transformation,[],[f5])).
% 4.38/0.94  fof(f5,axiom,(
% 4.38/0.94    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 4.38/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 4.38/0.94  fof(f65,plain,(
% 4.38/0.94    ( ! [X2,X0,X1] : (r2_hidden(sK4(sK6(X0,X1),X2),X0) | ~r2_hidden(X2,k2_relat_1(sK6(X0,X1))) | ~v1_relat_1(sK6(X0,X1))) )),
% 4.38/0.94    inference(subsumption_resolution,[],[f64,f46])).
% 4.38/0.94  fof(f46,plain,(
% 4.38/0.94    ( ! [X0,X1] : (v1_funct_1(sK6(X0,X1))) )),
% 4.38/0.94    inference(cnf_transformation,[],[f31])).
% 4.38/0.94  fof(f64,plain,(
% 4.38/0.94    ( ! [X2,X0,X1] : (r2_hidden(sK4(sK6(X0,X1),X2),X0) | ~r2_hidden(X2,k2_relat_1(sK6(X0,X1))) | ~v1_funct_1(sK6(X0,X1)) | ~v1_relat_1(sK6(X0,X1))) )),
% 4.38/0.94    inference(superposition,[],[f53,f47])).
% 4.38/0.94  fof(f47,plain,(
% 4.38/0.94    ( ! [X0,X1] : (k1_relat_1(sK6(X0,X1)) = X0) )),
% 4.38/0.94    inference(cnf_transformation,[],[f31])).
% 4.38/0.94  fof(f53,plain,(
% 4.38/0.94    ( ! [X0,X5] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.38/0.94    inference(equality_resolution,[],[f36])).
% 4.38/0.94  fof(f36,plain,(
% 4.38/0.94    ( ! [X0,X5,X1] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.38/0.94    inference(cnf_transformation,[],[f27])).
% 4.38/0.94  fof(f27,plain,(
% 4.38/0.94    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & ((sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.38/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f26,f25,f24])).
% 4.38/0.94  fof(f24,plain,(
% 4.38/0.94    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1))))),
% 4.38/0.94    introduced(choice_axiom,[])).
% 4.38/0.94  fof(f25,plain,(
% 4.38/0.94    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))),
% 4.38/0.94    introduced(choice_axiom,[])).
% 4.38/0.94  fof(f26,plain,(
% 4.38/0.94    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))))),
% 4.38/0.94    introduced(choice_axiom,[])).
% 4.38/0.94  fof(f23,plain,(
% 4.38/0.94    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.38/0.94    inference(rectify,[],[f22])).
% 4.38/0.94  fof(f22,plain,(
% 4.38/0.94    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.38/0.94    inference(nnf_transformation,[],[f16])).
% 4.38/0.94  fof(f16,plain,(
% 4.38/0.94    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.38/0.94    inference(flattening,[],[f15])).
% 4.38/0.94  fof(f15,plain,(
% 4.38/0.94    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.38/0.94    inference(ennf_transformation,[],[f4])).
% 4.38/0.94  fof(f4,axiom,(
% 4.38/0.94    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 4.38/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 4.38/0.94  fof(f72,plain,(
% 4.38/0.94    ( ! [X2,X0,X1] : (X1 = X2 | ~r2_hidden(X2,k2_relat_1(sK6(X0,X1))) | ~r2_hidden(sK4(sK6(X0,X1),X2),X0)) )),
% 4.38/0.94    inference(subsumption_resolution,[],[f71,f45])).
% 4.38/0.94  fof(f71,plain,(
% 4.38/0.94    ( ! [X2,X0,X1] : (X1 = X2 | ~r2_hidden(X2,k2_relat_1(sK6(X0,X1))) | ~v1_relat_1(sK6(X0,X1)) | ~r2_hidden(sK4(sK6(X0,X1),X2),X0)) )),
% 4.38/0.94    inference(subsumption_resolution,[],[f67,f46])).
% 4.38/0.94  fof(f67,plain,(
% 4.38/0.94    ( ! [X2,X0,X1] : (X1 = X2 | ~r2_hidden(X2,k2_relat_1(sK6(X0,X1))) | ~v1_funct_1(sK6(X0,X1)) | ~v1_relat_1(sK6(X0,X1)) | ~r2_hidden(sK4(sK6(X0,X1),X2),X0)) )),
% 4.38/0.94    inference(superposition,[],[f52,f48])).
% 4.38/0.94  fof(f48,plain,(
% 4.38/0.94    ( ! [X0,X3,X1] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 4.38/0.94    inference(cnf_transformation,[],[f31])).
% 4.38/0.94  fof(f52,plain,(
% 4.38/0.94    ( ! [X0,X5] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.38/0.94    inference(equality_resolution,[],[f37])).
% 4.38/0.94  fof(f37,plain,(
% 4.38/0.94    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.38/0.94    inference(cnf_transformation,[],[f27])).
% 4.38/0.94  fof(f43,plain,(
% 4.38/0.94    ( ! [X0,X1] : (sK5(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 4.38/0.94    inference(cnf_transformation,[],[f29])).
% 4.38/0.94  fof(f985,plain,(
% 4.38/0.94    ( ! [X80,X81] : (r2_hidden(X81,k2_relat_1(sK6(X80,X81)))) ) | ~spl7_26),
% 4.38/0.94    inference(avatar_component_clause,[],[f984])).
% 4.38/0.94  fof(f2993,plain,(
% 4.38/0.94    spl7_2 | spl7_63 | ~spl7_14 | ~spl7_16 | spl7_21),
% 4.38/0.94    inference(avatar_split_clause,[],[f2992,f661,f630,f563,f2256,f125])).
% 4.38/0.94  fof(f2256,plain,(
% 4.38/0.94    spl7_63 <=> ! [X2] : ~r2_hidden(X2,k1_tarski(sK1))),
% 4.38/0.94    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).
% 4.38/0.94  fof(f563,plain,(
% 4.38/0.94    spl7_14 <=> k1_xboole_0 = k2_relat_1(sK6(sK0,sK1))),
% 4.38/0.94    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 4.38/0.94  fof(f630,plain,(
% 4.38/0.94    spl7_16 <=> r2_hidden(sK1,k1_xboole_0)),
% 4.38/0.94    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 4.38/0.94  fof(f661,plain,(
% 4.38/0.94    spl7_21 <=> k1_xboole_0 = k1_tarski(sK1)),
% 4.38/0.94    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 4.38/0.94  fof(f2992,plain,(
% 4.38/0.94    ( ! [X28,X29] : (~r2_hidden(X29,k1_tarski(sK1)) | ~r2_hidden(X28,k1_tarski(X28))) ) | (~spl7_14 | ~spl7_16 | spl7_21)),
% 4.38/0.94    inference(subsumption_resolution,[],[f2767,f663])).
% 4.38/0.94  fof(f663,plain,(
% 4.38/0.94    k1_xboole_0 != k1_tarski(sK1) | spl7_21),
% 4.38/0.94    inference(avatar_component_clause,[],[f661])).
% 4.38/0.94  fof(f2767,plain,(
% 4.38/0.94    ( ! [X28,X29] : (~r2_hidden(X29,k1_tarski(sK1)) | k1_xboole_0 = k1_tarski(sK1) | ~r2_hidden(X28,k1_tarski(X28))) ) | (~spl7_14 | ~spl7_16)),
% 4.38/0.94    inference(superposition,[],[f1829,f103])).
% 4.38/0.94  fof(f103,plain,(
% 4.38/0.94    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK6(k1_tarski(X0),X1)) | ~r2_hidden(X0,k1_tarski(X0))) )),
% 4.38/0.94    inference(superposition,[],[f81,f48])).
% 4.38/0.94  fof(f81,plain,(
% 4.38/0.94    ( ! [X0,X1] : (k2_relat_1(sK6(k1_tarski(X0),X1)) = k1_tarski(k1_funct_1(sK6(k1_tarski(X0),X1),X0))) )),
% 4.38/0.94    inference(equality_resolution,[],[f77])).
% 4.38/0.94  fof(f77,plain,(
% 4.38/0.94    ( ! [X2,X0,X1] : (k1_tarski(X2) != X0 | k2_relat_1(sK6(X0,X1)) = k1_tarski(k1_funct_1(sK6(X0,X1),X2))) )),
% 4.38/0.94    inference(subsumption_resolution,[],[f76,f45])).
% 4.38/0.94  fof(f76,plain,(
% 4.38/0.94    ( ! [X2,X0,X1] : (k1_tarski(X2) != X0 | k2_relat_1(sK6(X0,X1)) = k1_tarski(k1_funct_1(sK6(X0,X1),X2)) | ~v1_relat_1(sK6(X0,X1))) )),
% 4.38/0.94    inference(subsumption_resolution,[],[f75,f46])).
% 4.38/0.94  fof(f75,plain,(
% 4.38/0.94    ( ! [X2,X0,X1] : (k1_tarski(X2) != X0 | k2_relat_1(sK6(X0,X1)) = k1_tarski(k1_funct_1(sK6(X0,X1),X2)) | ~v1_funct_1(sK6(X0,X1)) | ~v1_relat_1(sK6(X0,X1))) )),
% 4.38/0.94    inference(superposition,[],[f34,f47])).
% 4.38/0.94  fof(f34,plain,(
% 4.38/0.94    ( ! [X0,X1] : (k1_tarski(X0) != k1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 4.38/0.94    inference(cnf_transformation,[],[f12])).
% 4.38/0.94  fof(f12,plain,(
% 4.38/0.94    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 4.38/0.94    inference(flattening,[],[f11])).
% 4.38/0.94  fof(f11,plain,(
% 4.38/0.94    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 4.38/0.94    inference(ennf_transformation,[],[f7])).
% 4.38/0.94  fof(f7,axiom,(
% 4.38/0.94    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 4.38/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 4.38/0.94  fof(f1829,plain,(
% 4.38/0.94    ( ! [X0,X1] : (~r2_hidden(X1,k2_relat_1(sK6(X0,sK1))) | k1_xboole_0 = k2_relat_1(sK6(X0,sK1))) ) | (~spl7_14 | ~spl7_16)),
% 4.38/0.94    inference(subsumption_resolution,[],[f1828,f106])).
% 4.38/0.94  fof(f1828,plain,(
% 4.38/0.94    ( ! [X0,X1] : (sK1 != X1 | k1_xboole_0 = k2_relat_1(sK6(X0,sK1)) | ~r2_hidden(X1,k2_relat_1(sK6(X0,sK1)))) ) | (~spl7_14 | ~spl7_16)),
% 4.38/0.94    inference(subsumption_resolution,[],[f1827,f45])).
% 4.38/0.94  fof(f1827,plain,(
% 4.38/0.94    ( ! [X0,X1] : (sK1 != X1 | k1_xboole_0 = k2_relat_1(sK6(X0,sK1)) | ~v1_relat_1(sK6(X0,sK1)) | ~r2_hidden(X1,k2_relat_1(sK6(X0,sK1)))) ) | (~spl7_14 | ~spl7_16)),
% 4.38/0.94    inference(subsumption_resolution,[],[f1826,f46])).
% 4.38/0.94  fof(f1826,plain,(
% 4.38/0.94    ( ! [X0,X1] : (sK1 != X1 | k1_xboole_0 = k2_relat_1(sK6(X0,sK1)) | ~v1_funct_1(sK6(X0,sK1)) | ~v1_relat_1(sK6(X0,sK1)) | ~r2_hidden(X1,k2_relat_1(sK6(X0,sK1)))) ) | (~spl7_14 | ~spl7_16)),
% 4.38/0.94    inference(subsumption_resolution,[],[f1825,f632])).
% 4.38/0.94  fof(f632,plain,(
% 4.38/0.94    r2_hidden(sK1,k1_xboole_0) | ~spl7_16),
% 4.38/0.94    inference(avatar_component_clause,[],[f630])).
% 4.38/0.94  fof(f1825,plain,(
% 4.38/0.94    ( ! [X0,X1] : (sK1 != X1 | k1_xboole_0 = k2_relat_1(sK6(X0,sK1)) | ~r2_hidden(sK1,k1_xboole_0) | ~v1_funct_1(sK6(X0,sK1)) | ~v1_relat_1(sK6(X0,sK1)) | ~r2_hidden(X1,k2_relat_1(sK6(X0,sK1)))) ) | ~spl7_14),
% 4.38/0.94    inference(duplicate_literal_removal,[],[f1823])).
% 4.38/0.94  fof(f1823,plain,(
% 4.38/0.94    ( ! [X0,X1] : (sK1 != X1 | k1_xboole_0 = k2_relat_1(sK6(X0,sK1)) | ~r2_hidden(sK1,k1_xboole_0) | ~v1_funct_1(sK6(X0,sK1)) | ~v1_relat_1(sK6(X0,sK1)) | ~r2_hidden(X1,k2_relat_1(sK6(X0,sK1))) | k1_xboole_0 = k2_relat_1(sK6(X0,sK1))) ) | ~spl7_14),
% 4.38/0.94    inference(superposition,[],[f100,f619])).
% 4.38/0.94  fof(f619,plain,(
% 4.38/0.94    ( ! [X23] : (sK1 = sK2(sK6(X23,sK1),k1_xboole_0) | k1_xboole_0 = k2_relat_1(sK6(X23,sK1))) ) | ~spl7_14),
% 4.38/0.94    inference(superposition,[],[f327,f565])).
% 4.38/0.94  fof(f565,plain,(
% 4.38/0.94    k1_xboole_0 = k2_relat_1(sK6(sK0,sK1)) | ~spl7_14),
% 4.38/0.94    inference(avatar_component_clause,[],[f563])).
% 4.38/0.94  fof(f327,plain,(
% 4.38/0.94    ( ! [X2,X0,X1] : (sK2(sK6(X0,X1),k2_relat_1(sK6(X2,X1))) = X1 | k2_relat_1(sK6(X0,X1)) = k2_relat_1(sK6(X2,X1))) )),
% 4.38/0.94    inference(equality_resolution,[],[f212])).
% 4.38/0.94  fof(f212,plain,(
% 4.38/0.94    ( ! [X2,X0,X3,X1] : (X1 != X3 | sK2(sK6(X0,X1),k2_relat_1(sK6(X2,X3))) = X1 | k2_relat_1(sK6(X0,X1)) = k2_relat_1(sK6(X2,X3))) )),
% 4.38/0.94    inference(equality_factoring,[],[f162])).
% 4.38/0.94  fof(f162,plain,(
% 4.38/0.94    ( ! [X2,X0,X3,X1] : (sK2(sK6(X0,X1),k2_relat_1(sK6(X2,X3))) = X3 | sK2(sK6(X0,X1),k2_relat_1(sK6(X2,X3))) = X1 | k2_relat_1(sK6(X0,X1)) = k2_relat_1(sK6(X2,X3))) )),
% 4.38/0.94    inference(resolution,[],[f159,f106])).
% 4.38/0.94  fof(f159,plain,(
% 4.38/0.94    ( ! [X2,X0,X1] : (r2_hidden(sK2(sK6(X0,X1),X2),X2) | k2_relat_1(sK6(X0,X1)) = X2 | sK2(sK6(X0,X1),X2) = X1) )),
% 4.38/0.94    inference(subsumption_resolution,[],[f87,f80])).
% 4.38/0.94  fof(f80,plain,(
% 4.38/0.94    ( ! [X2,X0,X1] : (r2_hidden(sK3(sK6(X0,X1),X2),X0) | k2_relat_1(sK6(X0,X1)) = X2 | r2_hidden(sK2(sK6(X0,X1),X2),X2)) )),
% 4.38/0.94    inference(subsumption_resolution,[],[f79,f45])).
% 4.38/0.94  fof(f79,plain,(
% 4.38/0.94    ( ! [X2,X0,X1] : (r2_hidden(sK3(sK6(X0,X1),X2),X0) | k2_relat_1(sK6(X0,X1)) = X2 | r2_hidden(sK2(sK6(X0,X1),X2),X2) | ~v1_relat_1(sK6(X0,X1))) )),
% 4.38/0.94    inference(subsumption_resolution,[],[f78,f46])).
% 4.38/0.94  fof(f78,plain,(
% 4.38/0.94    ( ! [X2,X0,X1] : (r2_hidden(sK3(sK6(X0,X1),X2),X0) | k2_relat_1(sK6(X0,X1)) = X2 | r2_hidden(sK2(sK6(X0,X1),X2),X2) | ~v1_funct_1(sK6(X0,X1)) | ~v1_relat_1(sK6(X0,X1))) )),
% 4.38/0.94    inference(superposition,[],[f39,f47])).
% 4.38/0.94  fof(f39,plain,(
% 4.38/0.94    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | k2_relat_1(X0) = X1 | r2_hidden(sK2(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.38/0.94    inference(cnf_transformation,[],[f27])).
% 4.38/0.94  fof(f87,plain,(
% 4.38/0.94    ( ! [X2,X0,X1] : (sK2(sK6(X0,X1),X2) = X1 | k2_relat_1(sK6(X0,X1)) = X2 | r2_hidden(sK2(sK6(X0,X1),X2),X2) | ~r2_hidden(sK3(sK6(X0,X1),X2),X0)) )),
% 4.38/0.94    inference(subsumption_resolution,[],[f86,f45])).
% 4.38/0.94  fof(f86,plain,(
% 4.38/0.94    ( ! [X2,X0,X1] : (sK2(sK6(X0,X1),X2) = X1 | k2_relat_1(sK6(X0,X1)) = X2 | r2_hidden(sK2(sK6(X0,X1),X2),X2) | ~v1_relat_1(sK6(X0,X1)) | ~r2_hidden(sK3(sK6(X0,X1),X2),X0)) )),
% 4.38/0.94    inference(subsumption_resolution,[],[f82,f46])).
% 4.38/0.94  fof(f82,plain,(
% 4.38/0.94    ( ! [X2,X0,X1] : (sK2(sK6(X0,X1),X2) = X1 | k2_relat_1(sK6(X0,X1)) = X2 | r2_hidden(sK2(sK6(X0,X1),X2),X2) | ~v1_funct_1(sK6(X0,X1)) | ~v1_relat_1(sK6(X0,X1)) | ~r2_hidden(sK3(sK6(X0,X1),X2),X0)) )),
% 4.38/0.94    inference(superposition,[],[f40,f48])).
% 4.38/0.94  fof(f40,plain,(
% 4.38/0.94    ( ! [X0,X1] : (sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) | k2_relat_1(X0) = X1 | r2_hidden(sK2(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.38/0.94    inference(cnf_transformation,[],[f27])).
% 4.38/0.94  fof(f100,plain,(
% 4.38/0.94    ( ! [X6,X4,X5] : (sK2(X4,X6) != X5 | k2_relat_1(X4) = X6 | ~r2_hidden(sK2(X4,X6),X6) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~r2_hidden(X5,k2_relat_1(X4))) )),
% 4.38/0.94    inference(subsumption_resolution,[],[f95,f53])).
% 4.38/0.94  fof(f95,plain,(
% 4.38/0.94    ( ! [X6,X4,X5] : (sK2(X4,X6) != X5 | k2_relat_1(X4) = X6 | ~r2_hidden(sK4(X4,X5),k1_relat_1(X4)) | ~r2_hidden(sK2(X4,X6),X6) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~r2_hidden(X5,k2_relat_1(X4))) )),
% 4.38/0.94    inference(duplicate_literal_removal,[],[f92])).
% 4.38/0.94  fof(f92,plain,(
% 4.38/0.94    ( ! [X6,X4,X5] : (sK2(X4,X6) != X5 | k2_relat_1(X4) = X6 | ~r2_hidden(sK4(X4,X5),k1_relat_1(X4)) | ~r2_hidden(sK2(X4,X6),X6) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~r2_hidden(X5,k2_relat_1(X4)) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) )),
% 4.38/0.94    inference(superposition,[],[f41,f52])).
% 4.38/0.94  fof(f41,plain,(
% 4.38/0.94    ( ! [X0,X3,X1] : (k1_funct_1(X0,X3) != sK2(X0,X1) | k2_relat_1(X0) = X1 | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(sK2(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.38/0.94    inference(cnf_transformation,[],[f27])).
% 4.38/0.94  fof(f2711,plain,(
% 4.38/0.94    k1_xboole_0 != k2_relat_1(sK6(sK0,sK1)) | ~r2_hidden(sK1,k2_relat_1(sK6(sK0,sK1))) | r2_hidden(sK1,k1_xboole_0)),
% 4.38/0.94    introduced(theory_tautology_sat_conflict,[])).
% 4.38/0.94  fof(f2705,plain,(
% 4.38/0.94    ~spl7_15 | spl7_21 | ~spl7_63),
% 4.38/0.94    inference(avatar_contradiction_clause,[],[f2704])).
% 4.38/0.94  fof(f2704,plain,(
% 4.38/0.94    $false | (~spl7_15 | spl7_21 | ~spl7_63)),
% 4.38/0.94    inference(subsumption_resolution,[],[f2697,f2427])).
% 4.38/0.94  fof(f2427,plain,(
% 4.38/0.94    ( ! [X0] : (k1_tarski(X0) != sK0) ) | (spl7_21 | ~spl7_63)),
% 4.38/0.94    inference(superposition,[],[f2423,f47])).
% 4.38/0.94  fof(f2423,plain,(
% 4.38/0.94    ( ! [X45,X46] : (sK0 != k1_relat_1(sK6(k1_tarski(X45),X46))) ) | (spl7_21 | ~spl7_63)),
% 4.38/0.94    inference(subsumption_resolution,[],[f2422,f45])).
% 4.38/0.94  fof(f2422,plain,(
% 4.38/0.94    ( ! [X45,X46] : (sK0 != k1_relat_1(sK6(k1_tarski(X45),X46)) | ~v1_relat_1(sK6(k1_tarski(X45),X46))) ) | (spl7_21 | ~spl7_63)),
% 4.38/0.94    inference(subsumption_resolution,[],[f2402,f46])).
% 4.38/0.94  fof(f2402,plain,(
% 4.38/0.94    ( ! [X45,X46] : (sK0 != k1_relat_1(sK6(k1_tarski(X45),X46)) | ~v1_funct_1(sK6(k1_tarski(X45),X46)) | ~v1_relat_1(sK6(k1_tarski(X45),X46))) ) | (spl7_21 | ~spl7_63)),
% 4.38/0.94    inference(trivial_inequality_removal,[],[f2401])).
% 4.38/0.94  fof(f2401,plain,(
% 4.38/0.94    ( ! [X45,X46] : (k1_tarski(sK1) != k1_tarski(sK1) | sK0 != k1_relat_1(sK6(k1_tarski(X45),X46)) | ~v1_funct_1(sK6(k1_tarski(X45),X46)) | ~v1_relat_1(sK6(k1_tarski(X45),X46))) ) | (spl7_21 | ~spl7_63)),
% 4.38/0.94    inference(superposition,[],[f33,f2292])).
% 4.38/0.94  fof(f2292,plain,(
% 4.38/0.94    ( ! [X0,X1] : (k1_tarski(sK1) = k2_relat_1(sK6(k1_tarski(X0),X1))) ) | (spl7_21 | ~spl7_63)),
% 4.38/0.94    inference(backward_demodulation,[],[f81,f2272])).
% 4.38/0.94  fof(f2272,plain,(
% 4.38/0.94    ( ! [X9] : (k1_tarski(sK1) = k1_tarski(X9)) ) | (spl7_21 | ~spl7_63)),
% 4.38/0.94    inference(subsumption_resolution,[],[f2271,f663])).
% 4.38/0.94  fof(f2271,plain,(
% 4.38/0.94    ( ! [X9] : (k1_xboole_0 = k1_tarski(sK1) | k1_tarski(sK1) = k1_tarski(X9)) ) | ~spl7_63),
% 4.38/0.94    inference(resolution,[],[f2257,f42])).
% 4.38/0.94  fof(f2257,plain,(
% 4.38/0.94    ( ! [X2] : (~r2_hidden(X2,k1_tarski(sK1))) ) | ~spl7_63),
% 4.38/0.94    inference(avatar_component_clause,[],[f2256])).
% 4.38/0.94  fof(f33,plain,(
% 4.38/0.94    ( ! [X2] : (k2_relat_1(X2) != k1_tarski(sK1) | k1_relat_1(X2) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 4.38/0.94    inference(cnf_transformation,[],[f21])).
% 4.38/0.94  fof(f21,plain,(
% 4.38/0.94    ! [X2] : (k2_relat_1(X2) != k1_tarski(sK1) | k1_relat_1(X2) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & k1_xboole_0 != sK0),
% 4.38/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f20,f19])).
% 4.38/0.94  fof(f19,plain,(
% 4.38/0.94    ? [X0] : (? [X1] : ! [X2] : (k1_tarski(X1) != k2_relat_1(X2) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & k1_xboole_0 != X0) => (? [X1] : ! [X2] : (k1_tarski(X1) != k2_relat_1(X2) | k1_relat_1(X2) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & k1_xboole_0 != sK0)),
% 4.38/0.94    introduced(choice_axiom,[])).
% 4.38/0.94  fof(f20,plain,(
% 4.38/0.94    ? [X1] : ! [X2] : (k1_tarski(X1) != k2_relat_1(X2) | k1_relat_1(X2) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) => ! [X2] : (k2_relat_1(X2) != k1_tarski(sK1) | k1_relat_1(X2) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.38/0.94    introduced(choice_axiom,[])).
% 4.38/0.94  fof(f10,plain,(
% 4.38/0.94    ? [X0] : (? [X1] : ! [X2] : (k1_tarski(X1) != k2_relat_1(X2) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & k1_xboole_0 != X0)),
% 4.38/0.94    inference(ennf_transformation,[],[f9])).
% 4.38/0.94  fof(f9,negated_conjecture,(
% 4.38/0.94    ~! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 4.38/0.94    inference(negated_conjecture,[],[f8])).
% 4.38/0.94  fof(f8,conjecture,(
% 4.38/0.94    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 4.38/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 4.38/0.94  fof(f2697,plain,(
% 4.38/0.94    sK0 = k1_tarski(sK1) | (~spl7_15 | spl7_21 | ~spl7_63)),
% 4.38/0.94    inference(resolution,[],[f628,f2416])).
% 4.38/0.94  fof(f2416,plain,(
% 4.38/0.94    ( ! [X39,X41,X40] : (r2_hidden(sK2(sK6(k1_tarski(X39),X40),X41),X41) | k1_tarski(sK1) = X41) ) | (spl7_21 | ~spl7_63)),
% 4.38/0.94    inference(subsumption_resolution,[],[f2415,f45])).
% 4.38/0.94  fof(f2415,plain,(
% 4.38/0.94    ( ! [X39,X41,X40] : (~v1_relat_1(sK6(k1_tarski(X39),X40)) | k1_tarski(sK1) = X41 | r2_hidden(sK2(sK6(k1_tarski(X39),X40),X41),X41)) ) | (spl7_21 | ~spl7_63)),
% 4.38/0.94    inference(subsumption_resolution,[],[f2414,f46])).
% 4.38/0.94  fof(f2414,plain,(
% 4.38/0.94    ( ! [X39,X41,X40] : (~v1_funct_1(sK6(k1_tarski(X39),X40)) | ~v1_relat_1(sK6(k1_tarski(X39),X40)) | k1_tarski(sK1) = X41 | r2_hidden(sK2(sK6(k1_tarski(X39),X40),X41),X41)) ) | (spl7_21 | ~spl7_63)),
% 4.38/0.94    inference(subsumption_resolution,[],[f2399,f2257])).
% 4.38/0.94  fof(f2399,plain,(
% 4.38/0.94    ( ! [X39,X41,X40] : (r2_hidden(sK2(sK6(k1_tarski(X39),X40),X41),k1_tarski(sK1)) | ~v1_funct_1(sK6(k1_tarski(X39),X40)) | ~v1_relat_1(sK6(k1_tarski(X39),X40)) | k1_tarski(sK1) = X41 | r2_hidden(sK2(sK6(k1_tarski(X39),X40),X41),X41)) ) | (spl7_21 | ~spl7_63)),
% 4.38/0.94    inference(superposition,[],[f90,f2292])).
% 4.38/0.94  fof(f90,plain,(
% 4.38/0.94    ( ! [X4,X3] : (r2_hidden(sK2(X3,X4),k2_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | k2_relat_1(X3) = X4 | r2_hidden(sK2(X3,X4),X4)) )),
% 4.38/0.94    inference(subsumption_resolution,[],[f85,f39])).
% 4.38/0.94  fof(f85,plain,(
% 4.38/0.94    ( ! [X4,X3] : (r2_hidden(sK2(X3,X4),k2_relat_1(X3)) | ~r2_hidden(sK3(X3,X4),k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | k2_relat_1(X3) = X4 | r2_hidden(sK2(X3,X4),X4)) )),
% 4.38/0.94    inference(duplicate_literal_removal,[],[f84])).
% 4.38/0.94  fof(f84,plain,(
% 4.38/0.94    ( ! [X4,X3] : (r2_hidden(sK2(X3,X4),k2_relat_1(X3)) | ~r2_hidden(sK3(X3,X4),k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | k2_relat_1(X3) = X4 | r2_hidden(sK2(X3,X4),X4) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 4.38/0.94    inference(superposition,[],[f35,f40])).
% 4.38/0.94  fof(f35,plain,(
% 4.38/0.94    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 4.38/0.94    inference(cnf_transformation,[],[f14])).
% 4.38/0.94  fof(f14,plain,(
% 4.38/0.94    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 4.38/0.94    inference(flattening,[],[f13])).
% 4.38/0.94  fof(f13,plain,(
% 4.38/0.94    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 4.38/0.94    inference(ennf_transformation,[],[f6])).
% 4.38/0.94  fof(f6,axiom,(
% 4.38/0.94    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 4.38/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).
% 4.38/0.94  fof(f628,plain,(
% 4.38/0.94    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl7_15),
% 4.38/0.94    inference(avatar_component_clause,[],[f627])).
% 4.38/0.94  fof(f627,plain,(
% 4.38/0.94    spl7_15 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 4.38/0.94    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 4.38/0.94  fof(f2671,plain,(
% 4.38/0.94    spl7_15 | spl7_44 | ~spl7_62),
% 4.38/0.94    inference(avatar_split_clause,[],[f2654,f2204,f1223,f627])).
% 4.38/0.94  fof(f2204,plain,(
% 4.38/0.94    spl7_62 <=> ! [X25,X28] : (sK0 != X28 | k1_xboole_0 = k2_relat_1(sK6(X28,X25)))),
% 4.38/0.94    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).
% 4.38/0.94  fof(f2654,plain,(
% 4.38/0.94    ( ! [X0,X1] : (r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X1,sK0)) ) | ~spl7_62),
% 4.38/0.94    inference(superposition,[],[f63,f2650])).
% 4.38/0.94  fof(f2650,plain,(
% 4.38/0.94    ( ! [X0] : (k1_xboole_0 = k2_relat_1(sK6(sK0,X0))) ) | ~spl7_62),
% 4.38/0.94    inference(equality_resolution,[],[f2205])).
% 4.38/0.94  fof(f2205,plain,(
% 4.38/0.94    ( ! [X28,X25] : (sK0 != X28 | k1_xboole_0 = k2_relat_1(sK6(X28,X25))) ) | ~spl7_62),
% 4.38/0.94    inference(avatar_component_clause,[],[f2204])).
% 4.38/0.94  fof(f63,plain,(
% 4.38/0.94    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(sK6(X0,X1))) | ~r2_hidden(X2,X0)) )),
% 4.38/0.94    inference(duplicate_literal_removal,[],[f62])).
% 4.38/0.94  fof(f62,plain,(
% 4.38/0.94    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X1,k2_relat_1(sK6(X0,X1))) | ~r2_hidden(X2,X0)) )),
% 4.38/0.94    inference(forward_demodulation,[],[f61,f47])).
% 4.38/0.94  fof(f61,plain,(
% 4.38/0.94    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(sK6(X0,X1))) | ~r2_hidden(X2,k1_relat_1(sK6(X0,X1))) | ~r2_hidden(X2,X0)) )),
% 4.38/0.94    inference(subsumption_resolution,[],[f60,f45])).
% 4.38/0.94  fof(f60,plain,(
% 4.38/0.94    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(sK6(X0,X1))) | ~r2_hidden(X2,k1_relat_1(sK6(X0,X1))) | ~v1_relat_1(sK6(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 4.38/0.94    inference(subsumption_resolution,[],[f59,f46])).
% 4.38/0.94  % (651)Time limit reached!
% 4.38/0.94  % (651)------------------------------
% 4.38/0.94  % (651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.38/0.94  fof(f59,plain,(
% 4.38/0.94    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(sK6(X0,X1))) | ~r2_hidden(X2,k1_relat_1(sK6(X0,X1))) | ~v1_funct_1(sK6(X0,X1)) | ~v1_relat_1(sK6(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 4.38/0.94    inference(superposition,[],[f35,f48])).
% 4.38/0.94  % (651)Termination reason: Time limit
% 4.38/0.94  
% 4.38/0.94  fof(f2356,plain,(
% 4.38/0.94    spl7_62 | spl7_21 | ~spl7_63),
% 4.38/0.94    inference(avatar_split_clause,[],[f2355,f2256,f661,f2204])).
% 4.38/0.94  % (651)Memory used [KB]: 8827
% 4.38/0.94  % (651)Time elapsed: 0.526 s
% 4.38/0.94  % (651)------------------------------
% 4.38/0.94  % (651)------------------------------
% 4.38/0.94  fof(f2355,plain,(
% 4.38/0.94    ( ! [X17,X15] : (sK0 != X17 | k1_xboole_0 = k2_relat_1(sK6(X17,X15))) ) | (spl7_21 | ~spl7_63)),
% 4.38/0.94    inference(subsumption_resolution,[],[f2342,f2295])).
% 4.38/0.94  fof(f2295,plain,(
% 4.38/0.94    ( ! [X0,X1] : (k1_tarski(X0) = k1_tarski(X1)) ) | (spl7_21 | ~spl7_63)),
% 4.38/0.94    inference(superposition,[],[f2272,f2272])).
% 4.38/0.94  fof(f2342,plain,(
% 4.38/0.94    ( ! [X17,X15,X16] : (k1_tarski(sK1) != k1_tarski(X16) | sK0 != X17 | k1_xboole_0 = k2_relat_1(sK6(X17,X15))) ) | (spl7_21 | ~spl7_63)),
% 4.38/0.94    inference(superposition,[],[f539,f2295])).
% 4.38/0.94  fof(f539,plain,(
% 4.38/0.94    ( ! [X0,X1] : (k1_tarski(X1) != k1_tarski(sK1) | sK0 != X0 | k1_xboole_0 = k2_relat_1(sK6(X0,X1))) )),
% 4.38/0.94    inference(superposition,[],[f538,f47])).
% 4.38/0.94  fof(f538,plain,(
% 4.38/0.94    ( ! [X83,X84] : (sK0 != k1_relat_1(sK6(X83,X84)) | k1_tarski(sK1) != k1_tarski(X84) | k1_xboole_0 = k2_relat_1(sK6(X83,X84))) )),
% 4.38/0.94    inference(subsumption_resolution,[],[f537,f45])).
% 4.38/0.94  fof(f537,plain,(
% 4.38/0.94    ( ! [X83,X84] : (k1_tarski(sK1) != k1_tarski(X84) | sK0 != k1_relat_1(sK6(X83,X84)) | ~v1_relat_1(sK6(X83,X84)) | k1_xboole_0 = k2_relat_1(sK6(X83,X84))) )),
% 4.38/0.94    inference(subsumption_resolution,[],[f523,f46])).
% 4.38/0.94  fof(f523,plain,(
% 4.38/0.94    ( ! [X83,X84] : (k1_tarski(sK1) != k1_tarski(X84) | sK0 != k1_relat_1(sK6(X83,X84)) | ~v1_funct_1(sK6(X83,X84)) | ~v1_relat_1(sK6(X83,X84)) | k1_xboole_0 = k2_relat_1(sK6(X83,X84))) )),
% 4.38/0.94    inference(superposition,[],[f33,f262])).
% 4.38/0.94  fof(f2011,plain,(
% 4.38/0.94    spl7_55 | spl7_12 | ~spl7_14),
% 4.38/0.94    inference(avatar_split_clause,[],[f718,f563,f320,f2003])).
% 4.38/0.94  fof(f2003,plain,(
% 4.38/0.94    spl7_55 <=> r2_hidden(sK1,k2_relat_1(sK6(sK0,sK1)))),
% 4.38/0.94    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).
% 4.38/0.94  fof(f320,plain,(
% 4.38/0.94    spl7_12 <=> ! [X1,X0] : (k1_xboole_0 = k2_relat_1(sK6(X0,X1)) | r2_hidden(X1,k2_relat_1(sK6(X0,X1))))),
% 4.38/0.94    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 4.38/0.94  fof(f718,plain,(
% 4.38/0.94    ( ! [X161,X160] : (k1_xboole_0 = k2_relat_1(sK6(X160,X161)) | r2_hidden(X161,k2_relat_1(sK6(X160,X161))) | r2_hidden(sK1,k2_relat_1(sK6(sK0,sK1)))) ) | ~spl7_14),
% 4.38/0.94    inference(superposition,[],[f565,f392])).
% 4.38/0.94  fof(f392,plain,(
% 4.38/0.94    ( ! [X39,X37,X38,X40] : (k2_relat_1(sK6(X39,X40)) = k2_relat_1(sK6(X37,X38)) | r2_hidden(X38,k2_relat_1(sK6(X37,X38))) | r2_hidden(X40,k2_relat_1(sK6(X39,X40)))) )),
% 4.38/0.94    inference(subsumption_resolution,[],[f391,f236])).
% 4.38/0.94  fof(f236,plain,(
% 4.38/0.94    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_relat_1(sK6(X1,X0))) | r2_hidden(X0,k2_relat_1(sK6(X1,X0)))) )),
% 4.38/0.94    inference(resolution,[],[f177,f63])).
% 4.38/0.94  fof(f177,plain,(
% 4.38/0.94    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,k2_relat_1(sK6(k2_relat_1(sK6(X0,X1)),X2))) | r2_hidden(X1,k2_relat_1(sK6(X0,X1)))) )),
% 4.38/0.94    inference(duplicate_literal_removal,[],[f172])).
% 4.38/0.94  fof(f172,plain,(
% 4.38/0.94    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,k2_relat_1(sK6(X0,X1))) | ~r2_hidden(X3,k2_relat_1(sK6(k2_relat_1(sK6(X0,X1)),X2))) | ~r2_hidden(X3,k2_relat_1(sK6(k2_relat_1(sK6(X0,X1)),X2)))) )),
% 4.38/0.94    inference(superposition,[],[f66,f109])).
% 4.38/0.94  fof(f109,plain,(
% 4.38/0.94    ( ! [X6,X8,X7,X9] : (sK4(sK6(k2_relat_1(sK6(X7,X6)),X8),X9) = X6 | ~r2_hidden(X9,k2_relat_1(sK6(k2_relat_1(sK6(X7,X6)),X8)))) )),
% 4.38/0.94    inference(resolution,[],[f106,f66])).
% 4.38/0.94  fof(f391,plain,(
% 4.38/0.94    ( ! [X39,X37,X38,X40] : (r2_hidden(X38,k2_relat_1(sK6(X37,X38))) | k2_relat_1(sK6(X39,X40)) = k2_relat_1(sK6(X37,X38)) | r2_hidden(X38,k2_relat_1(sK6(X39,X40))) | r2_hidden(X40,k2_relat_1(sK6(X39,X40)))) )),
% 4.38/0.94    inference(subsumption_resolution,[],[f390,f45])).
% 4.38/0.94  fof(f390,plain,(
% 4.38/0.94    ( ! [X39,X37,X38,X40] : (r2_hidden(X38,k2_relat_1(sK6(X37,X38))) | ~v1_relat_1(sK6(X37,X38)) | k2_relat_1(sK6(X39,X40)) = k2_relat_1(sK6(X37,X38)) | r2_hidden(X38,k2_relat_1(sK6(X39,X40))) | r2_hidden(X40,k2_relat_1(sK6(X39,X40)))) )),
% 4.38/0.94    inference(subsumption_resolution,[],[f377,f46])).
% 4.38/0.94  fof(f377,plain,(
% 4.38/0.94    ( ! [X39,X37,X38,X40] : (r2_hidden(X38,k2_relat_1(sK6(X37,X38))) | ~v1_funct_1(sK6(X37,X38)) | ~v1_relat_1(sK6(X37,X38)) | k2_relat_1(sK6(X39,X40)) = k2_relat_1(sK6(X37,X38)) | r2_hidden(X38,k2_relat_1(sK6(X39,X40))) | r2_hidden(X40,k2_relat_1(sK6(X39,X40)))) )),
% 4.38/0.94    inference(duplicate_literal_removal,[],[f374])).
% 4.38/0.94  fof(f374,plain,(
% 4.38/0.94    ( ! [X39,X37,X38,X40] : (r2_hidden(X38,k2_relat_1(sK6(X37,X38))) | ~v1_funct_1(sK6(X37,X38)) | ~v1_relat_1(sK6(X37,X38)) | k2_relat_1(sK6(X39,X40)) = k2_relat_1(sK6(X37,X38)) | r2_hidden(X38,k2_relat_1(sK6(X39,X40))) | k2_relat_1(sK6(X39,X40)) = k2_relat_1(sK6(X37,X38)) | r2_hidden(X40,k2_relat_1(sK6(X39,X40)))) )),
% 4.38/0.94    inference(superposition,[],[f90,f363])).
% 4.38/0.94  fof(f363,plain,(
% 4.38/0.94    ( ! [X2,X0,X3,X1] : (sK2(sK6(X0,X1),k2_relat_1(sK6(X2,X3))) = X1 | k2_relat_1(sK6(X0,X1)) = k2_relat_1(sK6(X2,X3)) | r2_hidden(X3,k2_relat_1(sK6(X2,X3)))) )),
% 4.38/0.94    inference(subsumption_resolution,[],[f221,f212])).
% 4.38/0.94  fof(f221,plain,(
% 4.38/0.94    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,k2_relat_1(sK6(X2,X3))) | k2_relat_1(sK6(X0,X1)) = k2_relat_1(sK6(X2,X3)) | X1 = X3 | sK2(sK6(X0,X1),k2_relat_1(sK6(X2,X3))) = X1) )),
% 4.38/0.94    inference(duplicate_literal_removal,[],[f203])).
% 4.38/0.94  fof(f203,plain,(
% 4.38/0.94    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,k2_relat_1(sK6(X2,X3))) | k2_relat_1(sK6(X0,X1)) = k2_relat_1(sK6(X2,X3)) | X1 = X3 | sK2(sK6(X0,X1),k2_relat_1(sK6(X2,X3))) = X1 | k2_relat_1(sK6(X0,X1)) = k2_relat_1(sK6(X2,X3))) )),
% 4.38/0.94    inference(superposition,[],[f159,f162])).
% 4.38/0.94  fof(f1663,plain,(
% 4.38/0.94    ~spl7_14 | spl7_21 | ~spl7_44),
% 4.38/0.94    inference(avatar_contradiction_clause,[],[f1662])).
% 4.38/0.94  fof(f1662,plain,(
% 4.38/0.94    $false | (~spl7_14 | spl7_21 | ~spl7_44)),
% 4.38/0.94    inference(subsumption_resolution,[],[f1603,f1554])).
% 4.38/0.94  fof(f1554,plain,(
% 4.38/0.94    ( ! [X0] : (sK1 = X0) ) | (~spl7_14 | ~spl7_44)),
% 4.38/0.94    inference(resolution,[],[f1224,f606])).
% 4.38/0.94  fof(f606,plain,(
% 4.38/0.94    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0) | sK1 = X1) ) | ~spl7_14),
% 4.38/0.94    inference(superposition,[],[f106,f565])).
% 4.38/0.94  fof(f1224,plain,(
% 4.38/0.94    ( ! [X0] : (r2_hidden(X0,k1_xboole_0)) ) | ~spl7_44),
% 4.38/0.94    inference(avatar_component_clause,[],[f1223])).
% 4.38/0.94  fof(f1603,plain,(
% 4.38/0.94    k1_xboole_0 != sK1 | (~spl7_14 | spl7_21 | ~spl7_44)),
% 4.38/0.94    inference(superposition,[],[f663,f1554])).
% 4.38/0.94  fof(f1370,plain,(
% 4.38/0.94    spl7_22 | spl7_23),
% 4.38/0.94    inference(avatar_split_clause,[],[f1369,f772,f769])).
% 4.38/0.94  fof(f769,plain,(
% 4.38/0.94    spl7_22 <=> ! [X179,X180] : (k1_tarski(sK1) != k2_relat_1(sK6(X179,X180)) | r2_hidden(X180,k2_relat_1(sK6(X179,X180))))),
% 4.38/0.94    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 4.38/0.94  fof(f772,plain,(
% 4.38/0.94    spl7_23 <=> ! [X178,X177] : (sK0 != X177 | r2_hidden(X178,k2_relat_1(sK6(X177,X178))))),
% 4.38/0.94    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 4.38/0.94  fof(f1369,plain,(
% 4.38/0.94    ( ! [X14,X12,X15,X13] : (sK0 != X12 | k1_tarski(sK1) != k2_relat_1(sK6(X14,X15)) | r2_hidden(X15,k2_relat_1(sK6(X14,X15))) | r2_hidden(X13,k2_relat_1(sK6(X12,X13)))) )),
% 4.38/0.94    inference(forward_demodulation,[],[f1368,f47])).
% 4.38/0.94  fof(f1368,plain,(
% 4.38/0.94    ( ! [X14,X12,X15,X13] : (k1_tarski(sK1) != k2_relat_1(sK6(X14,X15)) | sK0 != k1_relat_1(sK6(X12,X13)) | r2_hidden(X15,k2_relat_1(sK6(X14,X15))) | r2_hidden(X13,k2_relat_1(sK6(X12,X13)))) )),
% 4.38/0.94    inference(subsumption_resolution,[],[f1367,f45])).
% 4.38/0.94  fof(f1367,plain,(
% 4.38/0.94    ( ! [X14,X12,X15,X13] : (k1_tarski(sK1) != k2_relat_1(sK6(X14,X15)) | sK0 != k1_relat_1(sK6(X12,X13)) | ~v1_relat_1(sK6(X12,X13)) | r2_hidden(X15,k2_relat_1(sK6(X14,X15))) | r2_hidden(X13,k2_relat_1(sK6(X12,X13)))) )),
% 4.38/0.94    inference(subsumption_resolution,[],[f1356,f46])).
% 4.38/0.94  fof(f1356,plain,(
% 4.38/0.94    ( ! [X14,X12,X15,X13] : (k1_tarski(sK1) != k2_relat_1(sK6(X14,X15)) | sK0 != k1_relat_1(sK6(X12,X13)) | ~v1_funct_1(sK6(X12,X13)) | ~v1_relat_1(sK6(X12,X13)) | r2_hidden(X15,k2_relat_1(sK6(X14,X15))) | r2_hidden(X13,k2_relat_1(sK6(X12,X13)))) )),
% 4.38/0.94    inference(superposition,[],[f33,f392])).
% 4.38/0.94  fof(f1348,plain,(
% 4.38/0.94    spl7_15 | spl7_16 | ~spl7_14),
% 4.38/0.94    inference(avatar_split_clause,[],[f1123,f563,f630,f627])).
% 4.38/0.94  fof(f1123,plain,(
% 4.38/0.94    ( ! [X0] : (r2_hidden(sK1,k1_xboole_0) | ~r2_hidden(X0,sK0)) ) | ~spl7_14),
% 4.38/0.94    inference(superposition,[],[f63,f565])).
% 4.38/0.94  fof(f1336,plain,(
% 4.38/0.94    spl7_1 | ~spl7_12 | ~spl7_15),
% 4.38/0.94    inference(avatar_contradiction_clause,[],[f1335])).
% 4.38/0.94  fof(f1335,plain,(
% 4.38/0.94    $false | (spl7_1 | ~spl7_12 | ~spl7_15)),
% 4.38/0.94    inference(subsumption_resolution,[],[f1334,f57])).
% 4.38/0.94  fof(f57,plain,(
% 4.38/0.94    k1_xboole_0 != sK0 | spl7_1),
% 4.38/0.94    inference(avatar_component_clause,[],[f55])).
% 4.38/0.94  fof(f55,plain,(
% 4.38/0.94    spl7_1 <=> k1_xboole_0 = sK0),
% 4.38/0.94    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 4.38/0.94  fof(f1334,plain,(
% 4.38/0.94    k1_xboole_0 = sK0 | (spl7_1 | ~spl7_12 | ~spl7_15)),
% 4.38/0.94    inference(subsumption_resolution,[],[f1307,f628])).
% 4.38/0.94  fof(f1307,plain,(
% 4.38/0.94    ( ! [X37] : (r2_hidden(X37,sK0) | k1_xboole_0 = sK0) ) | (spl7_1 | ~spl7_12 | ~spl7_15)),
% 4.38/0.94    inference(superposition,[],[f321,f1283])).
% 4.38/0.94  fof(f1283,plain,(
% 4.38/0.94    ( ! [X1] : (sK0 = k2_relat_1(sK6(sK0,X1))) ) | (spl7_1 | ~spl7_15)),
% 4.38/0.94    inference(forward_demodulation,[],[f1268,f1244])).
% 4.38/0.94  fof(f1244,plain,(
% 4.38/0.94    ( ! [X9] : (sK0 = k1_tarski(X9)) ) | (spl7_1 | ~spl7_15)),
% 4.38/0.94    inference(subsumption_resolution,[],[f1243,f57])).
% 4.38/0.94  fof(f1243,plain,(
% 4.38/0.94    ( ! [X9] : (k1_xboole_0 = sK0 | sK0 = k1_tarski(X9)) ) | ~spl7_15),
% 4.38/0.94    inference(resolution,[],[f628,f42])).
% 4.38/0.94  fof(f1268,plain,(
% 4.38/0.94    ( ! [X0,X1] : (k2_relat_1(sK6(sK0,X1)) = k1_tarski(k1_funct_1(sK6(sK0,X1),X0))) ) | (spl7_1 | ~spl7_15)),
% 4.38/0.94    inference(backward_demodulation,[],[f81,f1244])).
% 4.38/0.94  fof(f321,plain,(
% 4.38/0.94    ( ! [X0,X1] : (r2_hidden(X1,k2_relat_1(sK6(X0,X1))) | k1_xboole_0 = k2_relat_1(sK6(X0,X1))) ) | ~spl7_12),
% 4.38/0.94    inference(avatar_component_clause,[],[f320])).
% 4.38/0.94  fof(f1253,plain,(
% 4.38/0.94    ~spl7_16 | ~spl7_18),
% 4.38/0.94    inference(avatar_contradiction_clause,[],[f1245])).
% 4.38/0.94  fof(f1245,plain,(
% 4.38/0.94    $false | (~spl7_16 | ~spl7_18)),
% 4.38/0.94    inference(unit_resulting_resolution,[],[f632,f640])).
% 4.38/0.94  fof(f640,plain,(
% 4.38/0.94    ( ! [X19] : (~r2_hidden(X19,k1_xboole_0)) ) | ~spl7_18),
% 4.38/0.94    inference(avatar_component_clause,[],[f639])).
% 4.38/0.94  fof(f639,plain,(
% 4.38/0.94    spl7_18 <=> ! [X19] : ~r2_hidden(X19,k1_xboole_0)),
% 4.38/0.94    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 4.38/0.94  fof(f1238,plain,(
% 4.38/0.94    spl7_44 | ~spl7_2 | ~spl7_23),
% 4.38/0.94    inference(avatar_split_clause,[],[f1188,f772,f125,f1223])).
% 4.38/0.94  fof(f1188,plain,(
% 4.38/0.94    ( ! [X0] : (r2_hidden(X0,k1_xboole_0)) ) | (~spl7_2 | ~spl7_23)),
% 4.38/0.94    inference(backward_demodulation,[],[f1162,f1171])).
% 4.38/0.94  fof(f1171,plain,(
% 4.38/0.94    ( ! [X12] : (k1_xboole_0 = k2_relat_1(sK6(sK0,X12))) ) | (~spl7_2 | ~spl7_23)),
% 4.38/0.94    inference(subsumption_resolution,[],[f1169,f126])).
% 4.38/0.94  fof(f1169,plain,(
% 4.38/0.94    ( ! [X12] : (r2_hidden(X12,k1_tarski(X12)) | k1_xboole_0 = k2_relat_1(sK6(sK0,X12))) ) | ~spl7_23),
% 4.38/0.94    inference(superposition,[],[f1162,f262])).
% 4.38/0.94  fof(f1162,plain,(
% 4.38/0.94    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK6(sK0,X0)))) ) | ~spl7_23),
% 4.38/0.94    inference(equality_resolution,[],[f773])).
% 4.38/0.94  fof(f773,plain,(
% 4.38/0.94    ( ! [X177,X178] : (sK0 != X177 | r2_hidden(X178,k2_relat_1(sK6(X177,X178)))) ) | ~spl7_23),
% 4.38/0.94    inference(avatar_component_clause,[],[f772])).
% 4.38/0.94  fof(f988,plain,(
% 4.38/0.94    spl7_26 | spl7_18 | ~spl7_2 | ~spl7_22),
% 4.38/0.94    inference(avatar_split_clause,[],[f969,f769,f125,f639,f984])).
% 4.38/0.94  fof(f969,plain,(
% 4.38/0.94    ( ! [X90,X88,X87] : (~r2_hidden(X90,k1_xboole_0) | r2_hidden(X88,k2_relat_1(sK6(X87,X88)))) ) | (~spl7_2 | ~spl7_22)),
% 4.38/0.94    inference(superposition,[],[f242,f930])).
% 4.38/0.94  fof(f930,plain,(
% 4.38/0.94    ( ! [X0] : (k1_xboole_0 = k2_relat_1(sK6(X0,sK1))) ) | (~spl7_2 | ~spl7_22)),
% 4.38/0.94    inference(equality_resolution,[],[f927])).
% 4.38/0.94  fof(f927,plain,(
% 4.38/0.94    ( ! [X17,X16] : (k1_tarski(sK1) != k1_tarski(X17) | k1_xboole_0 = k2_relat_1(sK6(X16,X17))) ) | (~spl7_2 | ~spl7_22)),
% 4.38/0.94    inference(subsumption_resolution,[],[f925,f126])).
% 4.38/0.94  fof(f925,plain,(
% 4.38/0.94    ( ! [X17,X16] : (k1_tarski(sK1) != k1_tarski(X17) | r2_hidden(X17,k1_tarski(X17)) | k1_xboole_0 = k2_relat_1(sK6(X16,X17))) ) | ~spl7_22),
% 4.38/0.94    inference(superposition,[],[f770,f262])).
% 4.38/0.94  fof(f770,plain,(
% 4.38/0.94    ( ! [X180,X179] : (k1_tarski(sK1) != k2_relat_1(sK6(X179,X180)) | r2_hidden(X180,k2_relat_1(sK6(X179,X180)))) ) | ~spl7_22),
% 4.38/0.94    inference(avatar_component_clause,[],[f769])).
% 4.38/0.94  fof(f242,plain,(
% 4.38/0.94    ( ! [X30,X28,X31,X29,X27] : (~r2_hidden(X29,k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(X28,X27)),X30)),X31))) | r2_hidden(X27,k2_relat_1(sK6(X28,X27)))) )),
% 4.38/0.94    inference(resolution,[],[f177,f66])).
% 4.38/0.94  fof(f664,plain,(
% 4.38/0.94    ~spl7_21 | ~spl7_14),
% 4.38/0.94    inference(avatar_split_clause,[],[f659,f563,f661])).
% 4.38/0.94  fof(f659,plain,(
% 4.38/0.94    k1_xboole_0 != k1_tarski(sK1) | ~spl7_14),
% 4.38/0.94    inference(subsumption_resolution,[],[f658,f45])).
% 4.38/0.94  fof(f658,plain,(
% 4.38/0.94    k1_xboole_0 != k1_tarski(sK1) | ~v1_relat_1(sK6(sK0,sK1)) | ~spl7_14),
% 4.38/0.94    inference(subsumption_resolution,[],[f657,f46])).
% 4.38/0.94  fof(f657,plain,(
% 4.38/0.94    k1_xboole_0 != k1_tarski(sK1) | ~v1_funct_1(sK6(sK0,sK1)) | ~v1_relat_1(sK6(sK0,sK1)) | ~spl7_14),
% 4.38/0.94    inference(subsumption_resolution,[],[f625,f47])).
% 4.38/0.94  fof(f625,plain,(
% 4.38/0.94    k1_xboole_0 != k1_tarski(sK1) | sK0 != k1_relat_1(sK6(sK0,sK1)) | ~v1_funct_1(sK6(sK0,sK1)) | ~v1_relat_1(sK6(sK0,sK1)) | ~spl7_14),
% 4.38/0.94    inference(superposition,[],[f33,f565])).
% 4.38/0.94  fof(f566,plain,(
% 4.38/0.94    spl7_14),
% 4.38/0.94    inference(avatar_split_clause,[],[f561,f563])).
% 4.38/0.94  fof(f561,plain,(
% 4.38/0.94    k1_xboole_0 = k2_relat_1(sK6(sK0,sK1))),
% 4.38/0.94    inference(equality_resolution,[],[f560])).
% 4.38/0.94  fof(f560,plain,(
% 4.38/0.94    ( ! [X0] : (sK0 != X0 | k1_xboole_0 = k2_relat_1(sK6(X0,sK1))) )),
% 4.38/0.94    inference(equality_resolution,[],[f539])).
% 4.38/0.94  fof(f58,plain,(
% 4.38/0.94    ~spl7_1),
% 4.38/0.94    inference(avatar_split_clause,[],[f32,f55])).
% 4.38/0.94  fof(f32,plain,(
% 4.38/0.94    k1_xboole_0 != sK0),
% 4.38/0.94    inference(cnf_transformation,[],[f21])).
% 4.38/0.94  % SZS output end Proof for theBenchmark
% 4.38/0.94  % (700)------------------------------
% 4.38/0.94  % (700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.38/0.94  % (700)Termination reason: Refutation
% 4.38/0.94  
% 4.38/0.94  % (700)Memory used [KB]: 8059
% 4.38/0.94  % (700)Time elapsed: 0.375 s
% 4.38/0.94  % (700)------------------------------
% 4.38/0.94  % (700)------------------------------
% 4.38/0.94  % (649)Success in time 0.57 s
%------------------------------------------------------------------------------
