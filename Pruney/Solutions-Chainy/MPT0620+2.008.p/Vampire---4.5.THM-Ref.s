%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:54 EST 2020

% Result     : Theorem 3.72s
% Output     : Refutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :  234 (2463 expanded)
%              Number of leaves         :   29 ( 843 expanded)
%              Depth                    :   26
%              Number of atoms          :  917 (14357 expanded)
%              Number of equality atoms :  296 (5398 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4245,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f564,f966,f995,f1333,f1356,f1367,f2285,f2588,f2610,f2804,f2850,f3507,f4118,f4204,f4221,f4232,f4243,f4244])).

fof(f4244,plain,
    ( spl7_13
    | spl7_21
    | ~ spl7_92 ),
    inference(avatar_split_clause,[],[f4242,f4200,f659,f315])).

fof(f315,plain,
    ( spl7_13
  <=> ! [X2] : k1_xboole_0 != k1_tarski(X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f659,plain,
    ( spl7_21
  <=> k1_xboole_0 = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f4200,plain,
    ( spl7_92
  <=> ! [X9] : k1_tarski(sK1) = k1_tarski(X9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).

fof(f4242,plain,
    ( ! [X2] : k1_xboole_0 != k1_tarski(X2)
    | spl7_21
    | ~ spl7_92 ),
    inference(superposition,[],[f661,f4201])).

fof(f4201,plain,
    ( ! [X9] : k1_tarski(sK1) = k1_tarski(X9)
    | ~ spl7_92 ),
    inference(avatar_component_clause,[],[f4200])).

fof(f661,plain,
    ( k1_xboole_0 != k1_tarski(sK1)
    | spl7_21 ),
    inference(avatar_component_clause,[],[f659])).

fof(f4243,plain,
    ( spl7_10
    | ~ spl7_72
    | ~ spl7_92 ),
    inference(avatar_split_clause,[],[f4241,f4200,f3070,f294])).

fof(f294,plain,
    ( spl7_10
  <=> ! [X51,X52] : ~ r2_hidden(X52,k1_tarski(X51)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f3070,plain,
    ( spl7_72
  <=> ! [X22] : ~ r2_hidden(X22,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).

fof(f4241,plain,
    ( ! [X0,X1] : ~ r2_hidden(X1,k1_tarski(X0))
    | ~ spl7_72
    | ~ spl7_92 ),
    inference(superposition,[],[f3071,f4201])).

fof(f3071,plain,
    ( ! [X22] : ~ r2_hidden(X22,k1_tarski(sK1))
    | ~ spl7_72 ),
    inference(avatar_component_clause,[],[f3070])).

fof(f4232,plain,
    ( spl7_92
    | spl7_21
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f4231,f3070,f659,f4200])).

fof(f4231,plain,
    ( ! [X9] : k1_tarski(sK1) = k1_tarski(X9)
    | spl7_21
    | ~ spl7_72 ),
    inference(subsumption_resolution,[],[f4230,f661])).

fof(f4230,plain,
    ( ! [X9] :
        ( k1_xboole_0 = k1_tarski(sK1)
        | k1_tarski(sK1) = k1_tarski(X9) )
    | ~ spl7_72 ),
    inference(resolution,[],[f3071,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( sK5(X0,X1) != X1
        & r2_hidden(sK5(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f14,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK5(X0,X1) != X1
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f4221,plain,
    ( ~ spl7_21
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f4220,f561,f659])).

fof(f561,plain,
    ( spl7_14
  <=> k1_xboole_0 = k2_relat_1(sK6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f4220,plain,
    ( k1_xboole_0 != k1_tarski(sK1)
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f4219,f41])).

fof(f41,plain,(
    ! [X0,X1] : v1_relat_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK6(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK6(X0,X1)) = X0
      & v1_funct_1(sK6(X0,X1))
      & v1_relat_1(sK6(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f15,f27])).

fof(f27,plain,(
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

fof(f15,plain,(
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

fof(f4219,plain,
    ( k1_xboole_0 != k1_tarski(sK1)
    | ~ v1_relat_1(sK6(sK0,sK1))
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f4218,f42])).

fof(f42,plain,(
    ! [X0,X1] : v1_funct_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f4218,plain,
    ( k1_xboole_0 != k1_tarski(sK1)
    | ~ v1_funct_1(sK6(sK0,sK1))
    | ~ v1_relat_1(sK6(sK0,sK1))
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f2679,f43])).

fof(f43,plain,(
    ! [X0,X1] : k1_relat_1(sK6(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f28])).

fof(f2679,plain,
    ( k1_xboole_0 != k1_tarski(sK1)
    | sK0 != k1_relat_1(sK6(sK0,sK1))
    | ~ v1_funct_1(sK6(sK0,sK1))
    | ~ v1_relat_1(sK6(sK0,sK1))
    | ~ spl7_14 ),
    inference(superposition,[],[f30,f563])).

fof(f563,plain,
    ( k1_xboole_0 = k2_relat_1(sK6(sK0,sK1))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f561])).

fof(f30,plain,(
    ! [X2] :
      ( k2_relat_1(X2) != k1_tarski(sK1)
      | k1_relat_1(X2) != sK0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ! [X2] :
        ( k2_relat_1(X2) != k1_tarski(sK1)
        | k1_relat_1(X2) != sK0
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f17,f16])).

fof(f16,plain,
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

fof(f17,plain,
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

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
        ! [X2] :
          ( k1_tarski(X1) != k2_relat_1(X2)
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
            ( k1_tarski(X1) = k2_relat_1(X2)
            & k1_relat_1(X2) = X0
            & v1_funct_1(X2)
            & v1_relat_1(X2) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(f4204,plain,
    ( spl7_2
    | spl7_21
    | spl7_72
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f3050,f628,f561,f3070,f659,f124])).

fof(f124,plain,
    ( spl7_2
  <=> ! [X0] : ~ r2_hidden(X0,k1_tarski(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f628,plain,
    ( spl7_16
  <=> r2_hidden(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f3050,plain,
    ( ! [X21,X22] :
        ( ~ r2_hidden(X22,k1_tarski(sK1))
        | k1_xboole_0 = k1_tarski(sK1)
        | ~ r2_hidden(X21,k1_tarski(X21)) )
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(superposition,[],[f1548,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK6(k1_tarski(X0),X1))
      | ~ r2_hidden(X0,k1_tarski(X0)) ) ),
    inference(superposition,[],[f106,f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK6(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f106,plain,(
    ! [X0,X1] : k2_relat_1(sK6(k1_tarski(X0),X1)) = k1_tarski(k1_funct_1(sK6(k1_tarski(X0),X1),X0)) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X2) != X0
      | k2_relat_1(sK6(X0,X1)) = k1_tarski(k1_funct_1(sK6(X0,X1),X2)) ) ),
    inference(subsumption_resolution,[],[f74,f41])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X2) != X0
      | k2_relat_1(sK6(X0,X1)) = k1_tarski(k1_funct_1(sK6(X0,X1),X2))
      | ~ v1_relat_1(sK6(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f73,f42])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X2) != X0
      | k2_relat_1(sK6(X0,X1)) = k1_tarski(k1_funct_1(sK6(X0,X1),X2))
      | ~ v1_funct_1(sK6(X0,X1))
      | ~ v1_relat_1(sK6(X0,X1)) ) ),
    inference(superposition,[],[f31,f43])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k1_relat_1(X1)
      | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f1548,plain,
    ( ! [X12,X13] :
        ( ~ r2_hidden(X13,k2_relat_1(sK6(X12,sK1)))
        | k1_xboole_0 = k2_relat_1(sK6(X12,sK1)) )
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f1547,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_relat_1(sK6(X0,X1)))
      | X1 = X2 ) ),
    inference(subsumption_resolution,[],[f68,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(sK6(X0,X1),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(sK6(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f61,f41])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(sK6(X0,X1),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(sK6(X0,X1)))
      | ~ v1_relat_1(sK6(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f60,f42])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(sK6(X0,X1),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(sK6(X0,X1)))
      | ~ v1_funct_1(sK6(X0,X1))
      | ~ v1_relat_1(sK6(X0,X1)) ) ),
    inference(superposition,[],[f49,f43])).

fof(f49,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f23,f22,f21])).

fof(f21,plain,(
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

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK2(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(X2,k2_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(sK4(sK6(X0,X1),X2),X0) ) ),
    inference(subsumption_resolution,[],[f67,f41])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(X2,k2_relat_1(sK6(X0,X1)))
      | ~ v1_relat_1(sK6(X0,X1))
      | ~ r2_hidden(sK4(sK6(X0,X1),X2),X0) ) ),
    inference(subsumption_resolution,[],[f63,f42])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(X2,k2_relat_1(sK6(X0,X1)))
      | ~ v1_funct_1(sK6(X0,X1))
      | ~ v1_relat_1(sK6(X0,X1))
      | ~ r2_hidden(sK4(sK6(X0,X1),X2),X0) ) ),
    inference(superposition,[],[f48,f44])).

fof(f48,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1547,plain,
    ( ! [X12,X13] :
        ( sK1 != X13
        | k1_xboole_0 = k2_relat_1(sK6(X12,sK1))
        | ~ r2_hidden(X13,k2_relat_1(sK6(X12,sK1))) )
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f1546,f41])).

fof(f1546,plain,
    ( ! [X12,X13] :
        ( sK1 != X13
        | k1_xboole_0 = k2_relat_1(sK6(X12,sK1))
        | ~ v1_relat_1(sK6(X12,sK1))
        | ~ r2_hidden(X13,k2_relat_1(sK6(X12,sK1))) )
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f1545,f42])).

fof(f1545,plain,
    ( ! [X12,X13] :
        ( sK1 != X13
        | k1_xboole_0 = k2_relat_1(sK6(X12,sK1))
        | ~ v1_funct_1(sK6(X12,sK1))
        | ~ v1_relat_1(sK6(X12,sK1))
        | ~ r2_hidden(X13,k2_relat_1(sK6(X12,sK1))) )
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f1533,f630])).

fof(f630,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f628])).

fof(f1533,plain,
    ( ! [X12,X13] :
        ( sK1 != X13
        | k1_xboole_0 = k2_relat_1(sK6(X12,sK1))
        | ~ r2_hidden(sK1,k1_xboole_0)
        | ~ v1_funct_1(sK6(X12,sK1))
        | ~ v1_relat_1(sK6(X12,sK1))
        | ~ r2_hidden(X13,k2_relat_1(sK6(X12,sK1))) )
    | ~ spl7_14 ),
    inference(duplicate_literal_removal,[],[f1528])).

fof(f1528,plain,
    ( ! [X12,X13] :
        ( sK1 != X13
        | k1_xboole_0 = k2_relat_1(sK6(X12,sK1))
        | ~ r2_hidden(sK1,k1_xboole_0)
        | ~ v1_funct_1(sK6(X12,sK1))
        | ~ v1_relat_1(sK6(X12,sK1))
        | ~ r2_hidden(X13,k2_relat_1(sK6(X12,sK1)))
        | k1_xboole_0 = k2_relat_1(sK6(X12,sK1)) )
    | ~ spl7_14 ),
    inference(superposition,[],[f104,f617])).

fof(f617,plain,
    ( ! [X23] :
        ( sK1 = sK2(sK6(X23,sK1),k1_xboole_0)
        | k1_xboole_0 = k2_relat_1(sK6(X23,sK1)) )
    | ~ spl7_14 ),
    inference(superposition,[],[f319,f563])).

fof(f319,plain,(
    ! [X2,X0,X1] :
      ( sK2(sK6(X0,X1),k2_relat_1(sK6(X2,X1))) = X1
      | k2_relat_1(sK6(X0,X1)) = k2_relat_1(sK6(X2,X1)) ) ),
    inference(equality_resolution,[],[f205])).

fof(f205,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | sK2(sK6(X0,X1),k2_relat_1(sK6(X2,X3))) = X1
      | k2_relat_1(sK6(X0,X1)) = k2_relat_1(sK6(X2,X3)) ) ),
    inference(equality_factoring,[],[f156])).

fof(f156,plain,(
    ! [X2,X0,X3,X1] :
      ( sK2(sK6(X0,X1),k2_relat_1(sK6(X2,X3))) = X3
      | sK2(sK6(X0,X1),k2_relat_1(sK6(X2,X3))) = X1
      | k2_relat_1(sK6(X0,X1)) = k2_relat_1(sK6(X2,X3)) ) ),
    inference(resolution,[],[f155,f69])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(sK6(X0,X1),X2),X2)
      | k2_relat_1(sK6(X0,X1)) = X2
      | sK2(sK6(X0,X1),X2) = X1 ) ),
    inference(subsumption_resolution,[],[f91,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(sK6(X0,X1),X2),X0)
      | k2_relat_1(sK6(X0,X1)) = X2
      | r2_hidden(sK2(sK6(X0,X1),X2),X2) ) ),
    inference(subsumption_resolution,[],[f84,f41])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(sK6(X0,X1),X2),X0)
      | k2_relat_1(sK6(X0,X1)) = X2
      | r2_hidden(sK2(sK6(X0,X1),X2),X2)
      | ~ v1_relat_1(sK6(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f83,f42])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(sK6(X0,X1),X2),X0)
      | k2_relat_1(sK6(X0,X1)) = X2
      | r2_hidden(sK2(sK6(X0,X1),X2),X2)
      | ~ v1_funct_1(sK6(X0,X1))
      | ~ v1_relat_1(sK6(X0,X1)) ) ),
    inference(superposition,[],[f35,f43])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | k2_relat_1(X0) = X1
      | r2_hidden(sK2(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( sK2(sK6(X0,X1),X2) = X1
      | k2_relat_1(sK6(X0,X1)) = X2
      | r2_hidden(sK2(sK6(X0,X1),X2),X2)
      | ~ r2_hidden(sK3(sK6(X0,X1),X2),X0) ) ),
    inference(subsumption_resolution,[],[f90,f41])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( sK2(sK6(X0,X1),X2) = X1
      | k2_relat_1(sK6(X0,X1)) = X2
      | r2_hidden(sK2(sK6(X0,X1),X2),X2)
      | ~ v1_relat_1(sK6(X0,X1))
      | ~ r2_hidden(sK3(sK6(X0,X1),X2),X0) ) ),
    inference(subsumption_resolution,[],[f86,f42])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( sK2(sK6(X0,X1),X2) = X1
      | k2_relat_1(sK6(X0,X1)) = X2
      | r2_hidden(sK2(sK6(X0,X1),X2),X2)
      | ~ v1_funct_1(sK6(X0,X1))
      | ~ v1_relat_1(sK6(X0,X1))
      | ~ r2_hidden(sK3(sK6(X0,X1),X2),X0) ) ),
    inference(superposition,[],[f36,f44])).

fof(f36,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
      | k2_relat_1(X0) = X1
      | r2_hidden(sK2(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f104,plain,(
    ! [X6,X4,X5] :
      ( sK2(X4,X6) != X5
      | k2_relat_1(X4) = X6
      | ~ r2_hidden(sK2(X4,X6),X6)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ r2_hidden(X5,k2_relat_1(X4)) ) ),
    inference(subsumption_resolution,[],[f99,f49])).

fof(f99,plain,(
    ! [X6,X4,X5] :
      ( sK2(X4,X6) != X5
      | k2_relat_1(X4) = X6
      | ~ r2_hidden(sK4(X4,X5),k1_relat_1(X4))
      | ~ r2_hidden(sK2(X4,X6),X6)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ r2_hidden(X5,k2_relat_1(X4)) ) ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,(
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
    inference(superposition,[],[f37,f48])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X0,X3) != sK2(X0,X1)
      | k2_relat_1(X0) = X1
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(sK2(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4118,plain,
    ( spl7_66
    | ~ spl7_10
    | ~ spl7_13
    | ~ spl7_23
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f4117,f3070,f770,f315,f294,f2526])).

fof(f2526,plain,
    ( spl7_66
  <=> ! [X0] : r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f770,plain,
    ( spl7_23
  <=> ! [X178,X177] :
        ( sK0 != X177
        | r2_hidden(X178,k2_relat_1(sK6(X177,X178))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f4117,plain,
    ( ! [X41] : r2_hidden(X41,k1_xboole_0)
    | ~ spl7_10
    | ~ spl7_13
    | ~ spl7_23
    | ~ spl7_72 ),
    inference(subsumption_resolution,[],[f4104,f316])).

fof(f316,plain,
    ( ! [X2] : k1_xboole_0 != k1_tarski(X2)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f315])).

fof(f4104,plain,
    ( ! [X41] :
        ( k1_xboole_0 = k1_tarski(sK1)
        | r2_hidden(X41,k1_xboole_0) )
    | ~ spl7_10
    | ~ spl7_13
    | ~ spl7_23
    | ~ spl7_72 ),
    inference(superposition,[],[f3629,f4075])).

fof(f4075,plain,
    ( ! [X61] : k1_xboole_0 = k2_relat_1(sK6(sK0,X61))
    | ~ spl7_10
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f4061,f295])).

fof(f295,plain,
    ( ! [X52,X51] : ~ r2_hidden(X52,k1_tarski(X51))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f294])).

fof(f4061,plain,
    ( ! [X61] :
        ( r2_hidden(X61,k1_tarski(X61))
        | k1_xboole_0 = k2_relat_1(sK6(sK0,X61)) )
    | ~ spl7_23 ),
    inference(superposition,[],[f3508,f255])).

fof(f255,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK6(X0,X1))
      | k1_xboole_0 = k2_relat_1(sK6(X0,X1)) ) ),
    inference(equality_resolution,[],[f186])).

fof(f186,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | k1_xboole_0 = k2_relat_1(sK6(X0,X1))
      | k2_relat_1(sK6(X0,X1)) = k1_tarski(X2) ) ),
    inference(duplicate_literal_removal,[],[f183])).

fof(f183,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | k1_xboole_0 = k2_relat_1(sK6(X0,X1))
      | k2_relat_1(sK6(X0,X1)) = k1_tarski(X2)
      | k1_xboole_0 = k2_relat_1(sK6(X0,X1))
      | k2_relat_1(sK6(X0,X1)) = k1_tarski(X2) ) ),
    inference(superposition,[],[f39,f79])).

fof(f79,plain,(
    ! [X12,X10,X11] :
      ( sK5(k2_relat_1(sK6(X11,X10)),X12) = X10
      | k1_xboole_0 = k2_relat_1(sK6(X11,X10))
      | k2_relat_1(sK6(X11,X10)) = k1_tarski(X12) ) ),
    inference(resolution,[],[f69,f38])).

fof(f39,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3508,plain,
    ( ! [X0] : r2_hidden(X0,k2_relat_1(sK6(sK0,X0)))
    | ~ spl7_23 ),
    inference(equality_resolution,[],[f771])).

fof(f771,plain,
    ( ! [X177,X178] :
        ( sK0 != X177
        | r2_hidden(X178,k2_relat_1(sK6(X177,X178))) )
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f770])).

fof(f3629,plain,
    ( ! [X28,X29] :
        ( k1_tarski(sK1) = k2_relat_1(sK6(X28,X29))
        | r2_hidden(X29,k2_relat_1(sK6(X28,X29))) )
    | ~ spl7_13
    | ~ spl7_72 ),
    inference(subsumption_resolution,[],[f3628,f3071])).

fof(f3628,plain,
    ( ! [X28,X29] :
        ( r2_hidden(X29,k2_relat_1(sK6(X28,X29)))
        | k1_tarski(sK1) = k2_relat_1(sK6(X28,X29))
        | r2_hidden(X29,k1_tarski(sK1)) )
    | ~ spl7_13
    | ~ spl7_72 ),
    inference(subsumption_resolution,[],[f3627,f41])).

fof(f3627,plain,
    ( ! [X28,X29] :
        ( r2_hidden(X29,k2_relat_1(sK6(X28,X29)))
        | ~ v1_relat_1(sK6(X28,X29))
        | k1_tarski(sK1) = k2_relat_1(sK6(X28,X29))
        | r2_hidden(X29,k1_tarski(sK1)) )
    | ~ spl7_13
    | ~ spl7_72 ),
    inference(subsumption_resolution,[],[f3613,f42])).

fof(f3613,plain,
    ( ! [X28,X29] :
        ( r2_hidden(X29,k2_relat_1(sK6(X28,X29)))
        | ~ v1_funct_1(sK6(X28,X29))
        | ~ v1_relat_1(sK6(X28,X29))
        | k1_tarski(sK1) = k2_relat_1(sK6(X28,X29))
        | r2_hidden(X29,k1_tarski(sK1)) )
    | ~ spl7_13
    | ~ spl7_72 ),
    inference(duplicate_literal_removal,[],[f3612])).

fof(f3612,plain,
    ( ! [X28,X29] :
        ( r2_hidden(X29,k2_relat_1(sK6(X28,X29)))
        | ~ v1_funct_1(sK6(X28,X29))
        | ~ v1_relat_1(sK6(X28,X29))
        | k1_tarski(sK1) = k2_relat_1(sK6(X28,X29))
        | r2_hidden(X29,k1_tarski(sK1))
        | k1_tarski(sK1) = k2_relat_1(sK6(X28,X29)) )
    | ~ spl7_13
    | ~ spl7_72 ),
    inference(superposition,[],[f94,f3393])).

fof(f3393,plain,
    ( ! [X14,X15] :
        ( sK2(sK6(X14,X15),k1_tarski(sK1)) = X15
        | k1_tarski(sK1) = k2_relat_1(sK6(X14,X15)) )
    | ~ spl7_13
    | ~ spl7_72 ),
    inference(subsumption_resolution,[],[f3370,f3071])).

fof(f3370,plain,
    ( ! [X14,X15,X13] :
        ( sK2(sK6(X14,X15),k1_tarski(sK1)) = X15
        | k1_tarski(sK1) = k2_relat_1(sK6(X14,X15))
        | r2_hidden(X13,k1_tarski(sK1)) )
    | ~ spl7_13
    | ~ spl7_72 ),
    inference(superposition,[],[f350,f3093])).

fof(f3093,plain,
    ( ! [X0,X1] : k1_tarski(sK1) = k2_relat_1(sK6(k1_tarski(X0),X1))
    | ~ spl7_13
    | ~ spl7_72 ),
    inference(backward_demodulation,[],[f106,f3090])).

fof(f3090,plain,
    ( ! [X9] : k1_tarski(sK1) = k1_tarski(X9)
    | ~ spl7_13
    | ~ spl7_72 ),
    inference(subsumption_resolution,[],[f3089,f316])).

fof(f3089,plain,
    ( ! [X9] :
        ( k1_xboole_0 = k1_tarski(sK1)
        | k1_tarski(sK1) = k1_tarski(X9) )
    | ~ spl7_72 ),
    inference(resolution,[],[f3071,f38])).

fof(f350,plain,(
    ! [X2,X0,X3,X1] :
      ( sK2(sK6(X0,X1),k2_relat_1(sK6(X2,X3))) = X1
      | k2_relat_1(sK6(X0,X1)) = k2_relat_1(sK6(X2,X3))
      | r2_hidden(X3,k2_relat_1(sK6(X2,X3))) ) ),
    inference(subsumption_resolution,[],[f214,f205])).

fof(f214,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,k2_relat_1(sK6(X2,X3)))
      | k2_relat_1(sK6(X0,X1)) = k2_relat_1(sK6(X2,X3))
      | X1 = X3
      | sK2(sK6(X0,X1),k2_relat_1(sK6(X2,X3))) = X1 ) ),
    inference(duplicate_literal_removal,[],[f196])).

fof(f196,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,k2_relat_1(sK6(X2,X3)))
      | k2_relat_1(sK6(X0,X1)) = k2_relat_1(sK6(X2,X3))
      | X1 = X3
      | sK2(sK6(X0,X1),k2_relat_1(sK6(X2,X3))) = X1
      | k2_relat_1(sK6(X0,X1)) = k2_relat_1(sK6(X2,X3)) ) ),
    inference(superposition,[],[f155,f156])).

fof(f94,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK2(X3,X4),k2_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | k2_relat_1(X3) = X4
      | r2_hidden(sK2(X3,X4),X4) ) ),
    inference(subsumption_resolution,[],[f89,f35])).

fof(f89,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK2(X3,X4),k2_relat_1(X3))
      | ~ r2_hidden(sK3(X3,X4),k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | k2_relat_1(X3) = X4
      | r2_hidden(sK2(X3,X4),X4) ) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK2(X3,X4),k2_relat_1(X3))
      | ~ r2_hidden(sK3(X3,X4),k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | k2_relat_1(X3) = X4
      | r2_hidden(sK2(X3,X4),X4)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f47,f36])).

fof(f47,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3507,plain,
    ( ~ spl7_13
    | ~ spl7_22
    | ~ spl7_72 ),
    inference(avatar_contradiction_clause,[],[f3506])).

fof(f3506,plain,
    ( $false
    | ~ spl7_13
    | ~ spl7_22
    | ~ spl7_72 ),
    inference(subsumption_resolution,[],[f3504,f3071])).

fof(f3504,plain,
    ( ! [X5] : r2_hidden(X5,k1_tarski(sK1))
    | ~ spl7_13
    | ~ spl7_22
    | ~ spl7_72 ),
    inference(trivial_inequality_removal,[],[f3503])).

fof(f3503,plain,
    ( ! [X5] :
        ( k1_tarski(sK1) != k1_tarski(sK1)
        | r2_hidden(X5,k1_tarski(sK1)) )
    | ~ spl7_13
    | ~ spl7_22
    | ~ spl7_72 ),
    inference(superposition,[],[f768,f3093])).

fof(f768,plain,
    ( ! [X180,X179] :
        ( k1_tarski(sK1) != k2_relat_1(sK6(X179,X180))
        | r2_hidden(X180,k2_relat_1(sK6(X179,X180))) )
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f767])).

fof(f767,plain,
    ( spl7_22
  <=> ! [X179,X180] :
        ( k1_tarski(sK1) != k2_relat_1(sK6(X179,X180))
        | r2_hidden(X180,k2_relat_1(sK6(X179,X180))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f2850,plain,
    ( spl7_66
    | ~ spl7_24
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f2828,f1105,f962,f2526])).

fof(f962,plain,
    ( spl7_24
  <=> ! [X77,X76] : r2_hidden(X77,k2_relat_1(sK6(X76,X77))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f1105,plain,
    ( spl7_32
  <=> ! [X50,X54] : k1_xboole_0 = k2_relat_1(sK6(X54,X50)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f2828,plain,
    ( ! [X77] : r2_hidden(X77,k1_xboole_0)
    | ~ spl7_24
    | ~ spl7_32 ),
    inference(backward_demodulation,[],[f963,f1106])).

fof(f1106,plain,
    ( ! [X54,X50] : k1_xboole_0 = k2_relat_1(sK6(X54,X50))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f1105])).

fof(f963,plain,
    ( ! [X76,X77] : r2_hidden(X77,k2_relat_1(sK6(X76,X77)))
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f962])).

fof(f2804,plain,
    ( spl7_32
    | ~ spl7_2
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f2803,f962,f124,f1105])).

fof(f2803,plain,
    ( ! [X8,X9] : k1_xboole_0 = k2_relat_1(sK6(X8,X9))
    | ~ spl7_2
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f2801,f125])).

fof(f125,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_tarski(X0))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f124])).

fof(f2801,plain,
    ( ! [X8,X9] :
        ( r2_hidden(X9,k1_tarski(X9))
        | k1_xboole_0 = k2_relat_1(sK6(X8,X9)) )
    | ~ spl7_24 ),
    inference(superposition,[],[f963,f255])).

fof(f2610,plain,
    ( spl7_1
    | ~ spl7_47
    | ~ spl7_66 ),
    inference(avatar_contradiction_clause,[],[f2606])).

fof(f2606,plain,
    ( $false
    | spl7_1
    | ~ spl7_47
    | ~ spl7_66 ),
    inference(unit_resulting_resolution,[],[f53,f2527,f2527,f1993])).

fof(f1993,plain,
    ( ! [X8,X7] :
        ( ~ r2_hidden(X8,k1_xboole_0)
        | ~ r2_hidden(X7,k1_xboole_0)
        | X7 = X8 )
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f1992])).

fof(f1992,plain,
    ( spl7_47
  <=> ! [X7,X8] :
        ( ~ r2_hidden(X8,k1_xboole_0)
        | ~ r2_hidden(X7,k1_xboole_0)
        | X7 = X8 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f2527,plain,
    ( ! [X0] : r2_hidden(X0,k1_xboole_0)
    | ~ spl7_66 ),
    inference(avatar_component_clause,[],[f2526])).

fof(f53,plain,
    ( k1_xboole_0 != sK0
    | spl7_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl7_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f2588,plain,
    ( spl7_66
    | ~ spl7_2
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f2500,f770,f124,f2526])).

fof(f2500,plain,
    ( ! [X0] : r2_hidden(X0,k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_23 ),
    inference(backward_demodulation,[],[f1395,f2475])).

fof(f2475,plain,
    ( ! [X0] : k1_xboole_0 = k2_relat_1(sK6(sK0,X0))
    | ~ spl7_2
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f2448,f125])).

fof(f2448,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_tarski(X0))
        | k1_xboole_0 = k2_relat_1(sK6(sK0,X0)) )
    | ~ spl7_23 ),
    inference(superposition,[],[f1395,f255])).

fof(f1395,plain,
    ( ! [X0] : r2_hidden(X0,k2_relat_1(sK6(sK0,X0)))
    | ~ spl7_23 ),
    inference(equality_resolution,[],[f771])).

fof(f2285,plain,
    ( spl7_18
    | spl7_47
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f2260,f628,f561,f1992,f637])).

fof(f637,plain,
    ( spl7_18
  <=> ! [X19] : ~ r2_hidden(X19,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f2260,plain,
    ( ! [X2,X3,X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | X1 = X2
        | ~ r2_hidden(X2,k1_xboole_0)
        | ~ r2_hidden(X3,k1_xboole_0) )
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(superposition,[],[f673,f1540])).

fof(f1540,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k2_relat_1(sK6(X0,sK1))
        | ~ r2_hidden(X1,X0) )
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f1539,f630])).

fof(f1539,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | k1_xboole_0 = k2_relat_1(sK6(X0,sK1))
        | ~ r2_hidden(sK1,k1_xboole_0) )
    | ~ spl7_14 ),
    inference(trivial_inequality_removal,[],[f1538])).

fof(f1538,plain,
    ( ! [X0,X1] :
        ( sK1 != sK1
        | ~ r2_hidden(X1,X0)
        | k1_xboole_0 = k2_relat_1(sK6(X0,sK1))
        | ~ r2_hidden(sK1,k1_xboole_0) )
    | ~ spl7_14 ),
    inference(duplicate_literal_removal,[],[f1522])).

fof(f1522,plain,
    ( ! [X0,X1] :
        ( sK1 != sK1
        | ~ r2_hidden(X1,X0)
        | k1_xboole_0 = k2_relat_1(sK6(X0,sK1))
        | ~ r2_hidden(sK1,k1_xboole_0)
        | k1_xboole_0 = k2_relat_1(sK6(X0,sK1)) )
    | ~ spl7_14 ),
    inference(superposition,[],[f103,f617])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( sK2(sK6(X0,X1),X3) != X1
      | ~ r2_hidden(X2,X0)
      | k2_relat_1(sK6(X0,X1)) = X3
      | ~ r2_hidden(sK2(sK6(X0,X1),X3),X3) ) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,X0)
      | sK2(sK6(X0,X1),X3) != X1
      | k2_relat_1(sK6(X0,X1)) = X3
      | ~ r2_hidden(sK2(sK6(X0,X1),X3),X3)
      | ~ r2_hidden(X2,X0) ) ),
    inference(forward_demodulation,[],[f101,f43])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( sK2(sK6(X0,X1),X3) != X1
      | k2_relat_1(sK6(X0,X1)) = X3
      | ~ r2_hidden(X2,k1_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(sK2(sK6(X0,X1),X3),X3)
      | ~ r2_hidden(X2,X0) ) ),
    inference(subsumption_resolution,[],[f100,f41])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( sK2(sK6(X0,X1),X3) != X1
      | k2_relat_1(sK6(X0,X1)) = X3
      | ~ r2_hidden(X2,k1_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(sK2(sK6(X0,X1),X3),X3)
      | ~ v1_relat_1(sK6(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(subsumption_resolution,[],[f95,f42])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( sK2(sK6(X0,X1),X3) != X1
      | k2_relat_1(sK6(X0,X1)) = X3
      | ~ r2_hidden(X2,k1_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(sK2(sK6(X0,X1),X3),X3)
      | ~ v1_funct_1(sK6(X0,X1))
      | ~ v1_relat_1(sK6(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f37,f44])).

fof(f673,plain,
    ( ! [X6,X7,X5] :
        ( ~ r2_hidden(X7,k2_relat_1(sK6(k1_xboole_0,X6)))
        | X5 = X7
        | ~ r2_hidden(X5,k2_relat_1(sK6(k1_xboole_0,X6))) )
    | ~ spl7_14 ),
    inference(superposition,[],[f257,f563])).

fof(f257,plain,(
    ! [X6,X4,X8,X7,X5] :
      ( ~ r2_hidden(X8,k2_relat_1(sK6(k2_relat_1(sK6(X4,X5)),X6)))
      | X7 = X8
      | ~ r2_hidden(X7,k2_relat_1(sK6(k2_relat_1(sK6(X4,X5)),X6))) ) ),
    inference(superposition,[],[f174,f174])).

fof(f174,plain,(
    ! [X6,X4,X7,X5] :
      ( k1_funct_1(sK6(k2_relat_1(sK6(X4,X5)),X6),X5) = X7
      | ~ r2_hidden(X7,k2_relat_1(sK6(k2_relat_1(sK6(X4,X5)),X6))) ) ),
    inference(subsumption_resolution,[],[f173,f41])).

fof(f173,plain,(
    ! [X6,X4,X7,X5] :
      ( k1_funct_1(sK6(k2_relat_1(sK6(X4,X5)),X6),X5) = X7
      | ~ r2_hidden(X7,k2_relat_1(sK6(k2_relat_1(sK6(X4,X5)),X6)))
      | ~ v1_relat_1(sK6(k2_relat_1(sK6(X4,X5)),X6)) ) ),
    inference(subsumption_resolution,[],[f167,f42])).

fof(f167,plain,(
    ! [X6,X4,X7,X5] :
      ( k1_funct_1(sK6(k2_relat_1(sK6(X4,X5)),X6),X5) = X7
      | ~ r2_hidden(X7,k2_relat_1(sK6(k2_relat_1(sK6(X4,X5)),X6)))
      | ~ v1_funct_1(sK6(k2_relat_1(sK6(X4,X5)),X6))
      | ~ v1_relat_1(sK6(k2_relat_1(sK6(X4,X5)),X6)) ) ),
    inference(duplicate_literal_removal,[],[f164])).

fof(f164,plain,(
    ! [X6,X4,X7,X5] :
      ( k1_funct_1(sK6(k2_relat_1(sK6(X4,X5)),X6),X5) = X7
      | ~ r2_hidden(X7,k2_relat_1(sK6(k2_relat_1(sK6(X4,X5)),X6)))
      | ~ v1_funct_1(sK6(k2_relat_1(sK6(X4,X5)),X6))
      | ~ v1_relat_1(sK6(k2_relat_1(sK6(X4,X5)),X6))
      | ~ r2_hidden(X7,k2_relat_1(sK6(k2_relat_1(sK6(X4,X5)),X6))) ) ),
    inference(superposition,[],[f48,f78])).

fof(f78,plain,(
    ! [X6,X8,X7,X9] :
      ( sK4(sK6(k2_relat_1(sK6(X7,X6)),X8),X9) = X6
      | ~ r2_hidden(X9,k2_relat_1(sK6(k2_relat_1(sK6(X7,X6)),X8))) ) ),
    inference(resolution,[],[f69,f62])).

fof(f1367,plain,
    ( spl7_22
    | spl7_23 ),
    inference(avatar_split_clause,[],[f1366,f770,f767])).

fof(f1366,plain,(
    ! [X6,X4,X7,X5] :
      ( sK0 != X4
      | k1_tarski(sK1) != k2_relat_1(sK6(X6,X7))
      | r2_hidden(X7,k2_relat_1(sK6(X6,X7)))
      | r2_hidden(X5,k2_relat_1(sK6(X4,X5))) ) ),
    inference(forward_demodulation,[],[f1365,f43])).

fof(f1365,plain,(
    ! [X6,X4,X7,X5] :
      ( k1_tarski(sK1) != k2_relat_1(sK6(X6,X7))
      | sK0 != k1_relat_1(sK6(X4,X5))
      | r2_hidden(X7,k2_relat_1(sK6(X6,X7)))
      | r2_hidden(X5,k2_relat_1(sK6(X4,X5))) ) ),
    inference(subsumption_resolution,[],[f1364,f41])).

fof(f1364,plain,(
    ! [X6,X4,X7,X5] :
      ( k1_tarski(sK1) != k2_relat_1(sK6(X6,X7))
      | sK0 != k1_relat_1(sK6(X4,X5))
      | ~ v1_relat_1(sK6(X4,X5))
      | r2_hidden(X7,k2_relat_1(sK6(X6,X7)))
      | r2_hidden(X5,k2_relat_1(sK6(X4,X5))) ) ),
    inference(subsumption_resolution,[],[f1358,f42])).

fof(f1358,plain,(
    ! [X6,X4,X7,X5] :
      ( k1_tarski(sK1) != k2_relat_1(sK6(X6,X7))
      | sK0 != k1_relat_1(sK6(X4,X5))
      | ~ v1_funct_1(sK6(X4,X5))
      | ~ v1_relat_1(sK6(X4,X5))
      | r2_hidden(X7,k2_relat_1(sK6(X6,X7)))
      | r2_hidden(X5,k2_relat_1(sK6(X4,X5))) ) ),
    inference(superposition,[],[f30,f383])).

fof(f383,plain,(
    ! [X39,X37,X38,X40] :
      ( k2_relat_1(sK6(X39,X40)) = k2_relat_1(sK6(X37,X38))
      | r2_hidden(X38,k2_relat_1(sK6(X37,X38)))
      | r2_hidden(X40,k2_relat_1(sK6(X39,X40))) ) ),
    inference(subsumption_resolution,[],[f382,f228])).

fof(f228,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_relat_1(sK6(X1,X0)))
      | r2_hidden(X0,k2_relat_1(sK6(X1,X0))) ) ),
    inference(resolution,[],[f168,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X1,k2_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(X2,X0) ) ),
    inference(forward_demodulation,[],[f57,f43])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(X2,k1_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(X2,X0) ) ),
    inference(subsumption_resolution,[],[f56,f41])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(X2,k1_relat_1(sK6(X0,X1)))
      | ~ v1_relat_1(sK6(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(subsumption_resolution,[],[f55,f42])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(X2,k1_relat_1(sK6(X0,X1)))
      | ~ v1_funct_1(sK6(X0,X1))
      | ~ v1_relat_1(sK6(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f47,f44])).

fof(f168,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_relat_1(sK6(k2_relat_1(sK6(X0,X1)),X2)))
      | r2_hidden(X1,k2_relat_1(sK6(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f163])).

fof(f163,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,k2_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(X3,k2_relat_1(sK6(k2_relat_1(sK6(X0,X1)),X2)))
      | ~ r2_hidden(X3,k2_relat_1(sK6(k2_relat_1(sK6(X0,X1)),X2))) ) ),
    inference(superposition,[],[f62,f78])).

fof(f382,plain,(
    ! [X39,X37,X38,X40] :
      ( r2_hidden(X38,k2_relat_1(sK6(X37,X38)))
      | k2_relat_1(sK6(X39,X40)) = k2_relat_1(sK6(X37,X38))
      | r2_hidden(X38,k2_relat_1(sK6(X39,X40)))
      | r2_hidden(X40,k2_relat_1(sK6(X39,X40))) ) ),
    inference(subsumption_resolution,[],[f381,f41])).

fof(f381,plain,(
    ! [X39,X37,X38,X40] :
      ( r2_hidden(X38,k2_relat_1(sK6(X37,X38)))
      | ~ v1_relat_1(sK6(X37,X38))
      | k2_relat_1(sK6(X39,X40)) = k2_relat_1(sK6(X37,X38))
      | r2_hidden(X38,k2_relat_1(sK6(X39,X40)))
      | r2_hidden(X40,k2_relat_1(sK6(X39,X40))) ) ),
    inference(subsumption_resolution,[],[f368,f42])).

fof(f368,plain,(
    ! [X39,X37,X38,X40] :
      ( r2_hidden(X38,k2_relat_1(sK6(X37,X38)))
      | ~ v1_funct_1(sK6(X37,X38))
      | ~ v1_relat_1(sK6(X37,X38))
      | k2_relat_1(sK6(X39,X40)) = k2_relat_1(sK6(X37,X38))
      | r2_hidden(X38,k2_relat_1(sK6(X39,X40)))
      | r2_hidden(X40,k2_relat_1(sK6(X39,X40))) ) ),
    inference(duplicate_literal_removal,[],[f365])).

fof(f365,plain,(
    ! [X39,X37,X38,X40] :
      ( r2_hidden(X38,k2_relat_1(sK6(X37,X38)))
      | ~ v1_funct_1(sK6(X37,X38))
      | ~ v1_relat_1(sK6(X37,X38))
      | k2_relat_1(sK6(X39,X40)) = k2_relat_1(sK6(X37,X38))
      | r2_hidden(X38,k2_relat_1(sK6(X39,X40)))
      | k2_relat_1(sK6(X39,X40)) = k2_relat_1(sK6(X37,X38))
      | r2_hidden(X40,k2_relat_1(sK6(X39,X40))) ) ),
    inference(superposition,[],[f94,f350])).

fof(f1356,plain,
    ( spl7_15
    | spl7_16
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f898,f561,f628,f625])).

fof(f625,plain,
    ( spl7_15
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f898,plain,
    ( ! [X0] :
        ( r2_hidden(sK1,k1_xboole_0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl7_14 ),
    inference(duplicate_literal_removal,[],[f895])).

fof(f895,plain,
    ( ! [X0] :
        ( r2_hidden(sK1,k1_xboole_0)
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl7_14 ),
    inference(superposition,[],[f654,f44])).

fof(f654,plain,
    ( ! [X30] :
        ( r2_hidden(k1_funct_1(sK6(sK0,sK1),X30),k1_xboole_0)
        | ~ r2_hidden(X30,sK0) )
    | ~ spl7_14 ),
    inference(forward_demodulation,[],[f653,f43])).

fof(f653,plain,
    ( ! [X30] :
        ( r2_hidden(k1_funct_1(sK6(sK0,sK1),X30),k1_xboole_0)
        | ~ r2_hidden(X30,k1_relat_1(sK6(sK0,sK1))) )
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f652,f41])).

fof(f652,plain,
    ( ! [X30] :
        ( r2_hidden(k1_funct_1(sK6(sK0,sK1),X30),k1_xboole_0)
        | ~ r2_hidden(X30,k1_relat_1(sK6(sK0,sK1)))
        | ~ v1_relat_1(sK6(sK0,sK1)) )
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f622,f42])).

fof(f622,plain,
    ( ! [X30] :
        ( r2_hidden(k1_funct_1(sK6(sK0,sK1),X30),k1_xboole_0)
        | ~ r2_hidden(X30,k1_relat_1(sK6(sK0,sK1)))
        | ~ v1_funct_1(sK6(sK0,sK1))
        | ~ v1_relat_1(sK6(sK0,sK1)) )
    | ~ spl7_14 ),
    inference(superposition,[],[f47,f563])).

fof(f1333,plain,
    ( spl7_1
    | ~ spl7_14
    | ~ spl7_15 ),
    inference(avatar_contradiction_clause,[],[f1332])).

fof(f1332,plain,
    ( $false
    | spl7_1
    | ~ spl7_14
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f1315,f53])).

fof(f1315,plain,
    ( k1_xboole_0 = sK0
    | spl7_1
    | ~ spl7_14
    | ~ spl7_15 ),
    inference(superposition,[],[f1278,f563])).

fof(f1278,plain,
    ( ! [X1] : sK0 = k2_relat_1(sK6(sK0,X1))
    | spl7_1
    | ~ spl7_15 ),
    inference(forward_demodulation,[],[f1268,f1215])).

fof(f1215,plain,
    ( ! [X7] : sK0 = k1_tarski(X7)
    | spl7_1
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f1214,f53])).

fof(f1214,plain,
    ( ! [X7] :
        ( k1_xboole_0 = sK0
        | sK0 = k1_tarski(X7) )
    | ~ spl7_15 ),
    inference(resolution,[],[f626,f38])).

fof(f626,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f625])).

fof(f1268,plain,
    ( ! [X0,X1] : k2_relat_1(sK6(sK0,X1)) = k1_tarski(k1_funct_1(sK6(sK0,X1),X0))
    | spl7_1
    | ~ spl7_15 ),
    inference(backward_demodulation,[],[f106,f1215])).

fof(f995,plain,
    ( spl7_15
    | ~ spl7_14
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f975,f637,f561,f625])).

fof(f975,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl7_14
    | ~ spl7_18 ),
    inference(resolution,[],[f638,f654])).

fof(f638,plain,
    ( ! [X19] : ~ r2_hidden(X19,k1_xboole_0)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f637])).

fof(f966,plain,
    ( spl7_24
    | spl7_18
    | ~ spl7_2
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f954,f767,f124,f637,f962])).

fof(f954,plain,
    ( ! [X88,X85,X86] :
        ( ~ r2_hidden(X88,k1_xboole_0)
        | r2_hidden(X86,k2_relat_1(sK6(X85,X86))) )
    | ~ spl7_2
    | ~ spl7_22 ),
    inference(superposition,[],[f234,f916])).

fof(f916,plain,
    ( ! [X0] : k1_xboole_0 = k2_relat_1(sK6(X0,sK1))
    | ~ spl7_2
    | ~ spl7_22 ),
    inference(equality_resolution,[],[f913])).

fof(f913,plain,
    ( ! [X17,X16] :
        ( k1_tarski(sK1) != k1_tarski(X17)
        | k1_xboole_0 = k2_relat_1(sK6(X16,X17)) )
    | ~ spl7_2
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f911,f125])).

fof(f911,plain,
    ( ! [X17,X16] :
        ( k1_tarski(sK1) != k1_tarski(X17)
        | r2_hidden(X17,k1_tarski(X17))
        | k1_xboole_0 = k2_relat_1(sK6(X16,X17)) )
    | ~ spl7_22 ),
    inference(superposition,[],[f768,f255])).

fof(f234,plain,(
    ! [X30,X28,X31,X29,X27] :
      ( ~ r2_hidden(X29,k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(X28,X27)),X30)),X31)))
      | r2_hidden(X27,k2_relat_1(sK6(X28,X27))) ) ),
    inference(resolution,[],[f168,f62])).

fof(f564,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f559,f561])).

fof(f559,plain,(
    k1_xboole_0 = k2_relat_1(sK6(sK0,sK1)) ),
    inference(equality_resolution,[],[f558])).

fof(f558,plain,(
    ! [X0] :
      ( sK0 != X0
      | k1_xboole_0 = k2_relat_1(sK6(X0,sK1)) ) ),
    inference(equality_resolution,[],[f537])).

fof(f537,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) != k1_tarski(sK1)
      | sK0 != X0
      | k1_xboole_0 = k2_relat_1(sK6(X0,X1)) ) ),
    inference(superposition,[],[f536,f43])).

fof(f536,plain,(
    ! [X83,X84] :
      ( sK0 != k1_relat_1(sK6(X83,X84))
      | k1_tarski(sK1) != k1_tarski(X84)
      | k1_xboole_0 = k2_relat_1(sK6(X83,X84)) ) ),
    inference(subsumption_resolution,[],[f535,f41])).

fof(f535,plain,(
    ! [X83,X84] :
      ( k1_tarski(sK1) != k1_tarski(X84)
      | sK0 != k1_relat_1(sK6(X83,X84))
      | ~ v1_relat_1(sK6(X83,X84))
      | k1_xboole_0 = k2_relat_1(sK6(X83,X84)) ) ),
    inference(subsumption_resolution,[],[f521,f42])).

fof(f521,plain,(
    ! [X83,X84] :
      ( k1_tarski(sK1) != k1_tarski(X84)
      | sK0 != k1_relat_1(sK6(X83,X84))
      | ~ v1_funct_1(sK6(X83,X84))
      | ~ v1_relat_1(sK6(X83,X84))
      | k1_xboole_0 = k2_relat_1(sK6(X83,X84)) ) ),
    inference(superposition,[],[f30,f255])).

fof(f54,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f29,f51])).

fof(f29,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:35:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.52  % (23958)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.28/0.52  % (23948)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.28/0.52  % (23948)Refutation not found, incomplete strategy% (23948)------------------------------
% 1.28/0.52  % (23948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.52  % (23948)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.52  
% 1.28/0.52  % (23948)Memory used [KB]: 10618
% 1.28/0.52  % (23948)Time elapsed: 0.106 s
% 1.28/0.52  % (23948)------------------------------
% 1.28/0.52  % (23948)------------------------------
% 1.28/0.53  % (23953)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.28/0.53  % (23958)Refutation not found, incomplete strategy% (23958)------------------------------
% 1.28/0.53  % (23958)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (23958)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  
% 1.28/0.53  % (23958)Memory used [KB]: 10618
% 1.28/0.53  % (23958)Time elapsed: 0.113 s
% 1.28/0.53  % (23958)------------------------------
% 1.28/0.53  % (23958)------------------------------
% 1.28/0.53  % (23952)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.28/0.53  % (23965)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.28/0.53  % (23965)Refutation not found, incomplete strategy% (23965)------------------------------
% 1.28/0.53  % (23965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (23965)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  
% 1.28/0.53  % (23965)Memory used [KB]: 10618
% 1.28/0.53  % (23965)Time elapsed: 0.119 s
% 1.28/0.53  % (23965)------------------------------
% 1.28/0.53  % (23965)------------------------------
% 1.28/0.53  % (23956)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.28/0.53  % (23979)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.28/0.53  % (23964)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.28/0.53  % (23951)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.28/0.54  % (23951)Refutation not found, incomplete strategy% (23951)------------------------------
% 1.28/0.54  % (23951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (23951)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (23951)Memory used [KB]: 6140
% 1.28/0.54  % (23951)Time elapsed: 0.123 s
% 1.28/0.54  % (23951)------------------------------
% 1.28/0.54  % (23951)------------------------------
% 1.28/0.54  % (23968)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.39/0.54  % (23975)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.39/0.54  % (23969)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.39/0.54  % (23976)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.39/0.54  % (23947)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.39/0.54  % (23977)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.39/0.54  % (23946)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.39/0.54  % (23970)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.39/0.54  % (23949)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.39/0.54  % (23970)Refutation not found, incomplete strategy% (23970)------------------------------
% 1.39/0.54  % (23970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (23970)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  % (23969)Refutation not found, incomplete strategy% (23969)------------------------------
% 1.39/0.54  % (23969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  
% 1.39/0.54  % (23970)Memory used [KB]: 10618
% 1.39/0.54  % (23970)Time elapsed: 0.128 s
% 1.39/0.54  % (23970)------------------------------
% 1.39/0.54  % (23970)------------------------------
% 1.39/0.54  % (23954)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.39/0.54  % (23969)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (23969)Memory used [KB]: 1663
% 1.39/0.54  % (23969)Time elapsed: 0.126 s
% 1.39/0.54  % (23969)------------------------------
% 1.39/0.54  % (23969)------------------------------
% 1.39/0.54  % (23967)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.39/0.55  % (23961)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.39/0.55  % (23972)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.39/0.55  % (23974)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.39/0.55  % (23966)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.39/0.55  % (23974)Refutation not found, incomplete strategy% (23974)------------------------------
% 1.39/0.55  % (23974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (23974)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (23974)Memory used [KB]: 6268
% 1.39/0.55  % (23974)Time elapsed: 0.112 s
% 1.39/0.55  % (23974)------------------------------
% 1.39/0.55  % (23974)------------------------------
% 1.39/0.55  % (23960)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.39/0.56  % (23959)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.39/0.56  % (23971)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.39/0.56  % (23959)Refutation not found, incomplete strategy% (23959)------------------------------
% 1.39/0.56  % (23959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (23959)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (23959)Memory used [KB]: 10618
% 1.39/0.56  % (23959)Time elapsed: 0.159 s
% 1.39/0.56  % (23959)------------------------------
% 1.39/0.56  % (23959)------------------------------
% 1.39/0.56  % (23962)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.39/0.56  % (23968)Refutation not found, incomplete strategy% (23968)------------------------------
% 1.39/0.56  % (23968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (23968)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (23968)Memory used [KB]: 10618
% 1.39/0.56  % (23968)Time elapsed: 0.123 s
% 1.39/0.56  % (23968)------------------------------
% 1.39/0.56  % (23968)------------------------------
% 1.39/0.56  % (23975)Refutation not found, incomplete strategy% (23975)------------------------------
% 1.39/0.56  % (23975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (23975)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (23975)Memory used [KB]: 10746
% 1.39/0.56  % (23975)Time elapsed: 0.137 s
% 1.39/0.56  % (23975)------------------------------
% 1.39/0.56  % (23975)------------------------------
% 1.39/0.56  % (23955)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.39/0.56  % (23955)Refutation not found, incomplete strategy% (23955)------------------------------
% 1.39/0.56  % (23955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (23955)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (23955)Memory used [KB]: 10618
% 1.39/0.56  % (23955)Time elapsed: 0.156 s
% 1.39/0.56  % (23955)------------------------------
% 1.39/0.56  % (23955)------------------------------
% 1.39/0.57  % (23963)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.39/0.58  % (23963)Refutation not found, incomplete strategy% (23963)------------------------------
% 1.39/0.58  % (23963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.58  % (23963)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.58  
% 1.39/0.58  % (23963)Memory used [KB]: 6140
% 1.39/0.58  % (23963)Time elapsed: 0.166 s
% 1.39/0.58  % (23963)------------------------------
% 1.39/0.58  % (23963)------------------------------
% 1.92/0.63  % (24011)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.92/0.64  % (24012)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 1.92/0.64  % (24015)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 1.92/0.66  % (24016)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 1.92/0.67  % (24013)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.19/0.69  % (24019)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.19/0.69  % (24019)Refutation not found, incomplete strategy% (24019)------------------------------
% 2.19/0.69  % (24019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.69  % (24019)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.69  
% 2.19/0.69  % (24019)Memory used [KB]: 1791
% 2.19/0.69  % (24019)Time elapsed: 0.101 s
% 2.19/0.69  % (24019)------------------------------
% 2.19/0.69  % (24019)------------------------------
% 2.19/0.69  % (24014)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.19/0.70  % (24018)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.19/0.70  % (24021)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 2.19/0.70  % (24017)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.19/0.71  % (24020)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.19/0.71  % (24022)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 2.93/0.84  % (23952)Time limit reached!
% 2.93/0.84  % (23952)------------------------------
% 2.93/0.84  % (23952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.93/0.84  % (23952)Termination reason: Time limit
% 2.93/0.84  % (23952)Termination phase: Saturation
% 2.93/0.84  
% 2.93/0.84  % (23952)Memory used [KB]: 7803
% 2.93/0.84  % (23952)Time elapsed: 0.400 s
% 2.93/0.84  % (23952)------------------------------
% 2.93/0.84  % (23952)------------------------------
% 2.93/0.85  % (24028)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 2.93/0.92  % (23960)Time limit reached!
% 2.93/0.92  % (23960)------------------------------
% 2.93/0.92  % (23960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.93/0.92  % (23960)Termination reason: Time limit
% 2.93/0.92  % (23960)Termination phase: Saturation
% 2.93/0.92  
% 2.93/0.92  % (23960)Memory used [KB]: 8315
% 2.93/0.92  % (23960)Time elapsed: 0.520 s
% 2.93/0.92  % (23960)------------------------------
% 2.93/0.92  % (23960)------------------------------
% 2.93/0.92  % (23947)Time limit reached!
% 2.93/0.92  % (23947)------------------------------
% 2.93/0.92  % (23947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.93/0.92  % (23947)Termination reason: Time limit
% 2.93/0.92  
% 2.93/0.92  % (23947)Memory used [KB]: 8571
% 2.93/0.92  % (23947)Time elapsed: 0.517 s
% 2.93/0.92  % (23947)------------------------------
% 2.93/0.92  % (23947)------------------------------
% 3.36/0.94  % (23946)Time limit reached!
% 3.36/0.94  % (23946)------------------------------
% 3.36/0.94  % (23946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.36/0.94  % (23946)Termination reason: Time limit
% 3.36/0.94  
% 3.36/0.94  % (23946)Memory used [KB]: 3582
% 3.36/0.94  % (23946)Time elapsed: 0.532 s
% 3.36/0.94  % (23946)------------------------------
% 3.36/0.94  % (23946)------------------------------
% 3.36/0.96  % (24036)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 3.36/0.97  % (24036)Refutation not found, incomplete strategy% (24036)------------------------------
% 3.36/0.97  % (24036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.36/0.97  % (24036)Termination reason: Refutation not found, incomplete strategy
% 3.36/0.97  
% 3.36/0.97  % (24036)Memory used [KB]: 1663
% 3.36/0.97  % (24036)Time elapsed: 0.111 s
% 3.36/0.97  % (24036)------------------------------
% 3.36/0.97  % (24036)------------------------------
% 3.36/0.98  % (24014)Time limit reached!
% 3.36/0.98  % (24014)------------------------------
% 3.36/0.98  % (24014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.36/0.98  % (24014)Termination reason: Time limit
% 3.36/0.98  % (24014)Termination phase: Saturation
% 3.36/0.98  
% 3.36/0.98  % (24014)Memory used [KB]: 7675
% 3.36/0.98  % (24014)Time elapsed: 0.421 s
% 3.36/0.98  % (24014)------------------------------
% 3.36/0.98  % (24014)------------------------------
% 3.72/1.00  % (24013)Refutation found. Thanks to Tanya!
% 3.72/1.00  % SZS status Theorem for theBenchmark
% 3.72/1.01  % (24015)Time limit reached!
% 3.72/1.01  % (24015)------------------------------
% 3.72/1.01  % (24015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.72/1.01  % (24015)Termination reason: Time limit
% 3.72/1.01  
% 3.72/1.01  % (24015)Memory used [KB]: 13560
% 3.72/1.01  % (24015)Time elapsed: 0.429 s
% 3.72/1.01  % (24015)------------------------------
% 3.72/1.01  % (24015)------------------------------
% 3.72/1.01  % (23964)Time limit reached!
% 3.72/1.01  % (23964)------------------------------
% 3.72/1.01  % (23964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.72/1.01  % (23964)Termination reason: Time limit
% 3.72/1.01  
% 3.72/1.01  % (23964)Memory used [KB]: 15223
% 3.72/1.01  % (23964)Time elapsed: 0.606 s
% 3.72/1.01  % (23964)------------------------------
% 3.72/1.01  % (23964)------------------------------
% 3.72/1.01  % (23977)Time limit reached!
% 3.72/1.01  % (23977)------------------------------
% 3.72/1.01  % (23977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.72/1.02  % SZS output start Proof for theBenchmark
% 3.72/1.02  fof(f4245,plain,(
% 3.72/1.02    $false),
% 3.72/1.02    inference(avatar_sat_refutation,[],[f54,f564,f966,f995,f1333,f1356,f1367,f2285,f2588,f2610,f2804,f2850,f3507,f4118,f4204,f4221,f4232,f4243,f4244])).
% 3.72/1.02  fof(f4244,plain,(
% 3.72/1.02    spl7_13 | spl7_21 | ~spl7_92),
% 3.72/1.02    inference(avatar_split_clause,[],[f4242,f4200,f659,f315])).
% 3.72/1.02  fof(f315,plain,(
% 3.72/1.02    spl7_13 <=> ! [X2] : k1_xboole_0 != k1_tarski(X2)),
% 3.72/1.02    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 3.72/1.02  fof(f659,plain,(
% 3.72/1.02    spl7_21 <=> k1_xboole_0 = k1_tarski(sK1)),
% 3.72/1.02    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 3.72/1.02  fof(f4200,plain,(
% 3.72/1.02    spl7_92 <=> ! [X9] : k1_tarski(sK1) = k1_tarski(X9)),
% 3.72/1.02    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).
% 3.72/1.02  fof(f4242,plain,(
% 3.72/1.02    ( ! [X2] : (k1_xboole_0 != k1_tarski(X2)) ) | (spl7_21 | ~spl7_92)),
% 3.72/1.02    inference(superposition,[],[f661,f4201])).
% 3.72/1.02  fof(f4201,plain,(
% 3.72/1.02    ( ! [X9] : (k1_tarski(sK1) = k1_tarski(X9)) ) | ~spl7_92),
% 3.72/1.02    inference(avatar_component_clause,[],[f4200])).
% 3.72/1.02  fof(f661,plain,(
% 3.72/1.02    k1_xboole_0 != k1_tarski(sK1) | spl7_21),
% 3.72/1.02    inference(avatar_component_clause,[],[f659])).
% 3.72/1.02  fof(f4243,plain,(
% 3.72/1.02    spl7_10 | ~spl7_72 | ~spl7_92),
% 3.72/1.02    inference(avatar_split_clause,[],[f4241,f4200,f3070,f294])).
% 3.72/1.02  fof(f294,plain,(
% 3.72/1.02    spl7_10 <=> ! [X51,X52] : ~r2_hidden(X52,k1_tarski(X51))),
% 3.72/1.02    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 3.72/1.02  fof(f3070,plain,(
% 3.72/1.02    spl7_72 <=> ! [X22] : ~r2_hidden(X22,k1_tarski(sK1))),
% 3.72/1.02    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).
% 3.72/1.02  fof(f4241,plain,(
% 3.72/1.02    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(X0))) ) | (~spl7_72 | ~spl7_92)),
% 3.72/1.02    inference(superposition,[],[f3071,f4201])).
% 3.72/1.02  fof(f3071,plain,(
% 3.72/1.02    ( ! [X22] : (~r2_hidden(X22,k1_tarski(sK1))) ) | ~spl7_72),
% 3.72/1.02    inference(avatar_component_clause,[],[f3070])).
% 3.72/1.02  fof(f4232,plain,(
% 3.72/1.02    spl7_92 | spl7_21 | ~spl7_72),
% 3.72/1.02    inference(avatar_split_clause,[],[f4231,f3070,f659,f4200])).
% 3.72/1.02  fof(f4231,plain,(
% 3.72/1.02    ( ! [X9] : (k1_tarski(sK1) = k1_tarski(X9)) ) | (spl7_21 | ~spl7_72)),
% 3.72/1.02    inference(subsumption_resolution,[],[f4230,f661])).
% 3.72/1.02  fof(f4230,plain,(
% 3.72/1.02    ( ! [X9] : (k1_xboole_0 = k1_tarski(sK1) | k1_tarski(sK1) = k1_tarski(X9)) ) | ~spl7_72),
% 3.72/1.02    inference(resolution,[],[f3071,f38])).
% 3.72/1.02  fof(f38,plain,(
% 3.72/1.02    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 3.72/1.02    inference(cnf_transformation,[],[f26])).
% 3.72/1.02  fof(f26,plain,(
% 3.72/1.02    ! [X0,X1] : ((sK5(X0,X1) != X1 & r2_hidden(sK5(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 3.72/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f14,f25])).
% 3.72/1.02  fof(f25,plain,(
% 3.72/1.02    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK5(X0,X1) != X1 & r2_hidden(sK5(X0,X1),X0)))),
% 3.72/1.02    introduced(choice_axiom,[])).
% 3.72/1.02  fof(f14,plain,(
% 3.72/1.02    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 3.72/1.02    inference(ennf_transformation,[],[f3])).
% 3.72/1.02  fof(f3,axiom,(
% 3.72/1.02    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 3.72/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 3.72/1.02  fof(f4221,plain,(
% 3.72/1.02    ~spl7_21 | ~spl7_14),
% 3.72/1.02    inference(avatar_split_clause,[],[f4220,f561,f659])).
% 3.72/1.02  fof(f561,plain,(
% 3.72/1.02    spl7_14 <=> k1_xboole_0 = k2_relat_1(sK6(sK0,sK1))),
% 3.72/1.02    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 3.72/1.02  fof(f4220,plain,(
% 3.72/1.02    k1_xboole_0 != k1_tarski(sK1) | ~spl7_14),
% 3.72/1.02    inference(subsumption_resolution,[],[f4219,f41])).
% 3.72/1.02  fof(f41,plain,(
% 3.72/1.02    ( ! [X0,X1] : (v1_relat_1(sK6(X0,X1))) )),
% 3.72/1.02    inference(cnf_transformation,[],[f28])).
% 3.72/1.02  fof(f28,plain,(
% 3.72/1.02    ! [X0,X1] : (! [X3] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK6(X0,X1)) = X0 & v1_funct_1(sK6(X0,X1)) & v1_relat_1(sK6(X0,X1)))),
% 3.72/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f15,f27])).
% 3.72/1.02  fof(f27,plain,(
% 3.72/1.02    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK6(X0,X1)) = X0 & v1_funct_1(sK6(X0,X1)) & v1_relat_1(sK6(X0,X1))))),
% 3.72/1.02    introduced(choice_axiom,[])).
% 3.72/1.02  fof(f15,plain,(
% 3.72/1.02    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.72/1.02    inference(ennf_transformation,[],[f5])).
% 3.72/1.02  fof(f5,axiom,(
% 3.72/1.02    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.72/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 3.72/1.02  fof(f4219,plain,(
% 3.72/1.02    k1_xboole_0 != k1_tarski(sK1) | ~v1_relat_1(sK6(sK0,sK1)) | ~spl7_14),
% 3.72/1.02    inference(subsumption_resolution,[],[f4218,f42])).
% 3.72/1.02  fof(f42,plain,(
% 3.72/1.02    ( ! [X0,X1] : (v1_funct_1(sK6(X0,X1))) )),
% 3.72/1.02    inference(cnf_transformation,[],[f28])).
% 3.72/1.02  fof(f4218,plain,(
% 3.72/1.02    k1_xboole_0 != k1_tarski(sK1) | ~v1_funct_1(sK6(sK0,sK1)) | ~v1_relat_1(sK6(sK0,sK1)) | ~spl7_14),
% 3.72/1.02    inference(subsumption_resolution,[],[f2679,f43])).
% 3.72/1.02  fof(f43,plain,(
% 3.72/1.02    ( ! [X0,X1] : (k1_relat_1(sK6(X0,X1)) = X0) )),
% 3.72/1.02    inference(cnf_transformation,[],[f28])).
% 3.72/1.02  fof(f2679,plain,(
% 3.72/1.02    k1_xboole_0 != k1_tarski(sK1) | sK0 != k1_relat_1(sK6(sK0,sK1)) | ~v1_funct_1(sK6(sK0,sK1)) | ~v1_relat_1(sK6(sK0,sK1)) | ~spl7_14),
% 3.72/1.02    inference(superposition,[],[f30,f563])).
% 3.72/1.02  fof(f563,plain,(
% 3.72/1.02    k1_xboole_0 = k2_relat_1(sK6(sK0,sK1)) | ~spl7_14),
% 3.72/1.02    inference(avatar_component_clause,[],[f561])).
% 3.72/1.02  fof(f30,plain,(
% 3.72/1.02    ( ! [X2] : (k2_relat_1(X2) != k1_tarski(sK1) | k1_relat_1(X2) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.72/1.02    inference(cnf_transformation,[],[f18])).
% 3.72/1.02  fof(f18,plain,(
% 3.72/1.02    ! [X2] : (k2_relat_1(X2) != k1_tarski(sK1) | k1_relat_1(X2) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & k1_xboole_0 != sK0),
% 3.72/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f17,f16])).
% 3.72/1.02  fof(f16,plain,(
% 3.72/1.02    ? [X0] : (? [X1] : ! [X2] : (k1_tarski(X1) != k2_relat_1(X2) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & k1_xboole_0 != X0) => (? [X1] : ! [X2] : (k1_tarski(X1) != k2_relat_1(X2) | k1_relat_1(X2) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & k1_xboole_0 != sK0)),
% 3.72/1.02    introduced(choice_axiom,[])).
% 3.72/1.02  fof(f17,plain,(
% 3.72/1.02    ? [X1] : ! [X2] : (k1_tarski(X1) != k2_relat_1(X2) | k1_relat_1(X2) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) => ! [X2] : (k2_relat_1(X2) != k1_tarski(sK1) | k1_relat_1(X2) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.72/1.02    introduced(choice_axiom,[])).
% 3.72/1.02  fof(f9,plain,(
% 3.72/1.02    ? [X0] : (? [X1] : ! [X2] : (k1_tarski(X1) != k2_relat_1(X2) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & k1_xboole_0 != X0)),
% 3.72/1.02    inference(ennf_transformation,[],[f8])).
% 3.72/1.02  fof(f8,negated_conjecture,(
% 3.72/1.02    ~! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 3.72/1.02    inference(negated_conjecture,[],[f7])).
% 3.72/1.02  fof(f7,conjecture,(
% 3.72/1.02    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 3.72/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 3.72/1.02  fof(f4204,plain,(
% 3.72/1.02    spl7_2 | spl7_21 | spl7_72 | ~spl7_14 | ~spl7_16),
% 3.72/1.02    inference(avatar_split_clause,[],[f3050,f628,f561,f3070,f659,f124])).
% 3.72/1.02  fof(f124,plain,(
% 3.72/1.02    spl7_2 <=> ! [X0] : ~r2_hidden(X0,k1_tarski(X0))),
% 3.72/1.02    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 3.72/1.02  fof(f628,plain,(
% 3.72/1.02    spl7_16 <=> r2_hidden(sK1,k1_xboole_0)),
% 3.72/1.02    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 3.72/1.02  fof(f3050,plain,(
% 3.72/1.02    ( ! [X21,X22] : (~r2_hidden(X22,k1_tarski(sK1)) | k1_xboole_0 = k1_tarski(sK1) | ~r2_hidden(X21,k1_tarski(X21))) ) | (~spl7_14 | ~spl7_16)),
% 3.72/1.02    inference(superposition,[],[f1548,f112])).
% 3.72/1.02  fof(f112,plain,(
% 3.72/1.02    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK6(k1_tarski(X0),X1)) | ~r2_hidden(X0,k1_tarski(X0))) )),
% 3.72/1.02    inference(superposition,[],[f106,f44])).
% 3.72/1.02  fof(f44,plain,(
% 3.72/1.02    ( ! [X0,X3,X1] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 3.72/1.02    inference(cnf_transformation,[],[f28])).
% 3.72/1.02  fof(f106,plain,(
% 3.72/1.02    ( ! [X0,X1] : (k2_relat_1(sK6(k1_tarski(X0),X1)) = k1_tarski(k1_funct_1(sK6(k1_tarski(X0),X1),X0))) )),
% 3.72/1.02    inference(equality_resolution,[],[f75])).
% 3.72/1.02  fof(f75,plain,(
% 3.72/1.02    ( ! [X2,X0,X1] : (k1_tarski(X2) != X0 | k2_relat_1(sK6(X0,X1)) = k1_tarski(k1_funct_1(sK6(X0,X1),X2))) )),
% 3.72/1.02    inference(subsumption_resolution,[],[f74,f41])).
% 3.72/1.02  fof(f74,plain,(
% 3.72/1.02    ( ! [X2,X0,X1] : (k1_tarski(X2) != X0 | k2_relat_1(sK6(X0,X1)) = k1_tarski(k1_funct_1(sK6(X0,X1),X2)) | ~v1_relat_1(sK6(X0,X1))) )),
% 3.72/1.02    inference(subsumption_resolution,[],[f73,f42])).
% 3.72/1.02  fof(f73,plain,(
% 3.72/1.02    ( ! [X2,X0,X1] : (k1_tarski(X2) != X0 | k2_relat_1(sK6(X0,X1)) = k1_tarski(k1_funct_1(sK6(X0,X1),X2)) | ~v1_funct_1(sK6(X0,X1)) | ~v1_relat_1(sK6(X0,X1))) )),
% 3.72/1.02    inference(superposition,[],[f31,f43])).
% 3.72/1.02  fof(f31,plain,(
% 3.72/1.02    ( ! [X0,X1] : (k1_tarski(X0) != k1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.72/1.02    inference(cnf_transformation,[],[f11])).
% 3.72/1.02  fof(f11,plain,(
% 3.72/1.02    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.72/1.02    inference(flattening,[],[f10])).
% 3.72/1.02  fof(f10,plain,(
% 3.72/1.02    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.72/1.02    inference(ennf_transformation,[],[f6])).
% 3.72/1.02  fof(f6,axiom,(
% 3.72/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 3.72/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 3.72/1.02  fof(f1548,plain,(
% 3.72/1.02    ( ! [X12,X13] : (~r2_hidden(X13,k2_relat_1(sK6(X12,sK1))) | k1_xboole_0 = k2_relat_1(sK6(X12,sK1))) ) | (~spl7_14 | ~spl7_16)),
% 3.72/1.02    inference(subsumption_resolution,[],[f1547,f69])).
% 3.72/1.02  fof(f69,plain,(
% 3.72/1.02    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_relat_1(sK6(X0,X1))) | X1 = X2) )),
% 3.72/1.02    inference(subsumption_resolution,[],[f68,f62])).
% 3.72/1.02  fof(f62,plain,(
% 3.72/1.02    ( ! [X2,X0,X1] : (r2_hidden(sK4(sK6(X0,X1),X2),X0) | ~r2_hidden(X2,k2_relat_1(sK6(X0,X1)))) )),
% 3.72/1.02    inference(subsumption_resolution,[],[f61,f41])).
% 3.72/1.02  fof(f61,plain,(
% 3.72/1.02    ( ! [X2,X0,X1] : (r2_hidden(sK4(sK6(X0,X1),X2),X0) | ~r2_hidden(X2,k2_relat_1(sK6(X0,X1))) | ~v1_relat_1(sK6(X0,X1))) )),
% 3.72/1.02    inference(subsumption_resolution,[],[f60,f42])).
% 3.72/1.02  fof(f60,plain,(
% 3.72/1.02    ( ! [X2,X0,X1] : (r2_hidden(sK4(sK6(X0,X1),X2),X0) | ~r2_hidden(X2,k2_relat_1(sK6(X0,X1))) | ~v1_funct_1(sK6(X0,X1)) | ~v1_relat_1(sK6(X0,X1))) )),
% 3.72/1.02    inference(superposition,[],[f49,f43])).
% 3.72/1.02  fof(f49,plain,(
% 3.72/1.02    ( ! [X0,X5] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.72/1.02    inference(equality_resolution,[],[f32])).
% 3.72/1.02  fof(f32,plain,(
% 3.72/1.02    ( ! [X0,X5,X1] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.72/1.02    inference(cnf_transformation,[],[f24])).
% 3.72/1.02  fof(f24,plain,(
% 3.72/1.02    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & ((sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.72/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f23,f22,f21])).
% 3.72/1.03  fof(f21,plain,(
% 3.72/1.03    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1))))),
% 3.72/1.03    introduced(choice_axiom,[])).
% 3.72/1.03  fof(f22,plain,(
% 3.72/1.03    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))),
% 3.72/1.03    introduced(choice_axiom,[])).
% 3.72/1.03  fof(f23,plain,(
% 3.72/1.03    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))))),
% 3.72/1.03    introduced(choice_axiom,[])).
% 3.72/1.03  fof(f20,plain,(
% 3.72/1.03    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.72/1.03    inference(rectify,[],[f19])).
% 3.72/1.03  fof(f19,plain,(
% 3.72/1.03    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.72/1.03    inference(nnf_transformation,[],[f13])).
% 3.72/1.03  fof(f13,plain,(
% 3.72/1.03    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.72/1.03    inference(flattening,[],[f12])).
% 3.72/1.03  fof(f12,plain,(
% 3.72/1.03    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.72/1.03    inference(ennf_transformation,[],[f4])).
% 3.72/1.03  fof(f4,axiom,(
% 3.72/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.72/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 3.72/1.03  fof(f68,plain,(
% 3.72/1.03    ( ! [X2,X0,X1] : (X1 = X2 | ~r2_hidden(X2,k2_relat_1(sK6(X0,X1))) | ~r2_hidden(sK4(sK6(X0,X1),X2),X0)) )),
% 3.72/1.03    inference(subsumption_resolution,[],[f67,f41])).
% 3.72/1.03  fof(f67,plain,(
% 3.72/1.03    ( ! [X2,X0,X1] : (X1 = X2 | ~r2_hidden(X2,k2_relat_1(sK6(X0,X1))) | ~v1_relat_1(sK6(X0,X1)) | ~r2_hidden(sK4(sK6(X0,X1),X2),X0)) )),
% 3.72/1.03    inference(subsumption_resolution,[],[f63,f42])).
% 3.72/1.03  fof(f63,plain,(
% 3.72/1.03    ( ! [X2,X0,X1] : (X1 = X2 | ~r2_hidden(X2,k2_relat_1(sK6(X0,X1))) | ~v1_funct_1(sK6(X0,X1)) | ~v1_relat_1(sK6(X0,X1)) | ~r2_hidden(sK4(sK6(X0,X1),X2),X0)) )),
% 3.72/1.03    inference(superposition,[],[f48,f44])).
% 3.72/1.03  fof(f48,plain,(
% 3.72/1.03    ( ! [X0,X5] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.72/1.03    inference(equality_resolution,[],[f33])).
% 3.72/1.03  fof(f33,plain,(
% 3.72/1.03    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.72/1.03    inference(cnf_transformation,[],[f24])).
% 3.72/1.03  fof(f1547,plain,(
% 3.72/1.03    ( ! [X12,X13] : (sK1 != X13 | k1_xboole_0 = k2_relat_1(sK6(X12,sK1)) | ~r2_hidden(X13,k2_relat_1(sK6(X12,sK1)))) ) | (~spl7_14 | ~spl7_16)),
% 3.72/1.03    inference(subsumption_resolution,[],[f1546,f41])).
% 3.72/1.03  fof(f1546,plain,(
% 3.72/1.03    ( ! [X12,X13] : (sK1 != X13 | k1_xboole_0 = k2_relat_1(sK6(X12,sK1)) | ~v1_relat_1(sK6(X12,sK1)) | ~r2_hidden(X13,k2_relat_1(sK6(X12,sK1)))) ) | (~spl7_14 | ~spl7_16)),
% 3.72/1.03    inference(subsumption_resolution,[],[f1545,f42])).
% 3.72/1.03  fof(f1545,plain,(
% 3.72/1.03    ( ! [X12,X13] : (sK1 != X13 | k1_xboole_0 = k2_relat_1(sK6(X12,sK1)) | ~v1_funct_1(sK6(X12,sK1)) | ~v1_relat_1(sK6(X12,sK1)) | ~r2_hidden(X13,k2_relat_1(sK6(X12,sK1)))) ) | (~spl7_14 | ~spl7_16)),
% 3.72/1.03    inference(subsumption_resolution,[],[f1533,f630])).
% 3.72/1.03  fof(f630,plain,(
% 3.72/1.03    r2_hidden(sK1,k1_xboole_0) | ~spl7_16),
% 3.72/1.03    inference(avatar_component_clause,[],[f628])).
% 3.72/1.03  fof(f1533,plain,(
% 3.72/1.03    ( ! [X12,X13] : (sK1 != X13 | k1_xboole_0 = k2_relat_1(sK6(X12,sK1)) | ~r2_hidden(sK1,k1_xboole_0) | ~v1_funct_1(sK6(X12,sK1)) | ~v1_relat_1(sK6(X12,sK1)) | ~r2_hidden(X13,k2_relat_1(sK6(X12,sK1)))) ) | ~spl7_14),
% 3.72/1.03    inference(duplicate_literal_removal,[],[f1528])).
% 3.72/1.03  fof(f1528,plain,(
% 3.72/1.03    ( ! [X12,X13] : (sK1 != X13 | k1_xboole_0 = k2_relat_1(sK6(X12,sK1)) | ~r2_hidden(sK1,k1_xboole_0) | ~v1_funct_1(sK6(X12,sK1)) | ~v1_relat_1(sK6(X12,sK1)) | ~r2_hidden(X13,k2_relat_1(sK6(X12,sK1))) | k1_xboole_0 = k2_relat_1(sK6(X12,sK1))) ) | ~spl7_14),
% 3.72/1.03    inference(superposition,[],[f104,f617])).
% 3.72/1.03  fof(f617,plain,(
% 3.72/1.03    ( ! [X23] : (sK1 = sK2(sK6(X23,sK1),k1_xboole_0) | k1_xboole_0 = k2_relat_1(sK6(X23,sK1))) ) | ~spl7_14),
% 3.72/1.03    inference(superposition,[],[f319,f563])).
% 3.72/1.03  fof(f319,plain,(
% 3.72/1.03    ( ! [X2,X0,X1] : (sK2(sK6(X0,X1),k2_relat_1(sK6(X2,X1))) = X1 | k2_relat_1(sK6(X0,X1)) = k2_relat_1(sK6(X2,X1))) )),
% 3.72/1.03    inference(equality_resolution,[],[f205])).
% 3.72/1.03  fof(f205,plain,(
% 3.72/1.03    ( ! [X2,X0,X3,X1] : (X1 != X3 | sK2(sK6(X0,X1),k2_relat_1(sK6(X2,X3))) = X1 | k2_relat_1(sK6(X0,X1)) = k2_relat_1(sK6(X2,X3))) )),
% 3.72/1.03    inference(equality_factoring,[],[f156])).
% 3.72/1.03  fof(f156,plain,(
% 3.72/1.03    ( ! [X2,X0,X3,X1] : (sK2(sK6(X0,X1),k2_relat_1(sK6(X2,X3))) = X3 | sK2(sK6(X0,X1),k2_relat_1(sK6(X2,X3))) = X1 | k2_relat_1(sK6(X0,X1)) = k2_relat_1(sK6(X2,X3))) )),
% 3.72/1.03    inference(resolution,[],[f155,f69])).
% 3.72/1.03  fof(f155,plain,(
% 3.72/1.03    ( ! [X2,X0,X1] : (r2_hidden(sK2(sK6(X0,X1),X2),X2) | k2_relat_1(sK6(X0,X1)) = X2 | sK2(sK6(X0,X1),X2) = X1) )),
% 3.72/1.03    inference(subsumption_resolution,[],[f91,f85])).
% 3.72/1.03  fof(f85,plain,(
% 3.72/1.03    ( ! [X2,X0,X1] : (r2_hidden(sK3(sK6(X0,X1),X2),X0) | k2_relat_1(sK6(X0,X1)) = X2 | r2_hidden(sK2(sK6(X0,X1),X2),X2)) )),
% 3.72/1.03    inference(subsumption_resolution,[],[f84,f41])).
% 3.72/1.03  fof(f84,plain,(
% 3.72/1.03    ( ! [X2,X0,X1] : (r2_hidden(sK3(sK6(X0,X1),X2),X0) | k2_relat_1(sK6(X0,X1)) = X2 | r2_hidden(sK2(sK6(X0,X1),X2),X2) | ~v1_relat_1(sK6(X0,X1))) )),
% 3.72/1.03    inference(subsumption_resolution,[],[f83,f42])).
% 3.72/1.03  fof(f83,plain,(
% 3.72/1.03    ( ! [X2,X0,X1] : (r2_hidden(sK3(sK6(X0,X1),X2),X0) | k2_relat_1(sK6(X0,X1)) = X2 | r2_hidden(sK2(sK6(X0,X1),X2),X2) | ~v1_funct_1(sK6(X0,X1)) | ~v1_relat_1(sK6(X0,X1))) )),
% 3.72/1.03    inference(superposition,[],[f35,f43])).
% 3.72/1.03  fof(f35,plain,(
% 3.72/1.03    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | k2_relat_1(X0) = X1 | r2_hidden(sK2(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.72/1.03    inference(cnf_transformation,[],[f24])).
% 3.72/1.03  fof(f91,plain,(
% 3.72/1.03    ( ! [X2,X0,X1] : (sK2(sK6(X0,X1),X2) = X1 | k2_relat_1(sK6(X0,X1)) = X2 | r2_hidden(sK2(sK6(X0,X1),X2),X2) | ~r2_hidden(sK3(sK6(X0,X1),X2),X0)) )),
% 3.72/1.03    inference(subsumption_resolution,[],[f90,f41])).
% 3.72/1.03  fof(f90,plain,(
% 3.72/1.03    ( ! [X2,X0,X1] : (sK2(sK6(X0,X1),X2) = X1 | k2_relat_1(sK6(X0,X1)) = X2 | r2_hidden(sK2(sK6(X0,X1),X2),X2) | ~v1_relat_1(sK6(X0,X1)) | ~r2_hidden(sK3(sK6(X0,X1),X2),X0)) )),
% 3.72/1.03    inference(subsumption_resolution,[],[f86,f42])).
% 3.72/1.03  fof(f86,plain,(
% 3.72/1.03    ( ! [X2,X0,X1] : (sK2(sK6(X0,X1),X2) = X1 | k2_relat_1(sK6(X0,X1)) = X2 | r2_hidden(sK2(sK6(X0,X1),X2),X2) | ~v1_funct_1(sK6(X0,X1)) | ~v1_relat_1(sK6(X0,X1)) | ~r2_hidden(sK3(sK6(X0,X1),X2),X0)) )),
% 3.72/1.03    inference(superposition,[],[f36,f44])).
% 3.72/1.03  fof(f36,plain,(
% 3.72/1.03    ( ! [X0,X1] : (sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) | k2_relat_1(X0) = X1 | r2_hidden(sK2(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.72/1.03    inference(cnf_transformation,[],[f24])).
% 3.72/1.03  fof(f104,plain,(
% 3.72/1.03    ( ! [X6,X4,X5] : (sK2(X4,X6) != X5 | k2_relat_1(X4) = X6 | ~r2_hidden(sK2(X4,X6),X6) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~r2_hidden(X5,k2_relat_1(X4))) )),
% 3.72/1.03    inference(subsumption_resolution,[],[f99,f49])).
% 3.72/1.03  fof(f99,plain,(
% 3.72/1.03    ( ! [X6,X4,X5] : (sK2(X4,X6) != X5 | k2_relat_1(X4) = X6 | ~r2_hidden(sK4(X4,X5),k1_relat_1(X4)) | ~r2_hidden(sK2(X4,X6),X6) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~r2_hidden(X5,k2_relat_1(X4))) )),
% 3.72/1.03    inference(duplicate_literal_removal,[],[f96])).
% 3.72/1.03  fof(f96,plain,(
% 3.72/1.03    ( ! [X6,X4,X5] : (sK2(X4,X6) != X5 | k2_relat_1(X4) = X6 | ~r2_hidden(sK4(X4,X5),k1_relat_1(X4)) | ~r2_hidden(sK2(X4,X6),X6) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~r2_hidden(X5,k2_relat_1(X4)) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) )),
% 3.72/1.03    inference(superposition,[],[f37,f48])).
% 3.72/1.03  fof(f37,plain,(
% 3.72/1.03    ( ! [X0,X3,X1] : (k1_funct_1(X0,X3) != sK2(X0,X1) | k2_relat_1(X0) = X1 | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(sK2(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.72/1.03    inference(cnf_transformation,[],[f24])).
% 3.72/1.03  fof(f4118,plain,(
% 3.72/1.03    spl7_66 | ~spl7_10 | ~spl7_13 | ~spl7_23 | ~spl7_72),
% 3.72/1.03    inference(avatar_split_clause,[],[f4117,f3070,f770,f315,f294,f2526])).
% 3.72/1.03  fof(f2526,plain,(
% 3.72/1.03    spl7_66 <=> ! [X0] : r2_hidden(X0,k1_xboole_0)),
% 3.72/1.03    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).
% 3.72/1.03  fof(f770,plain,(
% 3.72/1.03    spl7_23 <=> ! [X178,X177] : (sK0 != X177 | r2_hidden(X178,k2_relat_1(sK6(X177,X178))))),
% 3.72/1.03    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 3.72/1.03  fof(f4117,plain,(
% 3.72/1.03    ( ! [X41] : (r2_hidden(X41,k1_xboole_0)) ) | (~spl7_10 | ~spl7_13 | ~spl7_23 | ~spl7_72)),
% 3.72/1.03    inference(subsumption_resolution,[],[f4104,f316])).
% 3.72/1.03  fof(f316,plain,(
% 3.72/1.03    ( ! [X2] : (k1_xboole_0 != k1_tarski(X2)) ) | ~spl7_13),
% 3.72/1.03    inference(avatar_component_clause,[],[f315])).
% 3.72/1.03  fof(f4104,plain,(
% 3.72/1.03    ( ! [X41] : (k1_xboole_0 = k1_tarski(sK1) | r2_hidden(X41,k1_xboole_0)) ) | (~spl7_10 | ~spl7_13 | ~spl7_23 | ~spl7_72)),
% 3.72/1.03    inference(superposition,[],[f3629,f4075])).
% 3.72/1.03  fof(f4075,plain,(
% 3.72/1.03    ( ! [X61] : (k1_xboole_0 = k2_relat_1(sK6(sK0,X61))) ) | (~spl7_10 | ~spl7_23)),
% 3.72/1.03    inference(subsumption_resolution,[],[f4061,f295])).
% 3.72/1.03  fof(f295,plain,(
% 3.72/1.03    ( ! [X52,X51] : (~r2_hidden(X52,k1_tarski(X51))) ) | ~spl7_10),
% 3.72/1.03    inference(avatar_component_clause,[],[f294])).
% 3.72/1.03  fof(f4061,plain,(
% 3.72/1.03    ( ! [X61] : (r2_hidden(X61,k1_tarski(X61)) | k1_xboole_0 = k2_relat_1(sK6(sK0,X61))) ) | ~spl7_23),
% 3.72/1.03    inference(superposition,[],[f3508,f255])).
% 3.72/1.03  fof(f255,plain,(
% 3.72/1.03    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK6(X0,X1)) | k1_xboole_0 = k2_relat_1(sK6(X0,X1))) )),
% 3.72/1.03    inference(equality_resolution,[],[f186])).
% 3.72/1.03  fof(f186,plain,(
% 3.72/1.03    ( ! [X2,X0,X1] : (X1 != X2 | k1_xboole_0 = k2_relat_1(sK6(X0,X1)) | k2_relat_1(sK6(X0,X1)) = k1_tarski(X2)) )),
% 3.72/1.03    inference(duplicate_literal_removal,[],[f183])).
% 3.72/1.03  fof(f183,plain,(
% 3.72/1.03    ( ! [X2,X0,X1] : (X1 != X2 | k1_xboole_0 = k2_relat_1(sK6(X0,X1)) | k2_relat_1(sK6(X0,X1)) = k1_tarski(X2) | k1_xboole_0 = k2_relat_1(sK6(X0,X1)) | k2_relat_1(sK6(X0,X1)) = k1_tarski(X2)) )),
% 3.72/1.03    inference(superposition,[],[f39,f79])).
% 3.72/1.03  fof(f79,plain,(
% 3.72/1.03    ( ! [X12,X10,X11] : (sK5(k2_relat_1(sK6(X11,X10)),X12) = X10 | k1_xboole_0 = k2_relat_1(sK6(X11,X10)) | k2_relat_1(sK6(X11,X10)) = k1_tarski(X12)) )),
% 3.72/1.03    inference(resolution,[],[f69,f38])).
% 3.72/1.03  fof(f39,plain,(
% 3.72/1.03    ( ! [X0,X1] : (sK5(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 3.72/1.03    inference(cnf_transformation,[],[f26])).
% 3.72/1.03  fof(f3508,plain,(
% 3.72/1.03    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK6(sK0,X0)))) ) | ~spl7_23),
% 3.72/1.03    inference(equality_resolution,[],[f771])).
% 3.72/1.03  fof(f771,plain,(
% 3.72/1.03    ( ! [X177,X178] : (sK0 != X177 | r2_hidden(X178,k2_relat_1(sK6(X177,X178)))) ) | ~spl7_23),
% 3.72/1.03    inference(avatar_component_clause,[],[f770])).
% 3.72/1.03  fof(f3629,plain,(
% 3.72/1.03    ( ! [X28,X29] : (k1_tarski(sK1) = k2_relat_1(sK6(X28,X29)) | r2_hidden(X29,k2_relat_1(sK6(X28,X29)))) ) | (~spl7_13 | ~spl7_72)),
% 3.72/1.03    inference(subsumption_resolution,[],[f3628,f3071])).
% 3.72/1.03  fof(f3628,plain,(
% 3.72/1.03    ( ! [X28,X29] : (r2_hidden(X29,k2_relat_1(sK6(X28,X29))) | k1_tarski(sK1) = k2_relat_1(sK6(X28,X29)) | r2_hidden(X29,k1_tarski(sK1))) ) | (~spl7_13 | ~spl7_72)),
% 3.72/1.03    inference(subsumption_resolution,[],[f3627,f41])).
% 3.72/1.03  fof(f3627,plain,(
% 3.72/1.03    ( ! [X28,X29] : (r2_hidden(X29,k2_relat_1(sK6(X28,X29))) | ~v1_relat_1(sK6(X28,X29)) | k1_tarski(sK1) = k2_relat_1(sK6(X28,X29)) | r2_hidden(X29,k1_tarski(sK1))) ) | (~spl7_13 | ~spl7_72)),
% 3.72/1.03    inference(subsumption_resolution,[],[f3613,f42])).
% 3.72/1.03  fof(f3613,plain,(
% 3.72/1.03    ( ! [X28,X29] : (r2_hidden(X29,k2_relat_1(sK6(X28,X29))) | ~v1_funct_1(sK6(X28,X29)) | ~v1_relat_1(sK6(X28,X29)) | k1_tarski(sK1) = k2_relat_1(sK6(X28,X29)) | r2_hidden(X29,k1_tarski(sK1))) ) | (~spl7_13 | ~spl7_72)),
% 3.72/1.03    inference(duplicate_literal_removal,[],[f3612])).
% 3.72/1.03  fof(f3612,plain,(
% 3.72/1.03    ( ! [X28,X29] : (r2_hidden(X29,k2_relat_1(sK6(X28,X29))) | ~v1_funct_1(sK6(X28,X29)) | ~v1_relat_1(sK6(X28,X29)) | k1_tarski(sK1) = k2_relat_1(sK6(X28,X29)) | r2_hidden(X29,k1_tarski(sK1)) | k1_tarski(sK1) = k2_relat_1(sK6(X28,X29))) ) | (~spl7_13 | ~spl7_72)),
% 3.72/1.03    inference(superposition,[],[f94,f3393])).
% 3.72/1.03  fof(f3393,plain,(
% 3.72/1.03    ( ! [X14,X15] : (sK2(sK6(X14,X15),k1_tarski(sK1)) = X15 | k1_tarski(sK1) = k2_relat_1(sK6(X14,X15))) ) | (~spl7_13 | ~spl7_72)),
% 3.72/1.03    inference(subsumption_resolution,[],[f3370,f3071])).
% 3.72/1.03  fof(f3370,plain,(
% 3.72/1.03    ( ! [X14,X15,X13] : (sK2(sK6(X14,X15),k1_tarski(sK1)) = X15 | k1_tarski(sK1) = k2_relat_1(sK6(X14,X15)) | r2_hidden(X13,k1_tarski(sK1))) ) | (~spl7_13 | ~spl7_72)),
% 3.72/1.03    inference(superposition,[],[f350,f3093])).
% 3.72/1.03  fof(f3093,plain,(
% 3.72/1.03    ( ! [X0,X1] : (k1_tarski(sK1) = k2_relat_1(sK6(k1_tarski(X0),X1))) ) | (~spl7_13 | ~spl7_72)),
% 3.72/1.03    inference(backward_demodulation,[],[f106,f3090])).
% 3.72/1.03  fof(f3090,plain,(
% 3.72/1.03    ( ! [X9] : (k1_tarski(sK1) = k1_tarski(X9)) ) | (~spl7_13 | ~spl7_72)),
% 3.72/1.03    inference(subsumption_resolution,[],[f3089,f316])).
% 3.72/1.03  fof(f3089,plain,(
% 3.72/1.03    ( ! [X9] : (k1_xboole_0 = k1_tarski(sK1) | k1_tarski(sK1) = k1_tarski(X9)) ) | ~spl7_72),
% 3.72/1.03    inference(resolution,[],[f3071,f38])).
% 3.72/1.03  fof(f350,plain,(
% 3.72/1.03    ( ! [X2,X0,X3,X1] : (sK2(sK6(X0,X1),k2_relat_1(sK6(X2,X3))) = X1 | k2_relat_1(sK6(X0,X1)) = k2_relat_1(sK6(X2,X3)) | r2_hidden(X3,k2_relat_1(sK6(X2,X3)))) )),
% 3.72/1.03    inference(subsumption_resolution,[],[f214,f205])).
% 3.72/1.03  fof(f214,plain,(
% 3.72/1.03    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,k2_relat_1(sK6(X2,X3))) | k2_relat_1(sK6(X0,X1)) = k2_relat_1(sK6(X2,X3)) | X1 = X3 | sK2(sK6(X0,X1),k2_relat_1(sK6(X2,X3))) = X1) )),
% 3.72/1.03    inference(duplicate_literal_removal,[],[f196])).
% 3.72/1.03  fof(f196,plain,(
% 3.72/1.03    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,k2_relat_1(sK6(X2,X3))) | k2_relat_1(sK6(X0,X1)) = k2_relat_1(sK6(X2,X3)) | X1 = X3 | sK2(sK6(X0,X1),k2_relat_1(sK6(X2,X3))) = X1 | k2_relat_1(sK6(X0,X1)) = k2_relat_1(sK6(X2,X3))) )),
% 3.72/1.03    inference(superposition,[],[f155,f156])).
% 3.72/1.03  fof(f94,plain,(
% 3.72/1.03    ( ! [X4,X3] : (r2_hidden(sK2(X3,X4),k2_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | k2_relat_1(X3) = X4 | r2_hidden(sK2(X3,X4),X4)) )),
% 3.72/1.03    inference(subsumption_resolution,[],[f89,f35])).
% 3.72/1.03  fof(f89,plain,(
% 3.72/1.03    ( ! [X4,X3] : (r2_hidden(sK2(X3,X4),k2_relat_1(X3)) | ~r2_hidden(sK3(X3,X4),k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | k2_relat_1(X3) = X4 | r2_hidden(sK2(X3,X4),X4)) )),
% 3.72/1.03    inference(duplicate_literal_removal,[],[f88])).
% 3.72/1.03  fof(f88,plain,(
% 3.72/1.03    ( ! [X4,X3] : (r2_hidden(sK2(X3,X4),k2_relat_1(X3)) | ~r2_hidden(sK3(X3,X4),k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | k2_relat_1(X3) = X4 | r2_hidden(sK2(X3,X4),X4) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 3.72/1.03    inference(superposition,[],[f47,f36])).
% 3.72/1.03  fof(f47,plain,(
% 3.72/1.03    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.72/1.03    inference(equality_resolution,[],[f46])).
% 3.72/1.03  fof(f46,plain,(
% 3.72/1.03    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.72/1.03    inference(equality_resolution,[],[f34])).
% 3.72/1.03  fof(f34,plain,(
% 3.72/1.03    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.72/1.03    inference(cnf_transformation,[],[f24])).
% 3.72/1.03  fof(f3507,plain,(
% 3.72/1.03    ~spl7_13 | ~spl7_22 | ~spl7_72),
% 3.72/1.03    inference(avatar_contradiction_clause,[],[f3506])).
% 3.72/1.03  fof(f3506,plain,(
% 3.72/1.03    $false | (~spl7_13 | ~spl7_22 | ~spl7_72)),
% 3.72/1.03    inference(subsumption_resolution,[],[f3504,f3071])).
% 3.72/1.03  fof(f3504,plain,(
% 3.72/1.03    ( ! [X5] : (r2_hidden(X5,k1_tarski(sK1))) ) | (~spl7_13 | ~spl7_22 | ~spl7_72)),
% 3.72/1.03    inference(trivial_inequality_removal,[],[f3503])).
% 3.72/1.03  fof(f3503,plain,(
% 3.72/1.03    ( ! [X5] : (k1_tarski(sK1) != k1_tarski(sK1) | r2_hidden(X5,k1_tarski(sK1))) ) | (~spl7_13 | ~spl7_22 | ~spl7_72)),
% 3.72/1.03    inference(superposition,[],[f768,f3093])).
% 3.72/1.03  fof(f768,plain,(
% 3.72/1.03    ( ! [X180,X179] : (k1_tarski(sK1) != k2_relat_1(sK6(X179,X180)) | r2_hidden(X180,k2_relat_1(sK6(X179,X180)))) ) | ~spl7_22),
% 3.72/1.03    inference(avatar_component_clause,[],[f767])).
% 3.72/1.03  fof(f767,plain,(
% 3.72/1.03    spl7_22 <=> ! [X179,X180] : (k1_tarski(sK1) != k2_relat_1(sK6(X179,X180)) | r2_hidden(X180,k2_relat_1(sK6(X179,X180))))),
% 3.72/1.03    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 3.72/1.03  fof(f2850,plain,(
% 3.72/1.03    spl7_66 | ~spl7_24 | ~spl7_32),
% 3.72/1.03    inference(avatar_split_clause,[],[f2828,f1105,f962,f2526])).
% 3.72/1.03  fof(f962,plain,(
% 3.72/1.03    spl7_24 <=> ! [X77,X76] : r2_hidden(X77,k2_relat_1(sK6(X76,X77)))),
% 3.72/1.03    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 3.72/1.03  fof(f1105,plain,(
% 3.72/1.03    spl7_32 <=> ! [X50,X54] : k1_xboole_0 = k2_relat_1(sK6(X54,X50))),
% 3.72/1.03    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 3.72/1.03  fof(f2828,plain,(
% 3.72/1.03    ( ! [X77] : (r2_hidden(X77,k1_xboole_0)) ) | (~spl7_24 | ~spl7_32)),
% 3.72/1.03    inference(backward_demodulation,[],[f963,f1106])).
% 3.72/1.03  fof(f1106,plain,(
% 3.72/1.03    ( ! [X54,X50] : (k1_xboole_0 = k2_relat_1(sK6(X54,X50))) ) | ~spl7_32),
% 3.72/1.03    inference(avatar_component_clause,[],[f1105])).
% 3.72/1.03  fof(f963,plain,(
% 3.72/1.03    ( ! [X76,X77] : (r2_hidden(X77,k2_relat_1(sK6(X76,X77)))) ) | ~spl7_24),
% 3.72/1.03    inference(avatar_component_clause,[],[f962])).
% 3.72/1.03  fof(f2804,plain,(
% 3.72/1.03    spl7_32 | ~spl7_2 | ~spl7_24),
% 3.72/1.03    inference(avatar_split_clause,[],[f2803,f962,f124,f1105])).
% 3.72/1.03  fof(f2803,plain,(
% 3.72/1.03    ( ! [X8,X9] : (k1_xboole_0 = k2_relat_1(sK6(X8,X9))) ) | (~spl7_2 | ~spl7_24)),
% 3.72/1.03    inference(subsumption_resolution,[],[f2801,f125])).
% 3.72/1.03  fof(f125,plain,(
% 3.72/1.03    ( ! [X0] : (~r2_hidden(X0,k1_tarski(X0))) ) | ~spl7_2),
% 3.72/1.03    inference(avatar_component_clause,[],[f124])).
% 3.72/1.03  fof(f2801,plain,(
% 3.72/1.03    ( ! [X8,X9] : (r2_hidden(X9,k1_tarski(X9)) | k1_xboole_0 = k2_relat_1(sK6(X8,X9))) ) | ~spl7_24),
% 3.72/1.03    inference(superposition,[],[f963,f255])).
% 3.72/1.03  fof(f2610,plain,(
% 3.72/1.03    spl7_1 | ~spl7_47 | ~spl7_66),
% 3.72/1.03    inference(avatar_contradiction_clause,[],[f2606])).
% 3.72/1.03  fof(f2606,plain,(
% 3.72/1.03    $false | (spl7_1 | ~spl7_47 | ~spl7_66)),
% 3.72/1.03    inference(unit_resulting_resolution,[],[f53,f2527,f2527,f1993])).
% 3.72/1.03  fof(f1993,plain,(
% 3.72/1.03    ( ! [X8,X7] : (~r2_hidden(X8,k1_xboole_0) | ~r2_hidden(X7,k1_xboole_0) | X7 = X8) ) | ~spl7_47),
% 3.72/1.03    inference(avatar_component_clause,[],[f1992])).
% 3.72/1.03  fof(f1992,plain,(
% 3.72/1.03    spl7_47 <=> ! [X7,X8] : (~r2_hidden(X8,k1_xboole_0) | ~r2_hidden(X7,k1_xboole_0) | X7 = X8)),
% 3.72/1.03    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).
% 3.72/1.03  fof(f2527,plain,(
% 3.72/1.03    ( ! [X0] : (r2_hidden(X0,k1_xboole_0)) ) | ~spl7_66),
% 3.72/1.03    inference(avatar_component_clause,[],[f2526])).
% 3.72/1.03  fof(f53,plain,(
% 3.72/1.03    k1_xboole_0 != sK0 | spl7_1),
% 3.72/1.03    inference(avatar_component_clause,[],[f51])).
% 3.72/1.03  fof(f51,plain,(
% 3.72/1.03    spl7_1 <=> k1_xboole_0 = sK0),
% 3.72/1.03    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 3.72/1.03  fof(f2588,plain,(
% 3.72/1.03    spl7_66 | ~spl7_2 | ~spl7_23),
% 3.72/1.03    inference(avatar_split_clause,[],[f2500,f770,f124,f2526])).
% 3.72/1.03  fof(f2500,plain,(
% 3.72/1.03    ( ! [X0] : (r2_hidden(X0,k1_xboole_0)) ) | (~spl7_2 | ~spl7_23)),
% 3.72/1.03    inference(backward_demodulation,[],[f1395,f2475])).
% 3.72/1.03  fof(f2475,plain,(
% 3.72/1.03    ( ! [X0] : (k1_xboole_0 = k2_relat_1(sK6(sK0,X0))) ) | (~spl7_2 | ~spl7_23)),
% 3.72/1.03    inference(subsumption_resolution,[],[f2448,f125])).
% 3.72/1.03  fof(f2448,plain,(
% 3.72/1.03    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0)) | k1_xboole_0 = k2_relat_1(sK6(sK0,X0))) ) | ~spl7_23),
% 3.72/1.03    inference(superposition,[],[f1395,f255])).
% 3.72/1.03  fof(f1395,plain,(
% 3.72/1.03    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK6(sK0,X0)))) ) | ~spl7_23),
% 3.72/1.03    inference(equality_resolution,[],[f771])).
% 3.72/1.03  fof(f2285,plain,(
% 3.72/1.03    spl7_18 | spl7_47 | ~spl7_14 | ~spl7_16),
% 3.72/1.03    inference(avatar_split_clause,[],[f2260,f628,f561,f1992,f637])).
% 3.72/1.03  fof(f637,plain,(
% 3.72/1.03    spl7_18 <=> ! [X19] : ~r2_hidden(X19,k1_xboole_0)),
% 3.72/1.03    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 3.72/1.03  fof(f2260,plain,(
% 3.72/1.03    ( ! [X2,X3,X1] : (~r2_hidden(X1,k1_xboole_0) | X1 = X2 | ~r2_hidden(X2,k1_xboole_0) | ~r2_hidden(X3,k1_xboole_0)) ) | (~spl7_14 | ~spl7_16)),
% 3.72/1.03    inference(superposition,[],[f673,f1540])).
% 3.72/1.03  fof(f1540,plain,(
% 3.72/1.03    ( ! [X0,X1] : (k1_xboole_0 = k2_relat_1(sK6(X0,sK1)) | ~r2_hidden(X1,X0)) ) | (~spl7_14 | ~spl7_16)),
% 3.72/1.03    inference(subsumption_resolution,[],[f1539,f630])).
% 3.72/1.03  fof(f1539,plain,(
% 3.72/1.03    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k1_xboole_0 = k2_relat_1(sK6(X0,sK1)) | ~r2_hidden(sK1,k1_xboole_0)) ) | ~spl7_14),
% 3.72/1.03    inference(trivial_inequality_removal,[],[f1538])).
% 3.72/1.03  fof(f1538,plain,(
% 3.72/1.03    ( ! [X0,X1] : (sK1 != sK1 | ~r2_hidden(X1,X0) | k1_xboole_0 = k2_relat_1(sK6(X0,sK1)) | ~r2_hidden(sK1,k1_xboole_0)) ) | ~spl7_14),
% 3.72/1.03    inference(duplicate_literal_removal,[],[f1522])).
% 3.72/1.03  fof(f1522,plain,(
% 3.72/1.03    ( ! [X0,X1] : (sK1 != sK1 | ~r2_hidden(X1,X0) | k1_xboole_0 = k2_relat_1(sK6(X0,sK1)) | ~r2_hidden(sK1,k1_xboole_0) | k1_xboole_0 = k2_relat_1(sK6(X0,sK1))) ) | ~spl7_14),
% 3.72/1.03    inference(superposition,[],[f103,f617])).
% 3.72/1.03  fof(f103,plain,(
% 3.72/1.03    ( ! [X2,X0,X3,X1] : (sK2(sK6(X0,X1),X3) != X1 | ~r2_hidden(X2,X0) | k2_relat_1(sK6(X0,X1)) = X3 | ~r2_hidden(sK2(sK6(X0,X1),X3),X3)) )),
% 3.72/1.03    inference(duplicate_literal_removal,[],[f102])).
% 3.72/1.03  fof(f102,plain,(
% 3.72/1.03    ( ! [X2,X0,X3,X1] : (~r2_hidden(X2,X0) | sK2(sK6(X0,X1),X3) != X1 | k2_relat_1(sK6(X0,X1)) = X3 | ~r2_hidden(sK2(sK6(X0,X1),X3),X3) | ~r2_hidden(X2,X0)) )),
% 3.72/1.03    inference(forward_demodulation,[],[f101,f43])).
% 3.72/1.03  fof(f101,plain,(
% 3.72/1.03    ( ! [X2,X0,X3,X1] : (sK2(sK6(X0,X1),X3) != X1 | k2_relat_1(sK6(X0,X1)) = X3 | ~r2_hidden(X2,k1_relat_1(sK6(X0,X1))) | ~r2_hidden(sK2(sK6(X0,X1),X3),X3) | ~r2_hidden(X2,X0)) )),
% 3.72/1.03    inference(subsumption_resolution,[],[f100,f41])).
% 3.72/1.03  fof(f100,plain,(
% 3.72/1.03    ( ! [X2,X0,X3,X1] : (sK2(sK6(X0,X1),X3) != X1 | k2_relat_1(sK6(X0,X1)) = X3 | ~r2_hidden(X2,k1_relat_1(sK6(X0,X1))) | ~r2_hidden(sK2(sK6(X0,X1),X3),X3) | ~v1_relat_1(sK6(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 3.72/1.03    inference(subsumption_resolution,[],[f95,f42])).
% 3.72/1.03  fof(f95,plain,(
% 3.72/1.03    ( ! [X2,X0,X3,X1] : (sK2(sK6(X0,X1),X3) != X1 | k2_relat_1(sK6(X0,X1)) = X3 | ~r2_hidden(X2,k1_relat_1(sK6(X0,X1))) | ~r2_hidden(sK2(sK6(X0,X1),X3),X3) | ~v1_funct_1(sK6(X0,X1)) | ~v1_relat_1(sK6(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 3.72/1.03    inference(superposition,[],[f37,f44])).
% 3.72/1.03  fof(f673,plain,(
% 3.72/1.03    ( ! [X6,X7,X5] : (~r2_hidden(X7,k2_relat_1(sK6(k1_xboole_0,X6))) | X5 = X7 | ~r2_hidden(X5,k2_relat_1(sK6(k1_xboole_0,X6)))) ) | ~spl7_14),
% 3.72/1.03    inference(superposition,[],[f257,f563])).
% 3.72/1.03  fof(f257,plain,(
% 3.72/1.03    ( ! [X6,X4,X8,X7,X5] : (~r2_hidden(X8,k2_relat_1(sK6(k2_relat_1(sK6(X4,X5)),X6))) | X7 = X8 | ~r2_hidden(X7,k2_relat_1(sK6(k2_relat_1(sK6(X4,X5)),X6)))) )),
% 3.72/1.03    inference(superposition,[],[f174,f174])).
% 3.72/1.03  fof(f174,plain,(
% 3.72/1.03    ( ! [X6,X4,X7,X5] : (k1_funct_1(sK6(k2_relat_1(sK6(X4,X5)),X6),X5) = X7 | ~r2_hidden(X7,k2_relat_1(sK6(k2_relat_1(sK6(X4,X5)),X6)))) )),
% 3.72/1.03    inference(subsumption_resolution,[],[f173,f41])).
% 3.72/1.03  fof(f173,plain,(
% 3.72/1.03    ( ! [X6,X4,X7,X5] : (k1_funct_1(sK6(k2_relat_1(sK6(X4,X5)),X6),X5) = X7 | ~r2_hidden(X7,k2_relat_1(sK6(k2_relat_1(sK6(X4,X5)),X6))) | ~v1_relat_1(sK6(k2_relat_1(sK6(X4,X5)),X6))) )),
% 3.72/1.03    inference(subsumption_resolution,[],[f167,f42])).
% 3.72/1.03  fof(f167,plain,(
% 3.72/1.03    ( ! [X6,X4,X7,X5] : (k1_funct_1(sK6(k2_relat_1(sK6(X4,X5)),X6),X5) = X7 | ~r2_hidden(X7,k2_relat_1(sK6(k2_relat_1(sK6(X4,X5)),X6))) | ~v1_funct_1(sK6(k2_relat_1(sK6(X4,X5)),X6)) | ~v1_relat_1(sK6(k2_relat_1(sK6(X4,X5)),X6))) )),
% 3.72/1.03    inference(duplicate_literal_removal,[],[f164])).
% 3.72/1.03  fof(f164,plain,(
% 3.72/1.03    ( ! [X6,X4,X7,X5] : (k1_funct_1(sK6(k2_relat_1(sK6(X4,X5)),X6),X5) = X7 | ~r2_hidden(X7,k2_relat_1(sK6(k2_relat_1(sK6(X4,X5)),X6))) | ~v1_funct_1(sK6(k2_relat_1(sK6(X4,X5)),X6)) | ~v1_relat_1(sK6(k2_relat_1(sK6(X4,X5)),X6)) | ~r2_hidden(X7,k2_relat_1(sK6(k2_relat_1(sK6(X4,X5)),X6)))) )),
% 3.72/1.03    inference(superposition,[],[f48,f78])).
% 3.72/1.03  fof(f78,plain,(
% 3.72/1.03    ( ! [X6,X8,X7,X9] : (sK4(sK6(k2_relat_1(sK6(X7,X6)),X8),X9) = X6 | ~r2_hidden(X9,k2_relat_1(sK6(k2_relat_1(sK6(X7,X6)),X8)))) )),
% 3.72/1.03    inference(resolution,[],[f69,f62])).
% 3.72/1.03  fof(f1367,plain,(
% 3.72/1.03    spl7_22 | spl7_23),
% 3.72/1.03    inference(avatar_split_clause,[],[f1366,f770,f767])).
% 3.72/1.03  fof(f1366,plain,(
% 3.72/1.03    ( ! [X6,X4,X7,X5] : (sK0 != X4 | k1_tarski(sK1) != k2_relat_1(sK6(X6,X7)) | r2_hidden(X7,k2_relat_1(sK6(X6,X7))) | r2_hidden(X5,k2_relat_1(sK6(X4,X5)))) )),
% 3.72/1.03    inference(forward_demodulation,[],[f1365,f43])).
% 3.72/1.03  fof(f1365,plain,(
% 3.72/1.03    ( ! [X6,X4,X7,X5] : (k1_tarski(sK1) != k2_relat_1(sK6(X6,X7)) | sK0 != k1_relat_1(sK6(X4,X5)) | r2_hidden(X7,k2_relat_1(sK6(X6,X7))) | r2_hidden(X5,k2_relat_1(sK6(X4,X5)))) )),
% 3.72/1.03    inference(subsumption_resolution,[],[f1364,f41])).
% 3.72/1.03  fof(f1364,plain,(
% 3.72/1.03    ( ! [X6,X4,X7,X5] : (k1_tarski(sK1) != k2_relat_1(sK6(X6,X7)) | sK0 != k1_relat_1(sK6(X4,X5)) | ~v1_relat_1(sK6(X4,X5)) | r2_hidden(X7,k2_relat_1(sK6(X6,X7))) | r2_hidden(X5,k2_relat_1(sK6(X4,X5)))) )),
% 3.72/1.03    inference(subsumption_resolution,[],[f1358,f42])).
% 3.72/1.03  fof(f1358,plain,(
% 3.72/1.03    ( ! [X6,X4,X7,X5] : (k1_tarski(sK1) != k2_relat_1(sK6(X6,X7)) | sK0 != k1_relat_1(sK6(X4,X5)) | ~v1_funct_1(sK6(X4,X5)) | ~v1_relat_1(sK6(X4,X5)) | r2_hidden(X7,k2_relat_1(sK6(X6,X7))) | r2_hidden(X5,k2_relat_1(sK6(X4,X5)))) )),
% 3.72/1.03    inference(superposition,[],[f30,f383])).
% 3.72/1.03  fof(f383,plain,(
% 3.72/1.03    ( ! [X39,X37,X38,X40] : (k2_relat_1(sK6(X39,X40)) = k2_relat_1(sK6(X37,X38)) | r2_hidden(X38,k2_relat_1(sK6(X37,X38))) | r2_hidden(X40,k2_relat_1(sK6(X39,X40)))) )),
% 3.72/1.03    inference(subsumption_resolution,[],[f382,f228])).
% 3.72/1.03  fof(f228,plain,(
% 3.72/1.03    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_relat_1(sK6(X1,X0))) | r2_hidden(X0,k2_relat_1(sK6(X1,X0)))) )),
% 3.72/1.03    inference(resolution,[],[f168,f59])).
% 3.72/1.03  fof(f59,plain,(
% 3.72/1.03    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(sK6(X0,X1))) | ~r2_hidden(X2,X0)) )),
% 3.72/1.03    inference(duplicate_literal_removal,[],[f58])).
% 3.72/1.03  fof(f58,plain,(
% 3.72/1.03    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X1,k2_relat_1(sK6(X0,X1))) | ~r2_hidden(X2,X0)) )),
% 3.72/1.03    inference(forward_demodulation,[],[f57,f43])).
% 3.72/1.03  fof(f57,plain,(
% 3.72/1.03    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(sK6(X0,X1))) | ~r2_hidden(X2,k1_relat_1(sK6(X0,X1))) | ~r2_hidden(X2,X0)) )),
% 3.72/1.03    inference(subsumption_resolution,[],[f56,f41])).
% 3.72/1.03  fof(f56,plain,(
% 3.72/1.03    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(sK6(X0,X1))) | ~r2_hidden(X2,k1_relat_1(sK6(X0,X1))) | ~v1_relat_1(sK6(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 3.72/1.03    inference(subsumption_resolution,[],[f55,f42])).
% 3.72/1.03  fof(f55,plain,(
% 3.72/1.03    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(sK6(X0,X1))) | ~r2_hidden(X2,k1_relat_1(sK6(X0,X1))) | ~v1_funct_1(sK6(X0,X1)) | ~v1_relat_1(sK6(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 3.72/1.03    inference(superposition,[],[f47,f44])).
% 3.72/1.03  fof(f168,plain,(
% 3.72/1.03    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,k2_relat_1(sK6(k2_relat_1(sK6(X0,X1)),X2))) | r2_hidden(X1,k2_relat_1(sK6(X0,X1)))) )),
% 3.72/1.03    inference(duplicate_literal_removal,[],[f163])).
% 3.72/1.03  fof(f163,plain,(
% 3.72/1.03    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,k2_relat_1(sK6(X0,X1))) | ~r2_hidden(X3,k2_relat_1(sK6(k2_relat_1(sK6(X0,X1)),X2))) | ~r2_hidden(X3,k2_relat_1(sK6(k2_relat_1(sK6(X0,X1)),X2)))) )),
% 3.72/1.03    inference(superposition,[],[f62,f78])).
% 3.72/1.03  fof(f382,plain,(
% 3.72/1.03    ( ! [X39,X37,X38,X40] : (r2_hidden(X38,k2_relat_1(sK6(X37,X38))) | k2_relat_1(sK6(X39,X40)) = k2_relat_1(sK6(X37,X38)) | r2_hidden(X38,k2_relat_1(sK6(X39,X40))) | r2_hidden(X40,k2_relat_1(sK6(X39,X40)))) )),
% 3.72/1.03    inference(subsumption_resolution,[],[f381,f41])).
% 3.72/1.03  fof(f381,plain,(
% 3.72/1.03    ( ! [X39,X37,X38,X40] : (r2_hidden(X38,k2_relat_1(sK6(X37,X38))) | ~v1_relat_1(sK6(X37,X38)) | k2_relat_1(sK6(X39,X40)) = k2_relat_1(sK6(X37,X38)) | r2_hidden(X38,k2_relat_1(sK6(X39,X40))) | r2_hidden(X40,k2_relat_1(sK6(X39,X40)))) )),
% 3.72/1.03    inference(subsumption_resolution,[],[f368,f42])).
% 3.72/1.03  fof(f368,plain,(
% 3.72/1.03    ( ! [X39,X37,X38,X40] : (r2_hidden(X38,k2_relat_1(sK6(X37,X38))) | ~v1_funct_1(sK6(X37,X38)) | ~v1_relat_1(sK6(X37,X38)) | k2_relat_1(sK6(X39,X40)) = k2_relat_1(sK6(X37,X38)) | r2_hidden(X38,k2_relat_1(sK6(X39,X40))) | r2_hidden(X40,k2_relat_1(sK6(X39,X40)))) )),
% 3.72/1.03    inference(duplicate_literal_removal,[],[f365])).
% 3.72/1.03  fof(f365,plain,(
% 3.72/1.03    ( ! [X39,X37,X38,X40] : (r2_hidden(X38,k2_relat_1(sK6(X37,X38))) | ~v1_funct_1(sK6(X37,X38)) | ~v1_relat_1(sK6(X37,X38)) | k2_relat_1(sK6(X39,X40)) = k2_relat_1(sK6(X37,X38)) | r2_hidden(X38,k2_relat_1(sK6(X39,X40))) | k2_relat_1(sK6(X39,X40)) = k2_relat_1(sK6(X37,X38)) | r2_hidden(X40,k2_relat_1(sK6(X39,X40)))) )),
% 3.72/1.03    inference(superposition,[],[f94,f350])).
% 3.72/1.03  fof(f1356,plain,(
% 3.72/1.03    spl7_15 | spl7_16 | ~spl7_14),
% 3.72/1.03    inference(avatar_split_clause,[],[f898,f561,f628,f625])).
% 3.72/1.03  fof(f625,plain,(
% 3.72/1.03    spl7_15 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 3.72/1.03    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 3.72/1.03  fof(f898,plain,(
% 3.72/1.03    ( ! [X0] : (r2_hidden(sK1,k1_xboole_0) | ~r2_hidden(X0,sK0)) ) | ~spl7_14),
% 3.72/1.03    inference(duplicate_literal_removal,[],[f895])).
% 3.72/1.03  fof(f895,plain,(
% 3.72/1.03    ( ! [X0] : (r2_hidden(sK1,k1_xboole_0) | ~r2_hidden(X0,sK0) | ~r2_hidden(X0,sK0)) ) | ~spl7_14),
% 3.72/1.03    inference(superposition,[],[f654,f44])).
% 3.72/1.03  fof(f654,plain,(
% 3.72/1.03    ( ! [X30] : (r2_hidden(k1_funct_1(sK6(sK0,sK1),X30),k1_xboole_0) | ~r2_hidden(X30,sK0)) ) | ~spl7_14),
% 3.72/1.03    inference(forward_demodulation,[],[f653,f43])).
% 3.72/1.03  fof(f653,plain,(
% 3.72/1.03    ( ! [X30] : (r2_hidden(k1_funct_1(sK6(sK0,sK1),X30),k1_xboole_0) | ~r2_hidden(X30,k1_relat_1(sK6(sK0,sK1)))) ) | ~spl7_14),
% 3.72/1.03    inference(subsumption_resolution,[],[f652,f41])).
% 3.72/1.03  fof(f652,plain,(
% 3.72/1.03    ( ! [X30] : (r2_hidden(k1_funct_1(sK6(sK0,sK1),X30),k1_xboole_0) | ~r2_hidden(X30,k1_relat_1(sK6(sK0,sK1))) | ~v1_relat_1(sK6(sK0,sK1))) ) | ~spl7_14),
% 3.72/1.03    inference(subsumption_resolution,[],[f622,f42])).
% 3.72/1.03  fof(f622,plain,(
% 3.72/1.03    ( ! [X30] : (r2_hidden(k1_funct_1(sK6(sK0,sK1),X30),k1_xboole_0) | ~r2_hidden(X30,k1_relat_1(sK6(sK0,sK1))) | ~v1_funct_1(sK6(sK0,sK1)) | ~v1_relat_1(sK6(sK0,sK1))) ) | ~spl7_14),
% 3.72/1.03    inference(superposition,[],[f47,f563])).
% 3.72/1.03  fof(f1333,plain,(
% 3.72/1.03    spl7_1 | ~spl7_14 | ~spl7_15),
% 3.72/1.03    inference(avatar_contradiction_clause,[],[f1332])).
% 3.72/1.03  fof(f1332,plain,(
% 3.72/1.03    $false | (spl7_1 | ~spl7_14 | ~spl7_15)),
% 3.72/1.03    inference(subsumption_resolution,[],[f1315,f53])).
% 3.72/1.03  fof(f1315,plain,(
% 3.72/1.03    k1_xboole_0 = sK0 | (spl7_1 | ~spl7_14 | ~spl7_15)),
% 3.72/1.03    inference(superposition,[],[f1278,f563])).
% 3.72/1.03  fof(f1278,plain,(
% 3.72/1.03    ( ! [X1] : (sK0 = k2_relat_1(sK6(sK0,X1))) ) | (spl7_1 | ~spl7_15)),
% 3.72/1.03    inference(forward_demodulation,[],[f1268,f1215])).
% 3.72/1.03  fof(f1215,plain,(
% 3.72/1.03    ( ! [X7] : (sK0 = k1_tarski(X7)) ) | (spl7_1 | ~spl7_15)),
% 3.72/1.03    inference(subsumption_resolution,[],[f1214,f53])).
% 3.72/1.03  fof(f1214,plain,(
% 3.72/1.03    ( ! [X7] : (k1_xboole_0 = sK0 | sK0 = k1_tarski(X7)) ) | ~spl7_15),
% 3.72/1.03    inference(resolution,[],[f626,f38])).
% 3.72/1.03  fof(f626,plain,(
% 3.72/1.03    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl7_15),
% 3.72/1.03    inference(avatar_component_clause,[],[f625])).
% 3.72/1.03  fof(f1268,plain,(
% 3.72/1.03    ( ! [X0,X1] : (k2_relat_1(sK6(sK0,X1)) = k1_tarski(k1_funct_1(sK6(sK0,X1),X0))) ) | (spl7_1 | ~spl7_15)),
% 3.72/1.03    inference(backward_demodulation,[],[f106,f1215])).
% 3.72/1.03  fof(f995,plain,(
% 3.72/1.03    spl7_15 | ~spl7_14 | ~spl7_18),
% 3.72/1.03    inference(avatar_split_clause,[],[f975,f637,f561,f625])).
% 3.72/1.03  fof(f975,plain,(
% 3.72/1.03    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | (~spl7_14 | ~spl7_18)),
% 3.72/1.03    inference(resolution,[],[f638,f654])).
% 3.72/1.03  fof(f638,plain,(
% 3.72/1.03    ( ! [X19] : (~r2_hidden(X19,k1_xboole_0)) ) | ~spl7_18),
% 3.72/1.03    inference(avatar_component_clause,[],[f637])).
% 3.72/1.03  fof(f966,plain,(
% 3.72/1.03    spl7_24 | spl7_18 | ~spl7_2 | ~spl7_22),
% 3.72/1.03    inference(avatar_split_clause,[],[f954,f767,f124,f637,f962])).
% 3.72/1.03  fof(f954,plain,(
% 3.72/1.03    ( ! [X88,X85,X86] : (~r2_hidden(X88,k1_xboole_0) | r2_hidden(X86,k2_relat_1(sK6(X85,X86)))) ) | (~spl7_2 | ~spl7_22)),
% 3.72/1.03    inference(superposition,[],[f234,f916])).
% 3.72/1.03  fof(f916,plain,(
% 3.72/1.03    ( ! [X0] : (k1_xboole_0 = k2_relat_1(sK6(X0,sK1))) ) | (~spl7_2 | ~spl7_22)),
% 3.72/1.03    inference(equality_resolution,[],[f913])).
% 3.72/1.03  fof(f913,plain,(
% 3.72/1.03    ( ! [X17,X16] : (k1_tarski(sK1) != k1_tarski(X17) | k1_xboole_0 = k2_relat_1(sK6(X16,X17))) ) | (~spl7_2 | ~spl7_22)),
% 3.72/1.03    inference(subsumption_resolution,[],[f911,f125])).
% 3.72/1.03  fof(f911,plain,(
% 3.72/1.03    ( ! [X17,X16] : (k1_tarski(sK1) != k1_tarski(X17) | r2_hidden(X17,k1_tarski(X17)) | k1_xboole_0 = k2_relat_1(sK6(X16,X17))) ) | ~spl7_22),
% 3.72/1.03    inference(superposition,[],[f768,f255])).
% 3.72/1.03  fof(f234,plain,(
% 3.72/1.03    ( ! [X30,X28,X31,X29,X27] : (~r2_hidden(X29,k2_relat_1(sK6(k2_relat_1(sK6(k2_relat_1(sK6(X28,X27)),X30)),X31))) | r2_hidden(X27,k2_relat_1(sK6(X28,X27)))) )),
% 3.72/1.03    inference(resolution,[],[f168,f62])).
% 3.72/1.03  fof(f564,plain,(
% 3.72/1.03    spl7_14),
% 3.72/1.03    inference(avatar_split_clause,[],[f559,f561])).
% 3.72/1.03  fof(f559,plain,(
% 3.72/1.03    k1_xboole_0 = k2_relat_1(sK6(sK0,sK1))),
% 3.72/1.03    inference(equality_resolution,[],[f558])).
% 3.72/1.03  fof(f558,plain,(
% 3.72/1.03    ( ! [X0] : (sK0 != X0 | k1_xboole_0 = k2_relat_1(sK6(X0,sK1))) )),
% 3.72/1.03    inference(equality_resolution,[],[f537])).
% 3.72/1.03  fof(f537,plain,(
% 3.72/1.03    ( ! [X0,X1] : (k1_tarski(X1) != k1_tarski(sK1) | sK0 != X0 | k1_xboole_0 = k2_relat_1(sK6(X0,X1))) )),
% 3.72/1.03    inference(superposition,[],[f536,f43])).
% 3.72/1.03  fof(f536,plain,(
% 3.72/1.03    ( ! [X83,X84] : (sK0 != k1_relat_1(sK6(X83,X84)) | k1_tarski(sK1) != k1_tarski(X84) | k1_xboole_0 = k2_relat_1(sK6(X83,X84))) )),
% 3.72/1.03    inference(subsumption_resolution,[],[f535,f41])).
% 3.72/1.03  fof(f535,plain,(
% 3.72/1.03    ( ! [X83,X84] : (k1_tarski(sK1) != k1_tarski(X84) | sK0 != k1_relat_1(sK6(X83,X84)) | ~v1_relat_1(sK6(X83,X84)) | k1_xboole_0 = k2_relat_1(sK6(X83,X84))) )),
% 3.72/1.03    inference(subsumption_resolution,[],[f521,f42])).
% 3.72/1.03  fof(f521,plain,(
% 3.72/1.03    ( ! [X83,X84] : (k1_tarski(sK1) != k1_tarski(X84) | sK0 != k1_relat_1(sK6(X83,X84)) | ~v1_funct_1(sK6(X83,X84)) | ~v1_relat_1(sK6(X83,X84)) | k1_xboole_0 = k2_relat_1(sK6(X83,X84))) )),
% 3.72/1.03    inference(superposition,[],[f30,f255])).
% 3.72/1.03  fof(f54,plain,(
% 3.72/1.03    ~spl7_1),
% 3.72/1.03    inference(avatar_split_clause,[],[f29,f51])).
% 3.72/1.03  fof(f29,plain,(
% 3.72/1.03    k1_xboole_0 != sK0),
% 3.72/1.03    inference(cnf_transformation,[],[f18])).
% 3.72/1.03  % SZS output end Proof for theBenchmark
% 3.72/1.03  % (24013)------------------------------
% 3.72/1.03  % (24013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.72/1.03  % (24013)Termination reason: Refutation
% 3.72/1.03  
% 3.72/1.03  % (24013)Memory used [KB]: 8571
% 3.72/1.03  % (24013)Time elapsed: 0.453 s
% 3.72/1.03  % (24013)------------------------------
% 3.72/1.03  % (24013)------------------------------
% 3.72/1.03  % (23942)Success in time 0.68 s
%------------------------------------------------------------------------------
