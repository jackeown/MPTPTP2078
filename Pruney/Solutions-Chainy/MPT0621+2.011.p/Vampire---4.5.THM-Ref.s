%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 113 expanded)
%              Number of leaves         :   18 (  37 expanded)
%              Depth                    :   17
%              Number of atoms          :  285 ( 506 expanded)
%              Number of equality atoms :  115 ( 208 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f198,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f127,f193,f197])).

fof(f197,plain,(
    spl9_7 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | spl9_7 ),
    inference(subsumption_resolution,[],[f49,f195])).

fof(f195,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | spl9_7 ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(X0) )
    | spl9_7 ),
    inference(superposition,[],[f148,f36])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f148,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl9_7 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl9_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f49,plain,(
    v1_xboole_0(sK8) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    v1_xboole_0(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f2,f31])).

fof(f31,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK8) ),
    introduced(choice_axiom,[])).

fof(f2,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f193,plain,
    ( ~ spl9_7
    | ~ spl9_1 ),
    inference(avatar_split_clause,[],[f192,f81,f146])).

fof(f81,plain,
    ( spl9_1
  <=> k1_xboole_0 = np__1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f192,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl9_1 ),
    inference(backward_demodulation,[],[f35,f83])).

fof(f83,plain,
    ( k1_xboole_0 = np__1
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f35,plain,(
    ~ v1_xboole_0(np__1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ~ v1_xboole_0(np__1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',spc1_boole)).

fof(f127,plain,(
    ~ spl9_2 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | ~ spl9_2 ),
    inference(trivial_inequality_removal,[],[f110])).

fof(f110,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK0 != sK0
    | ~ spl9_2 ),
    inference(superposition,[],[f34,f97])).

fof(f97,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | sK0 != X0 )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f96,f94])).

fof(f94,plain,
    ( ! [X0] :
        ( sK0 != X0
        | v1_relat_1(X0) )
    | ~ spl9_2 ),
    inference(resolution,[],[f86,f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK3(X0)
          & r2_hidden(sK3(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK4(X4),sK5(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f23,f25,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK3(X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK4(X4),sK5(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f86,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | sK0 != X0 )
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl9_2
  <=> ! [X1,X0] :
        ( sK0 != X0
        | ~ r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f96,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_relat_1(X0)
        | sK0 != X0 )
    | ~ spl9_2 ),
    inference(resolution,[],[f37,f86])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
     => r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

fof(f34,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f18])).

fof(f18,plain,
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

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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

fof(f93,plain,
    ( spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f92,f85,f81])).

fof(f92,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | k1_xboole_0 = np__1
      | ~ r2_hidden(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | k1_xboole_0 = np__1
      | ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(condensation,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X0
      | k1_xboole_0 = np__1
      | ~ r2_hidden(X1,X2)
      | sK0 != X2
      | ~ r2_hidden(X1,X0) ) ),
    inference(forward_demodulation,[],[f89,f47])).

fof(f47,plain,(
    ! [X0] : k1_relat_1(sK7(X0)) = X0 ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X2] :
          ( np__1 = k1_funct_1(sK7(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK7(X0)) = X0
      & v1_funct_1(sK7(X0))
      & v1_relat_1(sK7(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f17,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_funct_1(X1,X2) = np__1
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( np__1 = k1_funct_1(sK7(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK7(X0)) = X0
        & v1_funct_1(sK7(X0))
        & v1_relat_1(sK7(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = np__1 )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = np__1
      | ~ r2_hidden(X1,X2)
      | sK0 != X2
      | sK0 != k1_relat_1(sK7(X0))
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f88,f45])).

fof(f45,plain,(
    ! [X0] : v1_relat_1(sK7(X0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = np__1
      | ~ r2_hidden(X1,X2)
      | sK0 != X2
      | sK0 != k1_relat_1(sK7(X0))
      | ~ v1_relat_1(sK7(X0))
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f74,f46])).

fof(f46,plain,(
    ! [X0] : v1_funct_1(sK7(X0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = np__1
      | ~ r2_hidden(X1,X2)
      | sK0 != X2
      | sK0 != k1_relat_1(sK7(X0))
      | ~ v1_funct_1(sK7(X0))
      | ~ v1_relat_1(sK7(X0))
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f71,f48])).

fof(f48,plain,(
    ! [X2,X0] :
      ( np__1 = k1_funct_1(sK7(X0),X2)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,X0)
      | sK0 != X0
      | k1_relat_1(X1) != sK0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f44,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( sK6(X0) = X1
      | sK0 != X0
      | k1_relat_1(X1) != sK0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f53,f41])).

fof(f41,plain,(
    ! [X0] : v1_relat_1(sK6(X0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK6(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK6(X0)) = X0
      & v1_funct_1(sK6(X0))
      & v1_relat_1(sK6(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f16,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK6(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK6(X0)) = X0
        & v1_funct_1(sK6(X0))
        & v1_relat_1(sK6(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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

fof(f53,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK6(X0) = X1
      | k1_relat_1(X1) != sK0
      | ~ v1_relat_1(sK6(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f51,f42])).

fof(f42,plain,(
    ! [X0] : v1_funct_1(sK6(X0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK6(X0) = X1
      | k1_relat_1(X1) != sK0
      | ~ v1_funct_1(sK6(X0))
      | ~ v1_relat_1(sK6(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f33,f43])).

fof(f43,plain,(
    ! [X0] : k1_relat_1(sK6(X0)) = X0 ),
    inference(cnf_transformation,[],[f28])).

fof(f33,plain,(
    ! [X2,X1] :
      ( k1_relat_1(X2) != sK0
      | X1 = X2
      | k1_relat_1(X1) != sK0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = k1_funct_1(sK6(X0),X2)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:28:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (27906)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.50  % (27912)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.50  % (27913)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.50  % (27908)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (27921)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.51  % (27908)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f198,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f93,f127,f193,f197])).
% 0.22/0.51  fof(f197,plain,(
% 0.22/0.51    spl9_7),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f196])).
% 0.22/0.51  fof(f196,plain,(
% 0.22/0.51    $false | spl9_7),
% 0.22/0.51    inference(subsumption_resolution,[],[f49,f195])).
% 0.22/0.51  fof(f195,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_xboole_0(X0)) ) | spl9_7),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f194])).
% 0.22/0.51  fof(f194,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_xboole_0(X0) | ~v1_xboole_0(X0)) ) | spl9_7),
% 0.22/0.51    inference(superposition,[],[f148,f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    ~v1_xboole_0(k1_xboole_0) | spl9_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f146])).
% 0.22/0.51  fof(f146,plain,(
% 0.22/0.51    spl9_7 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    v1_xboole_0(sK8)),
% 0.22/0.51    inference(cnf_transformation,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    v1_xboole_0(sK8)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f2,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK8)),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ? [X0] : v1_xboole_0(X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.22/0.51  fof(f193,plain,(
% 0.22/0.51    ~spl9_7 | ~spl9_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f192,f81,f146])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    spl9_1 <=> k1_xboole_0 = np__1),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.22/0.51  fof(f192,plain,(
% 0.22/0.51    ~v1_xboole_0(k1_xboole_0) | ~spl9_1),
% 0.22/0.51    inference(backward_demodulation,[],[f35,f83])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    k1_xboole_0 = np__1 | ~spl9_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f81])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ~v1_xboole_0(np__1)),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ~v1_xboole_0(np__1)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',spc1_boole)).
% 0.22/0.51  fof(f127,plain,(
% 0.22/0.51    ~spl9_2),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f126])).
% 0.22/0.51  fof(f126,plain,(
% 0.22/0.51    $false | ~spl9_2),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f110])).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    k1_xboole_0 != k1_xboole_0 | sK0 != sK0 | ~spl9_2),
% 0.22/0.51    inference(superposition,[],[f34,f97])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = X0 | sK0 != X0) ) | ~spl9_2),
% 0.22/0.51    inference(subsumption_resolution,[],[f96,f94])).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    ( ! [X0] : (sK0 != X0 | v1_relat_1(X0)) ) | ~spl9_2),
% 0.22/0.51    inference(resolution,[],[f86,f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK3(X0) & r2_hidden(sK3(X0),X0))) & (! [X4] : (k4_tarski(sK4(X4),sK5(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f23,f25,f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK3(X0) & r2_hidden(sK3(X0),X0)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK4(X4),sK5(X4)) = X4)),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(rectify,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(nnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | sK0 != X0) ) | ~spl9_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f85])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    spl9_2 <=> ! [X1,X0] : (sK0 != X0 | ~r2_hidden(X1,X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_relat_1(X0) | sK0 != X0) ) | ~spl9_2),
% 0.22/0.51    inference(resolution,[],[f37,f86])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : (? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) => r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    k1_xboole_0 != sK0),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.51    inference(flattening,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,negated_conjecture,(
% 0.22/0.51    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.22/0.51    inference(negated_conjecture,[],[f8])).
% 0.22/0.51  fof(f8,conjecture,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    spl9_1 | spl9_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f92,f85,f81])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    ( ! [X0,X1] : (sK0 != X0 | k1_xboole_0 = np__1 | ~r2_hidden(X1,X0)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f91])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    ( ! [X0,X1] : (sK0 != X0 | k1_xboole_0 = np__1 | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X0)) )),
% 0.22/0.51    inference(condensation,[],[f90])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (sK0 != X0 | k1_xboole_0 = np__1 | ~r2_hidden(X1,X2) | sK0 != X2 | ~r2_hidden(X1,X0)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f89,f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ( ! [X0] : (k1_relat_1(sK7(X0)) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0] : (! [X2] : (np__1 = k1_funct_1(sK7(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK7(X0)) = X0 & v1_funct_1(sK7(X0)) & v1_relat_1(sK7(X0)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f17,f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0] : (? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (np__1 = k1_funct_1(sK7(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK7(X0)) = X0 & v1_funct_1(sK7(X0)) & v1_relat_1(sK7(X0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : ? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = np__1) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_xboole_0 = np__1 | ~r2_hidden(X1,X2) | sK0 != X2 | sK0 != k1_relat_1(sK7(X0)) | ~r2_hidden(X1,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f88,f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ( ! [X0] : (v1_relat_1(sK7(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_xboole_0 = np__1 | ~r2_hidden(X1,X2) | sK0 != X2 | sK0 != k1_relat_1(sK7(X0)) | ~v1_relat_1(sK7(X0)) | ~r2_hidden(X1,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f74,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X0] : (v1_funct_1(sK7(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_xboole_0 = np__1 | ~r2_hidden(X1,X2) | sK0 != X2 | sK0 != k1_relat_1(sK7(X0)) | ~v1_funct_1(sK7(X0)) | ~v1_relat_1(sK7(X0)) | ~r2_hidden(X1,X0)) )),
% 0.22/0.51    inference(superposition,[],[f71,f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ( ! [X2,X0] : (np__1 = k1_funct_1(sK7(X0),X2) | ~r2_hidden(X2,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0) | sK0 != X0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(superposition,[],[f44,f54])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ( ! [X0,X1] : (sK6(X0) = X1 | sK0 != X0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f53,f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ( ! [X0] : (v1_relat_1(sK6(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK6(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK6(X0)) = X0 & v1_funct_1(sK6(X0)) & v1_relat_1(sK6(X0)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f16,f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK6(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK6(X0)) = X0 & v1_funct_1(sK6(X0)) & v1_relat_1(sK6(X0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X0,X1] : (sK0 != X0 | sK6(X0) = X1 | k1_relat_1(X1) != sK0 | ~v1_relat_1(sK6(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f51,f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X0] : (v1_funct_1(sK6(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ( ! [X0,X1] : (sK0 != X0 | sK6(X0) = X1 | k1_relat_1(X1) != sK0 | ~v1_funct_1(sK6(X0)) | ~v1_relat_1(sK6(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(superposition,[],[f33,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ( ! [X0] : (k1_relat_1(sK6(X0)) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X2,X1] : (k1_relat_1(X2) != sK0 | X1 = X2 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X2,X0] : (k1_xboole_0 = k1_funct_1(sK6(X0),X2) | ~r2_hidden(X2,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (27908)------------------------------
% 0.22/0.51  % (27908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (27908)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (27908)Memory used [KB]: 6140
% 0.22/0.51  % (27908)Time elapsed: 0.094 s
% 0.22/0.51  % (27908)------------------------------
% 0.22/0.51  % (27908)------------------------------
% 0.22/0.51  % (27905)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (27922)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (27905)Refutation not found, incomplete strategy% (27905)------------------------------
% 0.22/0.51  % (27905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (27905)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (27905)Memory used [KB]: 10618
% 0.22/0.51  % (27905)Time elapsed: 0.082 s
% 0.22/0.51  % (27905)------------------------------
% 0.22/0.51  % (27905)------------------------------
% 0.22/0.51  % (27904)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (27904)Refutation not found, incomplete strategy% (27904)------------------------------
% 0.22/0.51  % (27904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (27904)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (27904)Memory used [KB]: 10490
% 0.22/0.51  % (27904)Time elapsed: 0.091 s
% 0.22/0.51  % (27904)------------------------------
% 0.22/0.51  % (27904)------------------------------
% 0.22/0.52  % (27915)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (27909)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (27915)Refutation not found, incomplete strategy% (27915)------------------------------
% 0.22/0.52  % (27915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (27915)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (27915)Memory used [KB]: 10490
% 0.22/0.52  % (27915)Time elapsed: 0.095 s
% 0.22/0.52  % (27915)------------------------------
% 0.22/0.52  % (27915)------------------------------
% 0.22/0.52  % (27926)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (27909)Refutation not found, incomplete strategy% (27909)------------------------------
% 0.22/0.52  % (27909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (27909)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (27909)Memory used [KB]: 6140
% 0.22/0.52  % (27909)Time elapsed: 0.093 s
% 0.22/0.52  % (27909)------------------------------
% 0.22/0.52  % (27909)------------------------------
% 0.22/0.52  % (27914)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (27920)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.52  % (27928)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.28/0.52  % (27924)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.28/0.53  % (27929)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.28/0.53  % (27917)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.28/0.53  % (27917)Refutation not found, incomplete strategy% (27917)------------------------------
% 1.28/0.53  % (27917)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (27917)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  
% 1.28/0.53  % (27917)Memory used [KB]: 6012
% 1.28/0.53  % (27917)Time elapsed: 0.114 s
% 1.28/0.53  % (27917)------------------------------
% 1.28/0.53  % (27917)------------------------------
% 1.28/0.53  % (27918)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.28/0.53  % (27916)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.28/0.53  % (27911)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.28/0.53  % (27903)Success in time 0.159 s
%------------------------------------------------------------------------------
