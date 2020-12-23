%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 372 expanded)
%              Number of leaves         :   18 ( 124 expanded)
%              Depth                    :   25
%              Number of atoms          :  457 (2032 expanded)
%              Number of equality atoms :  193 ( 834 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f817,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f346,f492,f685,f695,f790])).

fof(f790,plain,
    ( spl8_1
    | ~ spl8_12 ),
    inference(avatar_contradiction_clause,[],[f789])).

fof(f789,plain,
    ( $false
    | spl8_1
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f763,f464])).

fof(f464,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f463])).

fof(f463,plain,
    ( spl8_12
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f763,plain,
    ( ! [X3] : r2_hidden(X3,sK0)
    | spl8_1
    | ~ spl8_12 ),
    inference(backward_demodulation,[],[f56,f718])).

fof(f718,plain,
    ( ! [X11] : sK0 = k1_tarski(X11)
    | spl8_1
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f716,f61])).

fof(f61,plain,
    ( k1_xboole_0 != sK0
    | spl8_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl8_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f716,plain,
    ( ! [X11] :
        ( k1_xboole_0 = sK0
        | sK0 = k1_tarski(X11) )
    | ~ spl8_12 ),
    inference(resolution,[],[f464,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( sK5(X0,X1) != X1
        & r2_hidden(sK5(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f12,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK5(X0,X1) != X1
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f56,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f25,plain,(
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

fof(f695,plain,
    ( spl8_12
    | spl8_13
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f572,f343,f466,f463])).

fof(f466,plain,
    ( spl8_13
  <=> r2_hidden(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f343,plain,
    ( spl8_2
  <=> k1_xboole_0 = k2_relat_1(sK7(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f572,plain,
    ( ! [X0] :
        ( r2_hidden(sK1,k1_xboole_0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_2 ),
    inference(duplicate_literal_removal,[],[f569])).

fof(f569,plain,
    ( ! [X0] :
        ( r2_hidden(sK1,k1_xboole_0)
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_2 ),
    inference(superposition,[],[f484,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK7(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK7(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK7(X0,X1)) = X0
      & v1_funct_1(sK7(X0,X1))
      & v1_relat_1(sK7(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f13,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK7(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK7(X0,X1)) = X0
        & v1_funct_1(sK7(X0,X1))
        & v1_relat_1(sK7(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
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

fof(f484,plain,
    ( ! [X19] :
        ( r2_hidden(k1_funct_1(sK7(sK0,sK1),X19),k1_xboole_0)
        | ~ r2_hidden(X19,sK0) )
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f483,f48])).

fof(f48,plain,(
    ! [X0,X1] : k1_relat_1(sK7(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f30])).

fof(f483,plain,
    ( ! [X19] :
        ( r2_hidden(k1_funct_1(sK7(sK0,sK1),X19),k1_xboole_0)
        | ~ r2_hidden(X19,k1_relat_1(sK7(sK0,sK1))) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f482,f46])).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(sK7(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f482,plain,
    ( ! [X19] :
        ( r2_hidden(k1_funct_1(sK7(sK0,sK1),X19),k1_xboole_0)
        | ~ r2_hidden(X19,k1_relat_1(sK7(sK0,sK1)))
        | ~ v1_relat_1(sK7(sK0,sK1)) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f460,f47])).

fof(f47,plain,(
    ! [X0,X1] : v1_funct_1(sK7(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f460,plain,
    ( ! [X19] :
        ( r2_hidden(k1_funct_1(sK7(sK0,sK1),X19),k1_xboole_0)
        | ~ r2_hidden(X19,k1_relat_1(sK7(sK0,sK1)))
        | ~ v1_funct_1(sK7(sK0,sK1))
        | ~ v1_relat_1(sK7(sK0,sK1)) )
    | ~ spl8_2 ),
    inference(superposition,[],[f52,f345])).

fof(f345,plain,
    ( k1_xboole_0 = k2_relat_1(sK7(sK0,sK1))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f343])).

fof(f52,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f18,f21,f20,f19])).

fof(f19,plain,(
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

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK2(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f17,plain,(
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

fof(f685,plain,
    ( ~ spl8_2
    | ~ spl8_13
    | spl8_16 ),
    inference(avatar_contradiction_clause,[],[f684])).

fof(f684,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_13
    | spl8_16 ),
    inference(subsumption_resolution,[],[f682,f468])).

fof(f468,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f466])).

fof(f682,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | ~ spl8_2
    | ~ spl8_13
    | spl8_16 ),
    inference(trivial_inequality_removal,[],[f681])).

fof(f681,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK1,k1_xboole_0)
    | ~ spl8_2
    | ~ spl8_13
    | spl8_16 ),
    inference(superposition,[],[f491,f627])).

fof(f627,plain,
    ( ! [X0] :
        ( k1_tarski(X0) = k1_xboole_0
        | ~ r2_hidden(X0,k1_xboole_0) )
    | ~ spl8_2
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f626,f446])).

fof(f446,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | sK1 = X1 )
    | ~ spl8_2 ),
    inference(superposition,[],[f111,f345])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_relat_1(sK7(X0,X1)))
      | X1 = X2 ) ),
    inference(subsumption_resolution,[],[f79,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(sK7(X0,X1),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(sK7(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f72,f46])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(sK7(X0,X1),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(sK7(X0,X1)))
      | ~ v1_relat_1(sK7(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f71,f47])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(sK7(X0,X1),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(sK7(X0,X1)))
      | ~ v1_funct_1(sK7(X0,X1))
      | ~ v1_relat_1(sK7(X0,X1)) ) ),
    inference(superposition,[],[f54,f48])).

fof(f54,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(X2,k2_relat_1(sK7(X0,X1)))
      | ~ r2_hidden(sK4(sK7(X0,X1),X2),X0) ) ),
    inference(subsumption_resolution,[],[f78,f46])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(X2,k2_relat_1(sK7(X0,X1)))
      | ~ v1_relat_1(sK7(X0,X1))
      | ~ r2_hidden(sK4(sK7(X0,X1),X2),X0) ) ),
    inference(subsumption_resolution,[],[f74,f47])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(X2,k2_relat_1(sK7(X0,X1)))
      | ~ v1_funct_1(sK7(X0,X1))
      | ~ v1_relat_1(sK7(X0,X1))
      | ~ r2_hidden(sK4(sK7(X0,X1),X2),X0) ) ),
    inference(superposition,[],[f53,f49])).

fof(f53,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f626,plain,
    ( ! [X0] :
        ( sK1 != X0
        | k1_tarski(X0) = k1_xboole_0
        | ~ r2_hidden(X0,k1_xboole_0) )
    | ~ spl8_2
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f625,f468])).

fof(f625,plain,
    ( ! [X0] :
        ( sK1 != X0
        | k1_tarski(X0) = k1_xboole_0
        | ~ r2_hidden(sK1,k1_xboole_0)
        | ~ r2_hidden(X0,k1_xboole_0) )
    | ~ spl8_2 ),
    inference(duplicate_literal_removal,[],[f622])).

fof(f622,plain,
    ( ! [X0] :
        ( sK1 != X0
        | k1_tarski(X0) = k1_xboole_0
        | ~ r2_hidden(sK1,k1_xboole_0)
        | ~ r2_hidden(X0,k1_xboole_0)
        | k1_tarski(X0) = k1_xboole_0 )
    | ~ spl8_2 ),
    inference(superposition,[],[f44,f456])).

fof(f456,plain,
    ( ! [X16] :
        ( sK1 = sK6(X16,k1_xboole_0)
        | ~ r2_hidden(X16,k1_xboole_0)
        | k1_xboole_0 = k1_tarski(X16) )
    | ~ spl8_2 ),
    inference(superposition,[],[f221,f345])).

fof(f221,plain,(
    ! [X2,X0,X1] :
      ( sK6(X0,k2_relat_1(sK7(X1,X2))) = X2
      | ~ r2_hidden(X0,k2_relat_1(sK7(X1,X2)))
      | k1_tarski(X0) = k2_relat_1(sK7(X1,X2)) ) ),
    inference(trivial_inequality_removal,[],[f220])).

fof(f220,plain,(
    ! [X2,X0,X1] :
      ( X0 != X0
      | k1_tarski(X0) = k2_relat_1(sK7(X1,X2))
      | ~ r2_hidden(X0,k2_relat_1(sK7(X1,X2)))
      | sK6(X0,k2_relat_1(sK7(X1,X2))) = X2 ) ),
    inference(duplicate_literal_removal,[],[f217])).

fof(f217,plain,(
    ! [X2,X0,X1] :
      ( X0 != X0
      | k1_tarski(X0) = k2_relat_1(sK7(X1,X2))
      | ~ r2_hidden(X0,k2_relat_1(sK7(X1,X2)))
      | sK6(X0,k2_relat_1(sK7(X1,X2))) = X2
      | k1_tarski(X0) = k2_relat_1(sK7(X1,X2)) ) ),
    inference(superposition,[],[f44,f116])).

fof(f116,plain,(
    ! [X14,X15,X13] :
      ( sK6(X14,k2_relat_1(sK7(X15,X13))) = X14
      | sK6(X14,k2_relat_1(sK7(X15,X13))) = X13
      | k2_relat_1(sK7(X15,X13)) = k1_tarski(X14) ) ),
    inference(resolution,[],[f111,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | sK6(X0,X1) = X0
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    ! [X0,X1] :
      ( sK6(X0,X1) != X0
      | k1_tarski(X0) = X1
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f491,plain,
    ( k1_xboole_0 != k1_tarski(sK1)
    | spl8_16 ),
    inference(avatar_component_clause,[],[f489])).

fof(f489,plain,
    ( spl8_16
  <=> k1_xboole_0 = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f492,plain,
    ( ~ spl8_16
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f487,f343,f489])).

fof(f487,plain,
    ( k1_xboole_0 != k1_tarski(sK1)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f486,f46])).

fof(f486,plain,
    ( k1_xboole_0 != k1_tarski(sK1)
    | ~ v1_relat_1(sK7(sK0,sK1))
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f485,f47])).

fof(f485,plain,
    ( k1_xboole_0 != k1_tarski(sK1)
    | ~ v1_funct_1(sK7(sK0,sK1))
    | ~ v1_relat_1(sK7(sK0,sK1))
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f461,f48])).

fof(f461,plain,
    ( k1_xboole_0 != k1_tarski(sK1)
    | sK0 != k1_relat_1(sK7(sK0,sK1))
    | ~ v1_funct_1(sK7(sK0,sK1))
    | ~ v1_relat_1(sK7(sK0,sK1))
    | ~ spl8_2 ),
    inference(superposition,[],[f32,f345])).

fof(f32,plain,(
    ! [X2] :
      ( k2_relat_1(X2) != k1_tarski(sK1)
      | k1_relat_1(X2) != sK0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ! [X2] :
        ( k2_relat_1(X2) != k1_tarski(sK1)
        | k1_relat_1(X2) != sK0
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f15,f14])).

fof(f14,plain,
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

fof(f15,plain,
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

fof(f346,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f341,f343])).

fof(f341,plain,(
    k1_xboole_0 = k2_relat_1(sK7(sK0,sK1)) ),
    inference(equality_resolution,[],[f333])).

fof(f333,plain,(
    ! [X0] :
      ( sK0 != X0
      | k1_xboole_0 = k2_relat_1(sK7(X0,sK1)) ) ),
    inference(equality_resolution,[],[f331])).

fof(f331,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) != k1_tarski(sK1)
      | sK0 != X0
      | k1_xboole_0 = k2_relat_1(sK7(X0,X1)) ) ),
    inference(superposition,[],[f285,f48])).

fof(f285,plain,(
    ! [X41,X40] :
      ( sK0 != k1_relat_1(sK7(X40,X41))
      | k1_tarski(sK1) != k1_tarski(X41)
      | k1_xboole_0 = k2_relat_1(sK7(X40,X41)) ) ),
    inference(subsumption_resolution,[],[f284,f46])).

fof(f284,plain,(
    ! [X41,X40] :
      ( k1_tarski(sK1) != k1_tarski(X41)
      | sK0 != k1_relat_1(sK7(X40,X41))
      | ~ v1_relat_1(sK7(X40,X41))
      | k1_xboole_0 = k2_relat_1(sK7(X40,X41)) ) ),
    inference(subsumption_resolution,[],[f275,f47])).

fof(f275,plain,(
    ! [X41,X40] :
      ( k1_tarski(sK1) != k1_tarski(X41)
      | sK0 != k1_relat_1(sK7(X40,X41))
      | ~ v1_funct_1(sK7(X40,X41))
      | ~ v1_relat_1(sK7(X40,X41))
      | k1_xboole_0 = k2_relat_1(sK7(X40,X41)) ) ),
    inference(superposition,[],[f32,f229])).

fof(f229,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK7(X0,X1))
      | k1_xboole_0 = k2_relat_1(sK7(X0,X1)) ) ),
    inference(equality_resolution,[],[f216])).

fof(f216,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | k1_xboole_0 = k2_relat_1(sK7(X0,X1))
      | k2_relat_1(sK7(X0,X1)) = k1_tarski(X2) ) ),
    inference(duplicate_literal_removal,[],[f213])).

fof(f213,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | k1_xboole_0 = k2_relat_1(sK7(X0,X1))
      | k2_relat_1(sK7(X0,X1)) = k1_tarski(X2)
      | k1_xboole_0 = k2_relat_1(sK7(X0,X1))
      | k2_relat_1(sK7(X0,X1)) = k1_tarski(X2) ) ),
    inference(superposition,[],[f40,f115])).

fof(f115,plain,(
    ! [X12,X10,X11] :
      ( sK5(k2_relat_1(sK7(X11,X10)),X12) = X10
      | k1_xboole_0 = k2_relat_1(sK7(X11,X10))
      | k2_relat_1(sK7(X11,X10)) = k1_tarski(X12) ) ),
    inference(resolution,[],[f111,f39])).

fof(f40,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f31,f59])).

fof(f31,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:47:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (14651)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (14647)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.51  % (14650)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (14649)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.51  % (14648)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.51  % (14647)Refutation not found, incomplete strategy% (14647)------------------------------
% 0.22/0.51  % (14647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (14647)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (14647)Memory used [KB]: 1663
% 0.22/0.51  % (14647)Time elapsed: 0.107 s
% 0.22/0.51  % (14647)------------------------------
% 0.22/0.51  % (14647)------------------------------
% 0.22/0.51  % (14672)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (14659)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.52  % (14667)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.52  % (14660)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.52  % (14646)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (14664)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.52  % (14664)Refutation not found, incomplete strategy% (14664)------------------------------
% 0.22/0.52  % (14664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (14664)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (14664)Memory used [KB]: 1663
% 0.22/0.52  % (14664)Time elapsed: 0.113 s
% 0.22/0.52  % (14664)------------------------------
% 0.22/0.52  % (14664)------------------------------
% 0.22/0.52  % (14674)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.52  % (14673)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.52  % (14656)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (14668)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (14666)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.53  % (14665)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.53  % (14652)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (14657)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (14658)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.54  % (14653)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (14655)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.54  % (14660)Refutation not found, incomplete strategy% (14660)------------------------------
% 0.22/0.54  % (14660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (14660)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (14660)Memory used [KB]: 1663
% 0.22/0.54  % (14660)Time elapsed: 0.099 s
% 0.22/0.54  % (14660)------------------------------
% 0.22/0.54  % (14660)------------------------------
% 0.22/0.54  % (14657)Refutation not found, incomplete strategy% (14657)------------------------------
% 0.22/0.54  % (14657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (14657)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (14657)Memory used [KB]: 6268
% 0.22/0.54  % (14657)Time elapsed: 0.134 s
% 0.22/0.54  % (14657)------------------------------
% 0.22/0.54  % (14657)------------------------------
% 0.22/0.54  % (14672)Refutation not found, incomplete strategy% (14672)------------------------------
% 0.22/0.54  % (14672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (14672)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (14672)Memory used [KB]: 6140
% 0.22/0.54  % (14672)Time elapsed: 0.121 s
% 0.22/0.54  % (14672)------------------------------
% 0.22/0.54  % (14672)------------------------------
% 0.22/0.54  % (14662)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (14662)Refutation not found, incomplete strategy% (14662)------------------------------
% 0.22/0.54  % (14662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (14662)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (14662)Memory used [KB]: 10618
% 0.22/0.54  % (14662)Time elapsed: 0.127 s
% 0.22/0.54  % (14662)------------------------------
% 0.22/0.54  % (14662)------------------------------
% 0.22/0.54  % (14654)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.54  % (14670)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (14673)Refutation not found, incomplete strategy% (14673)------------------------------
% 0.22/0.54  % (14673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (14673)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (14673)Memory used [KB]: 6140
% 0.22/0.54  % (14673)Time elapsed: 0.143 s
% 0.22/0.54  % (14673)------------------------------
% 0.22/0.54  % (14673)------------------------------
% 0.22/0.54  % (14669)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (14671)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (14676)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (14671)Refutation not found, incomplete strategy% (14671)------------------------------
% 0.22/0.55  % (14671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (14671)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (14671)Memory used [KB]: 6268
% 0.22/0.55  % (14671)Time elapsed: 0.140 s
% 0.22/0.55  % (14671)------------------------------
% 0.22/0.55  % (14671)------------------------------
% 0.22/0.55  % (14663)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (14676)Refutation not found, incomplete strategy% (14676)------------------------------
% 0.22/0.55  % (14676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (14676)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (14676)Memory used [KB]: 1663
% 0.22/0.55  % (14676)Time elapsed: 0.104 s
% 0.22/0.55  % (14676)------------------------------
% 0.22/0.55  % (14676)------------------------------
% 0.22/0.55  % (14663)Refutation not found, incomplete strategy% (14663)------------------------------
% 0.22/0.55  % (14663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (14663)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (14663)Memory used [KB]: 1663
% 0.22/0.55  % (14663)Time elapsed: 0.142 s
% 0.22/0.55  % (14663)------------------------------
% 0.22/0.55  % (14663)------------------------------
% 0.22/0.55  % (14670)Refutation not found, incomplete strategy% (14670)------------------------------
% 0.22/0.55  % (14670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (14670)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (14670)Memory used [KB]: 10618
% 0.22/0.55  % (14670)Time elapsed: 0.136 s
% 0.22/0.55  % (14670)------------------------------
% 0.22/0.55  % (14670)------------------------------
% 0.22/0.55  % (14661)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.58  % (14667)Refutation found. Thanks to Tanya!
% 0.22/0.58  % SZS status Theorem for theBenchmark
% 0.22/0.58  % SZS output start Proof for theBenchmark
% 0.22/0.58  fof(f817,plain,(
% 0.22/0.58    $false),
% 0.22/0.58    inference(avatar_sat_refutation,[],[f62,f346,f492,f685,f695,f790])).
% 0.22/0.58  fof(f790,plain,(
% 0.22/0.58    spl8_1 | ~spl8_12),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f789])).
% 0.22/0.58  fof(f789,plain,(
% 0.22/0.58    $false | (spl8_1 | ~spl8_12)),
% 0.22/0.58    inference(subsumption_resolution,[],[f763,f464])).
% 0.22/0.58  fof(f464,plain,(
% 0.22/0.58    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl8_12),
% 0.22/0.58    inference(avatar_component_clause,[],[f463])).
% 0.22/0.58  fof(f463,plain,(
% 0.22/0.58    spl8_12 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.22/0.58  fof(f763,plain,(
% 0.22/0.58    ( ! [X3] : (r2_hidden(X3,sK0)) ) | (spl8_1 | ~spl8_12)),
% 0.22/0.58    inference(backward_demodulation,[],[f56,f718])).
% 0.22/0.58  fof(f718,plain,(
% 0.22/0.58    ( ! [X11] : (sK0 = k1_tarski(X11)) ) | (spl8_1 | ~spl8_12)),
% 0.22/0.58    inference(subsumption_resolution,[],[f716,f61])).
% 0.22/0.58  fof(f61,plain,(
% 0.22/0.58    k1_xboole_0 != sK0 | spl8_1),
% 0.22/0.58    inference(avatar_component_clause,[],[f59])).
% 0.22/0.58  fof(f59,plain,(
% 0.22/0.58    spl8_1 <=> k1_xboole_0 = sK0),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.58  fof(f716,plain,(
% 0.22/0.58    ( ! [X11] : (k1_xboole_0 = sK0 | sK0 = k1_tarski(X11)) ) | ~spl8_12),
% 0.22/0.58    inference(resolution,[],[f464,f39])).
% 0.22/0.58  fof(f39,plain,(
% 0.22/0.58    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f24])).
% 0.22/0.58  fof(f24,plain,(
% 0.22/0.58    ! [X0,X1] : ((sK5(X0,X1) != X1 & r2_hidden(sK5(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f12,f23])).
% 0.22/0.58  fof(f23,plain,(
% 0.22/0.58    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK5(X0,X1) != X1 & r2_hidden(sK5(X0,X1),X0)))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f12,plain,(
% 0.22/0.58    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.22/0.58    inference(ennf_transformation,[],[f4])).
% 0.22/0.58  fof(f4,axiom,(
% 0.22/0.58    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).
% 0.22/0.58  fof(f56,plain,(
% 0.22/0.58    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.22/0.58    inference(equality_resolution,[],[f55])).
% 0.22/0.58  fof(f55,plain,(
% 0.22/0.58    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.22/0.58    inference(equality_resolution,[],[f42])).
% 0.22/0.58  fof(f42,plain,(
% 0.22/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.22/0.58    inference(cnf_transformation,[],[f28])).
% 0.22/0.58  fof(f28,plain,(
% 0.22/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f26,f27])).
% 0.22/0.58  fof(f27,plain,(
% 0.22/0.58    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1))))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f26,plain,(
% 0.22/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.58    inference(rectify,[],[f25])).
% 0.22/0.58  fof(f25,plain,(
% 0.22/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.58    inference(nnf_transformation,[],[f1])).
% 0.22/0.58  fof(f1,axiom,(
% 0.22/0.58    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.58  fof(f695,plain,(
% 0.22/0.58    spl8_12 | spl8_13 | ~spl8_2),
% 0.22/0.58    inference(avatar_split_clause,[],[f572,f343,f466,f463])).
% 0.22/0.58  fof(f466,plain,(
% 0.22/0.58    spl8_13 <=> r2_hidden(sK1,k1_xboole_0)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.22/0.58  fof(f343,plain,(
% 0.22/0.58    spl8_2 <=> k1_xboole_0 = k2_relat_1(sK7(sK0,sK1))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.58  fof(f572,plain,(
% 0.22/0.58    ( ! [X0] : (r2_hidden(sK1,k1_xboole_0) | ~r2_hidden(X0,sK0)) ) | ~spl8_2),
% 0.22/0.58    inference(duplicate_literal_removal,[],[f569])).
% 0.22/0.58  fof(f569,plain,(
% 0.22/0.58    ( ! [X0] : (r2_hidden(sK1,k1_xboole_0) | ~r2_hidden(X0,sK0) | ~r2_hidden(X0,sK0)) ) | ~spl8_2),
% 0.22/0.58    inference(superposition,[],[f484,f49])).
% 0.22/0.58  fof(f49,plain,(
% 0.22/0.58    ( ! [X0,X3,X1] : (k1_funct_1(sK7(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f30])).
% 0.22/0.58  fof(f30,plain,(
% 0.22/0.58    ! [X0,X1] : (! [X3] : (k1_funct_1(sK7(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK7(X0,X1)) = X0 & v1_funct_1(sK7(X0,X1)) & v1_relat_1(sK7(X0,X1)))),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f13,f29])).
% 0.22/0.58  fof(f29,plain,(
% 0.22/0.58    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK7(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK7(X0,X1)) = X0 & v1_funct_1(sK7(X0,X1)) & v1_relat_1(sK7(X0,X1))))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f13,plain,(
% 0.22/0.58    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.58    inference(ennf_transformation,[],[f6])).
% 0.22/0.58  fof(f6,axiom,(
% 0.22/0.58    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 0.22/0.58  fof(f484,plain,(
% 0.22/0.58    ( ! [X19] : (r2_hidden(k1_funct_1(sK7(sK0,sK1),X19),k1_xboole_0) | ~r2_hidden(X19,sK0)) ) | ~spl8_2),
% 0.22/0.58    inference(forward_demodulation,[],[f483,f48])).
% 0.22/0.58  fof(f48,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k1_relat_1(sK7(X0,X1)) = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f30])).
% 0.22/0.58  fof(f483,plain,(
% 0.22/0.58    ( ! [X19] : (r2_hidden(k1_funct_1(sK7(sK0,sK1),X19),k1_xboole_0) | ~r2_hidden(X19,k1_relat_1(sK7(sK0,sK1)))) ) | ~spl8_2),
% 0.22/0.58    inference(subsumption_resolution,[],[f482,f46])).
% 0.22/0.58  fof(f46,plain,(
% 0.22/0.58    ( ! [X0,X1] : (v1_relat_1(sK7(X0,X1))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f30])).
% 0.22/0.58  fof(f482,plain,(
% 0.22/0.58    ( ! [X19] : (r2_hidden(k1_funct_1(sK7(sK0,sK1),X19),k1_xboole_0) | ~r2_hidden(X19,k1_relat_1(sK7(sK0,sK1))) | ~v1_relat_1(sK7(sK0,sK1))) ) | ~spl8_2),
% 0.22/0.58    inference(subsumption_resolution,[],[f460,f47])).
% 0.22/0.58  fof(f47,plain,(
% 0.22/0.58    ( ! [X0,X1] : (v1_funct_1(sK7(X0,X1))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f30])).
% 0.22/0.58  fof(f460,plain,(
% 0.22/0.58    ( ! [X19] : (r2_hidden(k1_funct_1(sK7(sK0,sK1),X19),k1_xboole_0) | ~r2_hidden(X19,k1_relat_1(sK7(sK0,sK1))) | ~v1_funct_1(sK7(sK0,sK1)) | ~v1_relat_1(sK7(sK0,sK1))) ) | ~spl8_2),
% 0.22/0.58    inference(superposition,[],[f52,f345])).
% 0.22/0.58  fof(f345,plain,(
% 0.22/0.58    k1_xboole_0 = k2_relat_1(sK7(sK0,sK1)) | ~spl8_2),
% 0.22/0.58    inference(avatar_component_clause,[],[f343])).
% 0.22/0.58  fof(f52,plain,(
% 0.22/0.58    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(equality_resolution,[],[f51])).
% 0.22/0.58  fof(f51,plain,(
% 0.22/0.58    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(equality_resolution,[],[f35])).
% 0.22/0.58  fof(f35,plain,(
% 0.22/0.58    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f22])).
% 0.22/0.58  fof(f22,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & ((sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f18,f21,f20,f19])).
% 0.22/0.58  fof(f19,plain,(
% 0.22/0.58    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1))))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f20,plain,(
% 0.22/0.58    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f21,plain,(
% 0.22/0.58    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f18,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.58    inference(rectify,[],[f17])).
% 0.22/0.58  fof(f17,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.58    inference(nnf_transformation,[],[f11])).
% 0.22/0.58  fof(f11,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.58    inference(flattening,[],[f10])).
% 0.22/0.58  fof(f10,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f5])).
% 0.22/0.58  fof(f5,axiom,(
% 0.22/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.22/0.58  fof(f685,plain,(
% 0.22/0.58    ~spl8_2 | ~spl8_13 | spl8_16),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f684])).
% 0.22/0.58  fof(f684,plain,(
% 0.22/0.58    $false | (~spl8_2 | ~spl8_13 | spl8_16)),
% 0.22/0.58    inference(subsumption_resolution,[],[f682,f468])).
% 0.22/0.58  fof(f468,plain,(
% 0.22/0.58    r2_hidden(sK1,k1_xboole_0) | ~spl8_13),
% 0.22/0.58    inference(avatar_component_clause,[],[f466])).
% 0.22/0.58  fof(f682,plain,(
% 0.22/0.58    ~r2_hidden(sK1,k1_xboole_0) | (~spl8_2 | ~spl8_13 | spl8_16)),
% 0.22/0.58    inference(trivial_inequality_removal,[],[f681])).
% 0.22/0.58  fof(f681,plain,(
% 0.22/0.58    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK1,k1_xboole_0) | (~spl8_2 | ~spl8_13 | spl8_16)),
% 0.22/0.58    inference(superposition,[],[f491,f627])).
% 0.22/0.58  fof(f627,plain,(
% 0.22/0.58    ( ! [X0] : (k1_tarski(X0) = k1_xboole_0 | ~r2_hidden(X0,k1_xboole_0)) ) | (~spl8_2 | ~spl8_13)),
% 0.22/0.58    inference(subsumption_resolution,[],[f626,f446])).
% 0.22/0.58  fof(f446,plain,(
% 0.22/0.58    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0) | sK1 = X1) ) | ~spl8_2),
% 0.22/0.58    inference(superposition,[],[f111,f345])).
% 0.22/0.58  fof(f111,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_relat_1(sK7(X0,X1))) | X1 = X2) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f79,f73])).
% 0.22/0.58  fof(f73,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (r2_hidden(sK4(sK7(X0,X1),X2),X0) | ~r2_hidden(X2,k2_relat_1(sK7(X0,X1)))) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f72,f46])).
% 0.22/0.58  fof(f72,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (r2_hidden(sK4(sK7(X0,X1),X2),X0) | ~r2_hidden(X2,k2_relat_1(sK7(X0,X1))) | ~v1_relat_1(sK7(X0,X1))) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f71,f47])).
% 0.22/0.58  fof(f71,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (r2_hidden(sK4(sK7(X0,X1),X2),X0) | ~r2_hidden(X2,k2_relat_1(sK7(X0,X1))) | ~v1_funct_1(sK7(X0,X1)) | ~v1_relat_1(sK7(X0,X1))) )),
% 0.22/0.58    inference(superposition,[],[f54,f48])).
% 0.22/0.58  fof(f54,plain,(
% 0.22/0.58    ( ! [X0,X5] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(equality_resolution,[],[f33])).
% 0.22/0.58  fof(f33,plain,(
% 0.22/0.58    ( ! [X0,X5,X1] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f22])).
% 0.22/0.58  fof(f79,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (X1 = X2 | ~r2_hidden(X2,k2_relat_1(sK7(X0,X1))) | ~r2_hidden(sK4(sK7(X0,X1),X2),X0)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f78,f46])).
% 0.22/0.58  fof(f78,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (X1 = X2 | ~r2_hidden(X2,k2_relat_1(sK7(X0,X1))) | ~v1_relat_1(sK7(X0,X1)) | ~r2_hidden(sK4(sK7(X0,X1),X2),X0)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f74,f47])).
% 0.22/0.58  fof(f74,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (X1 = X2 | ~r2_hidden(X2,k2_relat_1(sK7(X0,X1))) | ~v1_funct_1(sK7(X0,X1)) | ~v1_relat_1(sK7(X0,X1)) | ~r2_hidden(sK4(sK7(X0,X1),X2),X0)) )),
% 0.22/0.58    inference(superposition,[],[f53,f49])).
% 0.22/0.58  fof(f53,plain,(
% 0.22/0.58    ( ! [X0,X5] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(equality_resolution,[],[f34])).
% 0.22/0.58  fof(f34,plain,(
% 0.22/0.58    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f22])).
% 0.22/0.58  fof(f626,plain,(
% 0.22/0.58    ( ! [X0] : (sK1 != X0 | k1_tarski(X0) = k1_xboole_0 | ~r2_hidden(X0,k1_xboole_0)) ) | (~spl8_2 | ~spl8_13)),
% 0.22/0.58    inference(subsumption_resolution,[],[f625,f468])).
% 0.22/0.58  fof(f625,plain,(
% 0.22/0.58    ( ! [X0] : (sK1 != X0 | k1_tarski(X0) = k1_xboole_0 | ~r2_hidden(sK1,k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0)) ) | ~spl8_2),
% 0.22/0.58    inference(duplicate_literal_removal,[],[f622])).
% 0.22/0.58  fof(f622,plain,(
% 0.22/0.58    ( ! [X0] : (sK1 != X0 | k1_tarski(X0) = k1_xboole_0 | ~r2_hidden(sK1,k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0) | k1_tarski(X0) = k1_xboole_0) ) | ~spl8_2),
% 0.22/0.58    inference(superposition,[],[f44,f456])).
% 0.22/0.58  fof(f456,plain,(
% 0.22/0.58    ( ! [X16] : (sK1 = sK6(X16,k1_xboole_0) | ~r2_hidden(X16,k1_xboole_0) | k1_xboole_0 = k1_tarski(X16)) ) | ~spl8_2),
% 0.22/0.58    inference(superposition,[],[f221,f345])).
% 0.22/0.58  fof(f221,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (sK6(X0,k2_relat_1(sK7(X1,X2))) = X2 | ~r2_hidden(X0,k2_relat_1(sK7(X1,X2))) | k1_tarski(X0) = k2_relat_1(sK7(X1,X2))) )),
% 0.22/0.58    inference(trivial_inequality_removal,[],[f220])).
% 0.22/0.58  fof(f220,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (X0 != X0 | k1_tarski(X0) = k2_relat_1(sK7(X1,X2)) | ~r2_hidden(X0,k2_relat_1(sK7(X1,X2))) | sK6(X0,k2_relat_1(sK7(X1,X2))) = X2) )),
% 0.22/0.58    inference(duplicate_literal_removal,[],[f217])).
% 0.22/0.58  fof(f217,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (X0 != X0 | k1_tarski(X0) = k2_relat_1(sK7(X1,X2)) | ~r2_hidden(X0,k2_relat_1(sK7(X1,X2))) | sK6(X0,k2_relat_1(sK7(X1,X2))) = X2 | k1_tarski(X0) = k2_relat_1(sK7(X1,X2))) )),
% 0.22/0.58    inference(superposition,[],[f44,f116])).
% 0.22/0.58  fof(f116,plain,(
% 0.22/0.58    ( ! [X14,X15,X13] : (sK6(X14,k2_relat_1(sK7(X15,X13))) = X14 | sK6(X14,k2_relat_1(sK7(X15,X13))) = X13 | k2_relat_1(sK7(X15,X13)) = k1_tarski(X14)) )),
% 0.22/0.58    inference(resolution,[],[f111,f43])).
% 0.22/0.58  fof(f43,plain,(
% 0.22/0.58    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X1) | sK6(X0,X1) = X0 | k1_tarski(X0) = X1) )),
% 0.22/0.58    inference(cnf_transformation,[],[f28])).
% 0.22/0.58  fof(f44,plain,(
% 0.22/0.58    ( ! [X0,X1] : (sK6(X0,X1) != X0 | k1_tarski(X0) = X1 | ~r2_hidden(sK6(X0,X1),X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f28])).
% 0.22/0.58  fof(f491,plain,(
% 0.22/0.58    k1_xboole_0 != k1_tarski(sK1) | spl8_16),
% 0.22/0.58    inference(avatar_component_clause,[],[f489])).
% 0.22/0.58  fof(f489,plain,(
% 0.22/0.58    spl8_16 <=> k1_xboole_0 = k1_tarski(sK1)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.22/0.58  fof(f492,plain,(
% 0.22/0.58    ~spl8_16 | ~spl8_2),
% 0.22/0.58    inference(avatar_split_clause,[],[f487,f343,f489])).
% 0.22/0.58  fof(f487,plain,(
% 0.22/0.58    k1_xboole_0 != k1_tarski(sK1) | ~spl8_2),
% 0.22/0.58    inference(subsumption_resolution,[],[f486,f46])).
% 0.22/0.58  fof(f486,plain,(
% 0.22/0.58    k1_xboole_0 != k1_tarski(sK1) | ~v1_relat_1(sK7(sK0,sK1)) | ~spl8_2),
% 0.22/0.58    inference(subsumption_resolution,[],[f485,f47])).
% 0.22/0.58  fof(f485,plain,(
% 0.22/0.58    k1_xboole_0 != k1_tarski(sK1) | ~v1_funct_1(sK7(sK0,sK1)) | ~v1_relat_1(sK7(sK0,sK1)) | ~spl8_2),
% 0.22/0.58    inference(subsumption_resolution,[],[f461,f48])).
% 0.22/0.58  fof(f461,plain,(
% 0.22/0.58    k1_xboole_0 != k1_tarski(sK1) | sK0 != k1_relat_1(sK7(sK0,sK1)) | ~v1_funct_1(sK7(sK0,sK1)) | ~v1_relat_1(sK7(sK0,sK1)) | ~spl8_2),
% 0.22/0.58    inference(superposition,[],[f32,f345])).
% 0.22/0.58  fof(f32,plain,(
% 0.22/0.58    ( ! [X2] : (k2_relat_1(X2) != k1_tarski(sK1) | k1_relat_1(X2) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f16])).
% 0.22/0.58  fof(f16,plain,(
% 0.22/0.58    ! [X2] : (k2_relat_1(X2) != k1_tarski(sK1) | k1_relat_1(X2) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & k1_xboole_0 != sK0),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f15,f14])).
% 0.22/0.58  fof(f14,plain,(
% 0.22/0.58    ? [X0] : (? [X1] : ! [X2] : (k1_tarski(X1) != k2_relat_1(X2) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & k1_xboole_0 != X0) => (? [X1] : ! [X2] : (k1_tarski(X1) != k2_relat_1(X2) | k1_relat_1(X2) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & k1_xboole_0 != sK0)),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f15,plain,(
% 0.22/0.58    ? [X1] : ! [X2] : (k1_tarski(X1) != k2_relat_1(X2) | k1_relat_1(X2) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) => ! [X2] : (k2_relat_1(X2) != k1_tarski(sK1) | k1_relat_1(X2) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f9,plain,(
% 0.22/0.58    ? [X0] : (? [X1] : ! [X2] : (k1_tarski(X1) != k2_relat_1(X2) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & k1_xboole_0 != X0)),
% 0.22/0.58    inference(ennf_transformation,[],[f8])).
% 0.22/0.58  fof(f8,negated_conjecture,(
% 0.22/0.58    ~! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.58    inference(negated_conjecture,[],[f7])).
% 0.22/0.58  fof(f7,conjecture,(
% 0.22/0.58    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 0.22/0.58  fof(f346,plain,(
% 0.22/0.58    spl8_2),
% 0.22/0.58    inference(avatar_split_clause,[],[f341,f343])).
% 0.22/0.58  fof(f341,plain,(
% 0.22/0.58    k1_xboole_0 = k2_relat_1(sK7(sK0,sK1))),
% 0.22/0.58    inference(equality_resolution,[],[f333])).
% 0.22/0.58  fof(f333,plain,(
% 0.22/0.58    ( ! [X0] : (sK0 != X0 | k1_xboole_0 = k2_relat_1(sK7(X0,sK1))) )),
% 0.22/0.58    inference(equality_resolution,[],[f331])).
% 0.22/0.58  fof(f331,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k1_tarski(X1) != k1_tarski(sK1) | sK0 != X0 | k1_xboole_0 = k2_relat_1(sK7(X0,X1))) )),
% 0.22/0.58    inference(superposition,[],[f285,f48])).
% 0.22/0.58  fof(f285,plain,(
% 0.22/0.58    ( ! [X41,X40] : (sK0 != k1_relat_1(sK7(X40,X41)) | k1_tarski(sK1) != k1_tarski(X41) | k1_xboole_0 = k2_relat_1(sK7(X40,X41))) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f284,f46])).
% 0.22/0.58  fof(f284,plain,(
% 0.22/0.58    ( ! [X41,X40] : (k1_tarski(sK1) != k1_tarski(X41) | sK0 != k1_relat_1(sK7(X40,X41)) | ~v1_relat_1(sK7(X40,X41)) | k1_xboole_0 = k2_relat_1(sK7(X40,X41))) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f275,f47])).
% 0.22/0.58  fof(f275,plain,(
% 0.22/0.58    ( ! [X41,X40] : (k1_tarski(sK1) != k1_tarski(X41) | sK0 != k1_relat_1(sK7(X40,X41)) | ~v1_funct_1(sK7(X40,X41)) | ~v1_relat_1(sK7(X40,X41)) | k1_xboole_0 = k2_relat_1(sK7(X40,X41))) )),
% 0.22/0.58    inference(superposition,[],[f32,f229])).
% 0.22/0.58  fof(f229,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK7(X0,X1)) | k1_xboole_0 = k2_relat_1(sK7(X0,X1))) )),
% 0.22/0.58    inference(equality_resolution,[],[f216])).
% 0.22/0.58  fof(f216,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (X1 != X2 | k1_xboole_0 = k2_relat_1(sK7(X0,X1)) | k2_relat_1(sK7(X0,X1)) = k1_tarski(X2)) )),
% 0.22/0.58    inference(duplicate_literal_removal,[],[f213])).
% 0.22/0.58  fof(f213,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (X1 != X2 | k1_xboole_0 = k2_relat_1(sK7(X0,X1)) | k2_relat_1(sK7(X0,X1)) = k1_tarski(X2) | k1_xboole_0 = k2_relat_1(sK7(X0,X1)) | k2_relat_1(sK7(X0,X1)) = k1_tarski(X2)) )),
% 0.22/0.58    inference(superposition,[],[f40,f115])).
% 0.22/0.58  fof(f115,plain,(
% 0.22/0.58    ( ! [X12,X10,X11] : (sK5(k2_relat_1(sK7(X11,X10)),X12) = X10 | k1_xboole_0 = k2_relat_1(sK7(X11,X10)) | k2_relat_1(sK7(X11,X10)) = k1_tarski(X12)) )),
% 0.22/0.58    inference(resolution,[],[f111,f39])).
% 0.22/0.58  fof(f40,plain,(
% 0.22/0.58    ( ! [X0,X1] : (sK5(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f24])).
% 0.22/0.58  fof(f62,plain,(
% 0.22/0.58    ~spl8_1),
% 0.22/0.58    inference(avatar_split_clause,[],[f31,f59])).
% 0.22/0.58  fof(f31,plain,(
% 0.22/0.58    k1_xboole_0 != sK0),
% 0.22/0.58    inference(cnf_transformation,[],[f16])).
% 0.22/0.58  % SZS output end Proof for theBenchmark
% 0.22/0.58  % (14667)------------------------------
% 0.22/0.58  % (14667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (14667)Termination reason: Refutation
% 0.22/0.58  
% 0.22/0.58  % (14667)Memory used [KB]: 6780
% 0.22/0.58  % (14667)Time elapsed: 0.136 s
% 0.22/0.58  % (14667)------------------------------
% 0.22/0.58  % (14667)------------------------------
% 0.22/0.58  % (14645)Success in time 0.203 s
%------------------------------------------------------------------------------
