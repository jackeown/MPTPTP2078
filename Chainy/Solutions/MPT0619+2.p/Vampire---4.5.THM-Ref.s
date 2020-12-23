%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0619+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:40 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   86 (1835 expanded)
%              Number of leaves         :   15 ( 482 expanded)
%              Depth                    :   23
%              Number of atoms          :  305 (8069 expanded)
%              Number of equality atoms :  156 (3716 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1668,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1627,f1667])).

fof(f1667,plain,(
    ! [X2] : sK6(sK1) != X2 ),
    inference(subsumption_resolution,[],[f1666,f1615])).

fof(f1615,plain,(
    ! [X1] : k1_tarski(X1) != k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f1614,f1599])).

fof(f1599,plain,(
    k1_xboole_0 != k2_relat_1(sK1) ),
    inference(superposition,[],[f1090,f1235])).

fof(f1235,plain,(
    k2_relat_1(sK1) = k2_xboole_0(k1_tarski(sK6(sK1)),k2_relat_1(sK1)) ),
    inference(resolution,[],[f1223,f1086])).

fof(f1086,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f959])).

fof(f959,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f304])).

fof(f304,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f1223,plain,(
    r2_hidden(sK6(sK1),k2_relat_1(sK1)) ),
    inference(resolution,[],[f1149,f1110])).

fof(f1110,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f1109])).

fof(f1109,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f1073])).

fof(f1073,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f996])).

fof(f996,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK10(X0,X1) != X0
            | ~ r2_hidden(sK10(X0,X1),X1) )
          & ( sK10(X0,X1) = X0
            | r2_hidden(sK10(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f994,f995])).

fof(f995,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK10(X0,X1) != X0
          | ~ r2_hidden(sK10(X0,X1),X1) )
        & ( sK10(X0,X1) = X0
          | r2_hidden(sK10(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f994,plain,(
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
    inference(rectify,[],[f993])).

fof(f993,plain,(
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
    inference(nnf_transformation,[],[f175])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f1149,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | r2_hidden(sK6(sK1),k2_relat_1(sK1)) ) ),
    inference(forward_demodulation,[],[f1147,f1001])).

fof(f1001,plain,(
    k1_tarski(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f966])).

fof(f966,plain,
    ( k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))
    & k1_tarski(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f900,f965])).

fof(f965,plain,
    ( ? [X0,X1] :
        ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
        & k1_tarski(X0) = k1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))
      & k1_tarski(sK0) = k1_relat_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f900,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f899])).

fof(f899,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f896])).

fof(f896,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f895])).

fof(f895,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f1147,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | r2_hidden(sK6(sK1),k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f1021,f999])).

fof(f999,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f966])).

fof(f1021,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | r2_hidden(sK6(X1),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f979])).

fof(f979,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X1),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f913,f978])).

fof(f978,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
     => r2_hidden(sK6(X1),k2_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f913,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f912])).

fof(f912,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f792])).

fof(f792,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(X1))
          & r2_hidden(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_relat_1)).

fof(f1090,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f407])).

fof(f407,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f1614,plain,(
    ! [X1] :
      ( k1_tarski(X1) != k2_relat_1(sK1)
      | k1_xboole_0 = k2_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f1613,f1446])).

fof(f1446,plain,(
    k2_relat_1(sK1) != k1_tarski(sK6(sK1)) ),
    inference(backward_demodulation,[],[f1002,f1445])).

fof(f1445,plain,(
    k1_funct_1(sK1,sK0) = sK6(sK1) ),
    inference(backward_demodulation,[],[f1394,f1441])).

fof(f1441,plain,(
    sK0 = sK4(sK1,sK6(sK1)) ),
    inference(resolution,[],[f1363,f1223])).

fof(f1363,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_relat_1(sK1))
      | sK0 = sK4(sK1,X2) ) ),
    inference(resolution,[],[f1261,f1111])).

fof(f1111,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f1072])).

fof(f1072,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f996])).

fof(f1261,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK1,X0),k1_tarski(sK0))
      | ~ r2_hidden(X0,k2_relat_1(sK1)) ) ),
    inference(forward_demodulation,[],[f1260,f1001])).

fof(f1260,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | r2_hidden(sK4(sK1,X0),k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f1258,f1000])).

fof(f1000,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f966])).

fof(f1258,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | r2_hidden(sK4(sK1,X0),k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f1104,f999])).

fof(f1104,plain,(
    ! [X0,X5] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f1011])).

fof(f1011,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f975])).

fof(f975,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f971,f974,f973,f972])).

fof(f972,plain,(
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

fof(f973,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK2(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f974,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f971,plain,(
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
    inference(rectify,[],[f970])).

fof(f970,plain,(
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
    inference(nnf_transformation,[],[f908])).

fof(f908,plain,(
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
    inference(flattening,[],[f907])).

fof(f907,plain,(
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
    inference(ennf_transformation,[],[f891])).

fof(f891,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f1394,plain,(
    sK6(sK1) = k1_funct_1(sK1,sK4(sK1,sK6(sK1))) ),
    inference(resolution,[],[f1286,f1223])).

fof(f1286,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | k1_funct_1(sK1,sK4(sK1,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f1284,f1000])).

fof(f1284,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | k1_funct_1(sK1,sK4(sK1,X0)) = X0 ) ),
    inference(resolution,[],[f1103,f999])).

fof(f1103,plain,(
    ! [X0,X5] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK4(X0,X5)) = X5 ) ),
    inference(equality_resolution,[],[f1012])).

fof(f1012,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f975])).

fof(f1002,plain,(
    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f966])).

fof(f1613,plain,(
    ! [X1] :
      ( k1_tarski(X1) != k2_relat_1(sK1)
      | k2_relat_1(sK1) = k1_tarski(sK6(sK1))
      | k1_xboole_0 = k2_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f1601,f1164])).

fof(f1164,plain,(
    ! [X2] : k1_xboole_0 != k1_tarski(X2) ),
    inference(superposition,[],[f1090,f1139])).

fof(f1139,plain,(
    ! [X0] : k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(resolution,[],[f1086,f1110])).

fof(f1601,plain,(
    ! [X1] :
      ( k1_tarski(X1) != k2_relat_1(sK1)
      | k1_xboole_0 = k1_tarski(sK6(sK1))
      | k2_relat_1(sK1) = k1_tarski(sK6(sK1))
      | k1_xboole_0 = k2_relat_1(sK1) ) ),
    inference(superposition,[],[f1057,f1235])).

fof(f1057,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) != k1_tarski(X0)
      | k1_xboole_0 = X1
      | X1 = X2
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f946])).

fof(f946,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f402])).

fof(f402,axiom,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f1666,plain,(
    ! [X2] :
      ( sK6(sK1) != X2
      | k1_tarski(X2) = k2_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f1664,f1599])).

fof(f1664,plain,(
    ! [X2] :
      ( sK6(sK1) != X2
      | k1_xboole_0 = k2_relat_1(sK1)
      | k1_tarski(X2) = k2_relat_1(sK1) ) ),
    inference(superposition,[],[f1059,f1627])).

fof(f1059,plain,(
    ! [X0,X1] :
      ( sK8(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f984])).

fof(f984,plain,(
    ! [X0,X1] :
      ( ( sK8(X0,X1) != X1
        & r2_hidden(sK8(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f947,f983])).

fof(f983,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK8(X0,X1) != X1
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f947,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f314])).

fof(f314,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f1627,plain,(
    ! [X1] : sK6(sK1) = sK8(k2_relat_1(sK1),X1) ),
    inference(forward_demodulation,[],[f1626,f1445])).

fof(f1626,plain,(
    ! [X1] : k1_funct_1(sK1,sK0) = sK8(k2_relat_1(sK1),X1) ),
    inference(backward_demodulation,[],[f1625,f1623])).

fof(f1623,plain,(
    ! [X1] : sK0 = sK4(sK1,sK8(k2_relat_1(sK1),X1)) ),
    inference(subsumption_resolution,[],[f1606,f1615])).

fof(f1606,plain,(
    ! [X1] :
      ( sK0 = sK4(sK1,sK8(k2_relat_1(sK1),X1))
      | k1_tarski(X1) = k2_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f1442,f1599])).

fof(f1442,plain,(
    ! [X1] :
      ( sK0 = sK4(sK1,sK8(k2_relat_1(sK1),X1))
      | k1_xboole_0 = k2_relat_1(sK1)
      | k1_tarski(X1) = k2_relat_1(sK1) ) ),
    inference(resolution,[],[f1363,f1058])).

fof(f1058,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f984])).

fof(f1625,plain,(
    ! [X1] : sK8(k2_relat_1(sK1),X1) = k1_funct_1(sK1,sK4(sK1,sK8(k2_relat_1(sK1),X1))) ),
    inference(subsumption_resolution,[],[f1608,f1615])).

fof(f1608,plain,(
    ! [X1] :
      ( sK8(k2_relat_1(sK1),X1) = k1_funct_1(sK1,sK4(sK1,sK8(k2_relat_1(sK1),X1)))
      | k1_tarski(X1) = k2_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f1395,f1599])).

fof(f1395,plain,(
    ! [X1] :
      ( sK8(k2_relat_1(sK1),X1) = k1_funct_1(sK1,sK4(sK1,sK8(k2_relat_1(sK1),X1)))
      | k1_xboole_0 = k2_relat_1(sK1)
      | k1_tarski(X1) = k2_relat_1(sK1) ) ),
    inference(resolution,[],[f1286,f1058])).
%------------------------------------------------------------------------------
