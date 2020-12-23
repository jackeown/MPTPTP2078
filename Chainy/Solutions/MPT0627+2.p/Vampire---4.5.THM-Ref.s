%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0627+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:41 EST 2020

% Result     : Theorem 5.41s
% Output     : Refutation 5.41s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 278 expanded)
%              Number of leaves         :   20 (  85 expanded)
%              Depth                    :   20
%              Number of atoms          :  511 (1571 expanded)
%              Number of equality atoms :   50 ( 238 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7289,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f5154,f5164,f5175,f7288])).

fof(f7288,plain,(
    spl180_3 ),
    inference(avatar_contradiction_clause,[],[f7287])).

fof(f7287,plain,
    ( $false
    | spl180_3 ),
    inference(subsumption_resolution,[],[f7286,f2183])).

fof(f2183,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f1691])).

fof(f1691,plain,
    ( k1_funct_1(k5_relat_1(sK5,sK4),sK3) != k1_funct_1(sK4,k1_funct_1(sK5,sK3))
    & r2_hidden(sK3,k1_relat_1(k5_relat_1(sK5,sK4)))
    & v1_funct_1(sK5)
    & v1_relat_1(sK5)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f931,f1690,f1689])).

fof(f1689,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k1_funct_1(k5_relat_1(X2,X1),X0) != k1_funct_1(X1,k1_funct_1(X2,X0))
            & r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k1_funct_1(k5_relat_1(X2,sK4),sK3) != k1_funct_1(sK4,k1_funct_1(X2,sK3))
          & r2_hidden(sK3,k1_relat_1(k5_relat_1(X2,sK4)))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f1690,plain,
    ( ? [X2] :
        ( k1_funct_1(k5_relat_1(X2,sK4),sK3) != k1_funct_1(sK4,k1_funct_1(X2,sK3))
        & r2_hidden(sK3,k1_relat_1(k5_relat_1(X2,sK4)))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(k5_relat_1(sK5,sK4),sK3) != k1_funct_1(sK4,k1_funct_1(sK5,sK3))
      & r2_hidden(sK3,k1_relat_1(k5_relat_1(sK5,sK4)))
      & v1_funct_1(sK5)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f931,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) != k1_funct_1(X1,k1_funct_1(X2,X0))
          & r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f930])).

fof(f930,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) != k1_funct_1(X1,k1_funct_1(X2,X0))
          & r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f912])).

fof(f912,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
             => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f911])).

fof(f911,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

fof(f7286,plain,
    ( ~ v1_relat_1(sK5)
    | spl180_3 ),
    inference(subsumption_resolution,[],[f7285,f2184])).

fof(f2184,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f1691])).

fof(f7285,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | spl180_3 ),
    inference(subsumption_resolution,[],[f7282,f4911])).

fof(f4911,plain,(
    r2_hidden(sK3,k1_relat_1(sK5)) ),
    inference(subsumption_resolution,[],[f4910,f2183])).

fof(f4910,plain,
    ( ~ v1_relat_1(sK5)
    | r2_hidden(sK3,k1_relat_1(sK5)) ),
    inference(subsumption_resolution,[],[f4909,f2181])).

fof(f2181,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f1691])).

fof(f4909,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK5)
    | r2_hidden(sK3,k1_relat_1(sK5)) ),
    inference(resolution,[],[f2317,f4900])).

fof(f4900,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK5,sK4)),X0)
      | r2_hidden(sK3,X0) ) ),
    inference(resolution,[],[f2908,f2185])).

fof(f2185,plain,(
    r2_hidden(sK3,k1_relat_1(k5_relat_1(sK5,sK4))) ),
    inference(cnf_transformation,[],[f1691])).

fof(f2908,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1936])).

fof(f1936,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK100(X0,X1),X1)
          & r2_hidden(sK100(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK100])],[f1934,f1935])).

fof(f1935,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK100(X0,X1),X1)
        & r2_hidden(sK100(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1934,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1933])).

fof(f1933,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1407])).

fof(f1407,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f2317,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f986])).

fof(f986,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f843])).

fof(f843,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(f7282,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK5))
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | spl180_3 ),
    inference(resolution,[],[f7272,f3646])).

fof(f3646,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f2428])).

fof(f2428,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1759])).

fof(f1759,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1080])).

fof(f1080,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1079])).

fof(f1079,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f890])).

fof(f890,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f7272,plain,
    ( ~ r2_hidden(k4_tarski(sK3,k1_funct_1(sK5,sK3)),sK5)
    | spl180_3 ),
    inference(subsumption_resolution,[],[f7271,f2182])).

fof(f2182,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f1691])).

fof(f7271,plain,
    ( ~ r2_hidden(k4_tarski(sK3,k1_funct_1(sK5,sK3)),sK5)
    | ~ v1_funct_1(sK4)
    | spl180_3 ),
    inference(subsumption_resolution,[],[f7270,f7236])).

fof(f7236,plain,(
    r2_hidden(k1_funct_1(sK5,sK3),k1_relat_1(sK4)) ),
    inference(resolution,[],[f7226,f3668])).

fof(f3668,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f2886])).

fof(f2886,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1915])).

fof(f1915,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f1914])).

fof(f1914,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f7226,plain,(
    ! [X9] :
      ( ~ r1_tarski(k1_relat_1(sK4),X9)
      | r2_hidden(k1_funct_1(sK5,sK3),X9) ) ),
    inference(subsumption_resolution,[],[f7225,f2181])).

fof(f7225,plain,(
    ! [X9] :
      ( ~ v1_relat_1(sK4)
      | r2_hidden(k1_funct_1(sK5,sK3),X9)
      | ~ r1_tarski(k1_relat_1(sK4),X9) ) ),
    inference(subsumption_resolution,[],[f7224,f2182])).

fof(f7224,plain,(
    ! [X9] :
      ( ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4)
      | r2_hidden(k1_funct_1(sK5,sK3),X9)
      | ~ r1_tarski(k1_relat_1(sK4),X9) ) ),
    inference(subsumption_resolution,[],[f7223,f2183])).

fof(f7223,plain,(
    ! [X9] :
      ( ~ v1_relat_1(sK5)
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4)
      | r2_hidden(k1_funct_1(sK5,sK3),X9)
      | ~ r1_tarski(k1_relat_1(sK4),X9) ) ),
    inference(subsumption_resolution,[],[f7211,f2184])).

fof(f7211,plain,(
    ! [X9] :
      ( ~ v1_funct_1(sK5)
      | ~ v1_relat_1(sK5)
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4)
      | r2_hidden(k1_funct_1(sK5,sK3),X9)
      | ~ r1_tarski(k1_relat_1(sK4),X9) ) ),
    inference(resolution,[],[f4979,f2185])).

fof(f4979,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(X4,k1_relat_1(k5_relat_1(X5,X6)))
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6)
      | r2_hidden(k1_funct_1(X5,X4),X7)
      | ~ r1_tarski(k1_relat_1(X6),X7) ) ),
    inference(resolution,[],[f2846,f2908])).

fof(f2846,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1895])).

fof(f1895,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1894])).

fof(f1894,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1374])).

fof(f1374,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1373])).

fof(f1373,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f910])).

fof(f910,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

fof(f7270,plain,
    ( ~ r2_hidden(k4_tarski(sK3,k1_funct_1(sK5,sK3)),sK5)
    | ~ r2_hidden(k1_funct_1(sK5,sK3),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | spl180_3 ),
    inference(subsumption_resolution,[],[f7269,f2183])).

fof(f7269,plain,
    ( ~ r2_hidden(k4_tarski(sK3,k1_funct_1(sK5,sK3)),sK5)
    | ~ v1_relat_1(sK5)
    | ~ r2_hidden(k1_funct_1(sK5,sK3),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | spl180_3 ),
    inference(subsumption_resolution,[],[f7262,f2181])).

fof(f7262,plain,
    ( ~ r2_hidden(k4_tarski(sK3,k1_funct_1(sK5,sK3)),sK5)
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK5)
    | ~ r2_hidden(k1_funct_1(sK5,sK3),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | spl180_3 ),
    inference(resolution,[],[f5018,f5153])).

fof(f5153,plain,
    ( ~ r2_hidden(k4_tarski(sK3,k1_funct_1(sK4,k1_funct_1(sK5,sK3))),k5_relat_1(sK5,sK4))
    | spl180_3 ),
    inference(avatar_component_clause,[],[f5151])).

fof(f5151,plain,
    ( spl180_3
  <=> r2_hidden(k4_tarski(sK3,k1_funct_1(sK4,k1_funct_1(sK5,sK3))),k5_relat_1(sK5,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_3])])).

fof(f5018,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X1,X2)),k5_relat_1(X3,X1))
      | ~ r2_hidden(k4_tarski(X0,X2),X3)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X3)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f5014])).

fof(f5014,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X1,X2)),k5_relat_1(X3,X1))
      | ~ r2_hidden(k4_tarski(X0,X2),X3)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X3)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f5013,f3646])).

fof(f5013,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( ~ r2_hidden(k4_tarski(X9,X8),X1)
      | r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f3628,f2854])).

fof(f2854,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1382])).

fof(f1382,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1381])).

fof(f1381,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f667])).

fof(f667,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f3628,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f2363])).

fof(f2363,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1722])).

fof(f1722,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK18(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK17(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK17(X0,X1,X2),sK18(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK19(X0,X1,X2),sK18(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK17(X0,X1,X2),sK19(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK17(X0,X1,X2),sK18(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK20(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK20(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17,sK18,sK19,sK20])],[f1718,f1721,f1720,f1719])).

fof(f1719,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK18(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK17(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK17(X0,X1,X2),sK18(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK18(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK17(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK17(X0,X1,X2),sK18(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1720,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK18(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK17(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK19(X0,X1,X2),sK18(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK17(X0,X1,X2),sK19(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1721,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK20(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK20(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1718,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1717])).

fof(f1717,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X3,X4] :
                      ( ( r2_hidden(k4_tarski(X3,X4),X2)
                        | ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1035])).

fof(f1035,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f660])).

fof(f660,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(f5175,plain,(
    spl180_2 ),
    inference(avatar_contradiction_clause,[],[f5174])).

fof(f5174,plain,
    ( $false
    | spl180_2 ),
    inference(subsumption_resolution,[],[f5173,f2183])).

fof(f5173,plain,
    ( ~ v1_relat_1(sK5)
    | spl180_2 ),
    inference(subsumption_resolution,[],[f5172,f2184])).

fof(f5172,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | spl180_2 ),
    inference(subsumption_resolution,[],[f5171,f2181])).

fof(f5171,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | spl180_2 ),
    inference(subsumption_resolution,[],[f5168,f2182])).

fof(f5168,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | spl180_2 ),
    inference(resolution,[],[f5149,f2839])).

fof(f2839,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1364])).

fof(f1364,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1363])).

fof(f1363,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f895])).

fof(f895,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f5149,plain,
    ( ~ v1_funct_1(k5_relat_1(sK5,sK4))
    | spl180_2 ),
    inference(avatar_component_clause,[],[f5147])).

fof(f5147,plain,
    ( spl180_2
  <=> v1_funct_1(k5_relat_1(sK5,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_2])])).

fof(f5164,plain,(
    spl180_1 ),
    inference(avatar_contradiction_clause,[],[f5163])).

fof(f5163,plain,
    ( $false
    | spl180_1 ),
    inference(subsumption_resolution,[],[f5162,f2183])).

fof(f5162,plain,
    ( ~ v1_relat_1(sK5)
    | spl180_1 ),
    inference(subsumption_resolution,[],[f5156,f2181])).

fof(f5156,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK5)
    | spl180_1 ),
    inference(resolution,[],[f5145,f2854])).

fof(f5145,plain,
    ( ~ v1_relat_1(k5_relat_1(sK5,sK4))
    | spl180_1 ),
    inference(avatar_component_clause,[],[f5143])).

fof(f5143,plain,
    ( spl180_1
  <=> v1_relat_1(k5_relat_1(sK5,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_1])])).

fof(f5154,plain,
    ( ~ spl180_1
    | ~ spl180_2
    | ~ spl180_3 ),
    inference(avatar_split_clause,[],[f4930,f5151,f5147,f5143])).

fof(f4930,plain,
    ( ~ r2_hidden(k4_tarski(sK3,k1_funct_1(sK4,k1_funct_1(sK5,sK3))),k5_relat_1(sK5,sK4))
    | ~ v1_funct_1(k5_relat_1(sK5,sK4))
    | ~ v1_relat_1(k5_relat_1(sK5,sK4)) ),
    inference(resolution,[],[f4377,f3866])).

fof(f3866,plain,(
    ~ sQ179_eqProxy(k1_funct_1(k5_relat_1(sK5,sK4),sK3),k1_funct_1(sK4,k1_funct_1(sK5,sK3))) ),
    inference(equality_proxy_replacement,[],[f2186,f3848])).

fof(f3848,plain,(
    ! [X1,X0] :
      ( sQ179_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ179_eqProxy])])).

fof(f2186,plain,(
    k1_funct_1(k5_relat_1(sK5,sK4),sK3) != k1_funct_1(sK4,k1_funct_1(sK5,sK3)) ),
    inference(cnf_transformation,[],[f1691])).

fof(f4377,plain,(
    ! [X2,X0,X1] :
      ( sQ179_eqProxy(k1_funct_1(X2,X0),X1)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_proxy_replacement,[],[f3165,f3848])).

fof(f3165,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2018])).

fof(f2018,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f2017])).

fof(f2017,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f1542])).

fof(f1542,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1541])).

fof(f1541,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f913])).

fof(f913,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
%------------------------------------------------------------------------------
