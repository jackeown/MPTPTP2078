%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0845+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:53 EST 2020

% Result     : Theorem 2.19s
% Output     : Refutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   39 (  87 expanded)
%              Number of leaves         :   10 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  107 ( 260 expanded)
%              Number of equality atoms :   12 (  38 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7698,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f7462,f7461,f7419])).

fof(f7419,plain,(
    ! [X3,X1] :
      ( ~ r2_hidden(X3,sK238(X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(condensation,[],[f4855])).

fof(f4855,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK238(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f3212])).

fof(f3212,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK238(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK238(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK238])],[f2171,f3211])).

fof(f3211,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK238(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK238(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f2171,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f433])).

fof(f433,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(f7461,plain,(
    r2_hidden(sK157(sK7,sK238(sK7)),sK238(sK7)) ),
    inference(resolution,[],[f7444,f4266])).

fof(f4266,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK157(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f2959])).

fof(f2959,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK157(X0,X1),X1)
          & r2_hidden(sK157(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK157])],[f1700,f2958])).

fof(f2958,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK157(X0,X1),X1)
        & r2_hidden(sK157(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1700,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f1292])).

fof(f1292,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f7444,plain,(
    ~ r1_xboole_0(sK7,sK238(sK7)) ),
    inference(resolution,[],[f7441,f7430])).

fof(f7430,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK7)
      | ~ r1_xboole_0(sK7,X0) ) ),
    inference(resolution,[],[f4431,f3454])).

fof(f3454,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,sK7)
      | ~ r2_hidden(X1,sK7) ) ),
    inference(cnf_transformation,[],[f2606])).

fof(f2606,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK7)
        | ~ r2_hidden(X1,sK7) )
    & k1_xboole_0 != sK7 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f1303,f2605])).

fof(f2605,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ~ r1_xboole_0(X1,X0)
            | ~ r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 )
   => ( ! [X1] :
          ( ~ r1_xboole_0(X1,sK7)
          | ~ r2_hidden(X1,sK7) )
      & k1_xboole_0 != sK7 ) ),
    introduced(choice_axiom,[])).

fof(f1303,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ r1_xboole_0(X1,X0)
          | ~ r2_hidden(X1,X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f1274])).

fof(f1274,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ~ ( r1_xboole_0(X1,X0)
                & r2_hidden(X1,X0) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f1273])).

fof(f1273,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f4431,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1865])).

fof(f1865,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f7441,plain,(
    r2_hidden(sK238(sK7),sK7) ),
    inference(resolution,[],[f7438,f4854])).

fof(f4854,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK238(X1),X1) ) ),
    inference(cnf_transformation,[],[f3212])).

fof(f7438,plain,(
    r2_hidden(sK129(sK7),sK7) ),
    inference(resolution,[],[f6206,f5948])).

fof(f5948,plain,(
    ~ sQ321_eqProxy(k1_xboole_0,sK7) ),
    inference(equality_proxy_replacement,[],[f3453,f5929])).

fof(f5929,plain,(
    ! [X1,X0] :
      ( sQ321_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ321_eqProxy])])).

fof(f3453,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f2606])).

fof(f6206,plain,(
    ! [X0] :
      ( sQ321_eqProxy(k1_xboole_0,X0)
      | r2_hidden(sK129(X0),X0) ) ),
    inference(equality_proxy_replacement,[],[f4105,f5929])).

fof(f4105,plain,(
    ! [X0] :
      ( r2_hidden(sK129(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f2897])).

fof(f2897,plain,(
    ! [X0] :
      ( r2_hidden(sK129(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK129])],[f1682,f2896])).

fof(f2896,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK129(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1682,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f7462,plain,(
    r2_hidden(sK157(sK7,sK238(sK7)),sK7) ),
    inference(resolution,[],[f7444,f4265])).

fof(f4265,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK157(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f2959])).
%------------------------------------------------------------------------------
