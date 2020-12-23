%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0388+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:27 EST 2020

% Result     : Theorem 2.09s
% Output     : Refutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   43 (  93 expanded)
%              Number of leaves         :    9 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :  202 ( 475 expanded)
%              Number of equality atoms :   49 ( 115 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2026,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2018,f830])).

fof(f830,plain,(
    r2_hidden(sK10(sK1,k1_setfam_1(sK0)),sK1) ),
    inference(resolution,[],[f639,f709])).

fof(f709,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK10(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f624])).

fof(f624,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK10(X0,X1),X1)
          & r2_hidden(sK10(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f622,f623])).

fof(f623,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK10(X0,X1),X1)
        & r2_hidden(sK10(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f622,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f621])).

fof(f621,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f590])).

fof(f590,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f639,plain,(
    ~ r1_tarski(sK1,k1_setfam_1(sK0)) ),
    inference(cnf_transformation,[],[f596])).

fof(f596,plain,
    ( ~ r1_tarski(sK1,k1_setfam_1(sK0))
    & k1_xboole_0 != sK0
    & ! [X2] :
        ( r1_tarski(sK1,X2)
        | ~ r2_hidden(X2,sK0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f561,f595])).

fof(f595,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X1,k1_setfam_1(X0))
        & k1_xboole_0 != X0
        & ! [X2] :
            ( r1_tarski(X1,X2)
            | ~ r2_hidden(X2,X0) ) )
   => ( ~ r1_tarski(sK1,k1_setfam_1(sK0))
      & k1_xboole_0 != sK0
      & ! [X2] :
          ( r1_tarski(sK1,X2)
          | ~ r2_hidden(X2,sK0) ) ) ),
    introduced(choice_axiom,[])).

fof(f561,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X1,k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f560])).

fof(f560,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X1,k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f559])).

fof(f559,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ! [X2] :
            ( r2_hidden(X2,X0)
           => r1_tarski(X1,X2) )
       => ( r1_tarski(X1,k1_setfam_1(X0))
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f558])).

fof(f558,conjecture,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f2018,plain,(
    ~ r2_hidden(sK10(sK1,k1_setfam_1(sK0)),sK1) ),
    inference(resolution,[],[f1280,f831])).

fof(f831,plain,(
    ~ r2_hidden(sK10(sK1,k1_setfam_1(sK0)),k1_setfam_1(sK0)) ),
    inference(resolution,[],[f639,f710])).

fof(f710,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK10(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f624])).

fof(f1280,plain,(
    ! [X34] :
      ( r2_hidden(X34,k1_setfam_1(sK0))
      | ~ r2_hidden(X34,sK1) ) ),
    inference(subsumption_resolution,[],[f1261,f808])).

fof(f808,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK0,X1),sK0)
      | r2_hidden(X1,k1_setfam_1(sK0)) ) ),
    inference(resolution,[],[f744,f751])).

fof(f751,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | r2_hidden(sK4(X0,X5),X0)
      | sQ14_eqProxy(k1_xboole_0,X0) ) ),
    inference(equality_proxy_replacement,[],[f732,f743])).

fof(f743,plain,(
    ! [X1,X0] :
      ( sQ14_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ14_eqProxy])])).

fof(f732,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | r2_hidden(sK4(X0,X5),X0)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f642])).

fof(f642,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(sK4(X0,X5),X0)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f602])).

fof(f602,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK2(X0,X1),sK3(X0,X1))
                  & r2_hidden(sK3(X0,X1),X0) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK2(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK2(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK4(X0,X5))
                    & r2_hidden(sK4(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f598,f601,f600,f599])).

fof(f599,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(X2,X3)
                & r2_hidden(X3,X0) )
            | ~ r2_hidden(X2,X1) )
          & ( ! [X4] :
                ( r2_hidden(X2,X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(X2,X1) ) )
     => ( ( ? [X3] :
              ( ~ r2_hidden(sK2(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK2(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f600,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(sK2(X0,X1),X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f601,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK4(X0,X5))
        & r2_hidden(sK4(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f598,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r2_hidden(X4,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ? [X6] :
                      ( ~ r2_hidden(X5,X6)
                      & r2_hidden(X6,X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(rectify,[],[f597])).

fof(f597,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f563])).

fof(f563,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f544])).

fof(f544,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f744,plain,(
    ~ sQ14_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f638,f743])).

fof(f638,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f596])).

fof(f1261,plain,(
    ! [X34] :
      ( ~ r2_hidden(sK4(sK0,X34),sK0)
      | ~ r2_hidden(X34,sK1)
      | r2_hidden(X34,k1_setfam_1(sK0)) ) ),
    inference(resolution,[],[f857,f807])).

fof(f807,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK4(sK0,X0))
      | r2_hidden(X0,k1_setfam_1(sK0)) ) ),
    inference(resolution,[],[f744,f750])).

fof(f750,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | ~ r2_hidden(X5,sK4(X0,X5))
      | sQ14_eqProxy(k1_xboole_0,X0) ) ),
    inference(equality_proxy_replacement,[],[f731,f743])).

fof(f731,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | ~ r2_hidden(X5,sK4(X0,X5))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f643])).

fof(f643,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X5,sK4(X0,X5))
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f602])).

fof(f857,plain,(
    ! [X19,X18] :
      ( r2_hidden(X19,X18)
      | ~ r2_hidden(X18,sK0)
      | ~ r2_hidden(X19,sK1) ) ),
    inference(resolution,[],[f637,f708])).

fof(f708,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f624])).

fof(f637,plain,(
    ! [X2] :
      ( r1_tarski(sK1,X2)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(cnf_transformation,[],[f596])).
%------------------------------------------------------------------------------
