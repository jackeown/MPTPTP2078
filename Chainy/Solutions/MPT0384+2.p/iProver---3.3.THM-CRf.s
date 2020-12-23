%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0384+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:37 EST 2020

% Result     : Theorem 11.79s
% Output     : CNFRefutation 11.79s
% Verified   : 
% Statistics : Number of formulae       :   23 (  29 expanded)
%              Number of clauses        :    4 (   4 expanded)
%              Number of leaves         :    6 (   9 expanded)
%              Depth                    :   11
%              Number of atoms          :  116 ( 122 expanded)
%              Number of equality atoms :   53 (  59 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f543,conjecture,(
    k1_xboole_0 = k1_setfam_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f544,negated_conjecture,(
    k1_xboole_0 != k1_setfam_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f543])).

fof(f556,plain,(
    k1_xboole_0 != k1_setfam_1(k1_xboole_0) ),
    inference(flattening,[],[f544])).

fof(f2066,plain,(
    k1_xboole_0 != k1_setfam_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f556])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1209,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f2532,plain,(
    o_0_0_xboole_0 != k1_setfam_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f2066,f1209,f1209])).

fof(f540,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f891,plain,(
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
    inference(ennf_transformation,[],[f540])).

fof(f1196,plain,(
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
    inference(nnf_transformation,[],[f891])).

fof(f1197,plain,(
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
    inference(rectify,[],[f1196])).

fof(f1200,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK93(X0,X5))
        & r2_hidden(sK93(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1199,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(X2,sK92(X0,X1))
        & r2_hidden(sK92(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1198,plain,(
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
              ( ~ r2_hidden(sK91(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK91(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK91(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK91(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1201,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK91(X0,X1),sK92(X0,X1))
                  & r2_hidden(sK92(X0,X1),X0) )
                | ~ r2_hidden(sK91(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK91(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK91(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK93(X0,X5))
                    & r2_hidden(sK93(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK91,sK92,sK93])],[f1197,f1200,f1199,f1198])).

fof(f2063,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f1201])).

fof(f2525,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = X1
      | k1_setfam_1(X0) != X1
      | o_0_0_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f2063,f1209,f1209])).

fof(f2669,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = k1_setfam_1(X0)
      | o_0_0_xboole_0 != X0 ) ),
    inference(equality_resolution,[],[f2525])).

fof(f2670,plain,(
    o_0_0_xboole_0 = k1_setfam_1(o_0_0_xboole_0) ),
    inference(equality_resolution,[],[f2669])).

cnf(c_850,negated_conjecture,
    ( o_0_0_xboole_0 != k1_setfam_1(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2532])).

cnf(c_842,plain,
    ( k1_setfam_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2670])).

cnf(c_36968,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_850,c_842])).

cnf(c_36969,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_36968])).

%------------------------------------------------------------------------------
