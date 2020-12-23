%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0023+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:12 EST 2020

% Result     : Theorem 7.67s
% Output     : CNFRefutation 7.67s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 205 expanded)
%              Number of clauses        :   29 (  46 expanded)
%              Number of leaves         :    6 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  191 (1384 expanded)
%              Number of equality atoms :   27 ( 206 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f116,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f117,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f116])).

fof(f118,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f117])).

fof(f119,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f120,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f118,f119])).

fof(f171,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f120])).

fof(f267,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f171])).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f120])).

fof(f46,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(negated_conjecture,[],[f46])).

fof(f93,plain,(
    ? [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(ennf_transformation,[],[f47])).

fof(f150,plain,
    ( ? [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k3_xboole_0(X0,X1),X2)
   => k3_xboole_0(k3_xboole_0(sK14,sK15),sK16) != k3_xboole_0(sK14,k3_xboole_0(sK15,sK16)) ),
    introduced(choice_axiom,[])).

fof(f151,plain,(
    k3_xboole_0(k3_xboole_0(sK14,sK15),sK16) != k3_xboole_0(sK14,k3_xboole_0(sK15,sK16)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14,sK15,sK16])],[f93,f150])).

fof(f229,plain,(
    k3_xboole_0(k3_xboole_0(sK14,sK15),sK16) != k3_xboole_0(sK14,k3_xboole_0(sK15,sK16)) ),
    inference(cnf_transformation,[],[f151])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f66])).

fof(f140,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK10(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK10(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f79,f140])).

fof(f208,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f141])).

fof(f170,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f120])).

fof(f268,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f170])).

fof(f169,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f120])).

fof(f269,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f169])).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f120])).

fof(f174,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f267])).

cnf(c_9241,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),X0)
    | r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),k3_xboole_0(sK15,X0))
    | ~ r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),sK15) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_35987,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),k3_xboole_0(sK15,sK16))
    | ~ r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),sK16)
    | ~ r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),sK15) ),
    inference(instantiation,[status(thm)],[c_9241])).

cnf(c_6285,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),X0)
    | r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),k3_xboole_0(sK14,X0))
    | ~ r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),sK14) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_32493,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),k3_xboole_0(sK14,sK15))
    | ~ r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),sK15)
    | ~ r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),sK14) ),
    inference(instantiation,[status(thm)],[c_6285])).

cnf(c_32472,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),k3_xboole_0(sK15,sK16))
    | r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),k3_xboole_0(sK14,k3_xboole_0(sK15,sK16)))
    | ~ r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),sK14) ),
    inference(instantiation,[status(thm)],[c_6285])).

cnf(c_18,plain,
    ( r2_hidden(sK3(X0,X1,X2),X0)
    | r2_hidden(sK3(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f172])).

cnf(c_75,negated_conjecture,
    ( k3_xboole_0(k3_xboole_0(sK14,sK15),sK16) != k3_xboole_0(sK14,k3_xboole_0(sK15,sK16)) ),
    inference(cnf_transformation,[],[f229])).

cnf(c_24667,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),k3_xboole_0(sK14,k3_xboole_0(sK15,sK16)))
    | r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),k3_xboole_0(sK14,sK15)) ),
    inference(resolution,[status(thm)],[c_18,c_75])).

cnf(c_53,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f208])).

cnf(c_25511,plain,
    ( ~ r1_xboole_0(sK14,k3_xboole_0(sK15,sK16))
    | r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),k3_xboole_0(sK14,sK15)) ),
    inference(resolution,[status(thm)],[c_24667,c_53])).

cnf(c_20,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f268])).

cnf(c_26018,plain,
    ( ~ r1_xboole_0(sK14,k3_xboole_0(sK15,sK16))
    | r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),sK15) ),
    inference(resolution,[status(thm)],[c_25511,c_20])).

cnf(c_4171,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),k3_xboole_0(sK14,sK15))
    | r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),sK15) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_25507,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),k3_xboole_0(sK15,sK16))
    | r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),k3_xboole_0(sK14,sK15)) ),
    inference(resolution,[status(thm)],[c_24667,c_20])).

cnf(c_21,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f269])).

cnf(c_26507,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),k3_xboole_0(sK14,sK15))
    | r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),sK15) ),
    inference(resolution,[status(thm)],[c_25507,c_21])).

cnf(c_31598,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),sK15) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26018,c_4171,c_26507])).

cnf(c_25509,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),k3_xboole_0(sK14,sK15))
    | r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),sK14) ),
    inference(resolution,[status(thm)],[c_24667,c_21])).

cnf(c_4174,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),k3_xboole_0(sK14,sK15))
    | r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),sK14) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_26473,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),sK14) ),
    inference(global_propositional_subsumption,[status(thm)],[c_25509,c_4174])).

cnf(c_17,plain,
    ( r2_hidden(sK3(X0,X1,X2),X1)
    | r2_hidden(sK3(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f173])).

cnf(c_23990,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),k3_xboole_0(sK14,k3_xboole_0(sK15,sK16)))
    | r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),sK16) ),
    inference(resolution,[status(thm)],[c_17,c_75])).

cnf(c_3601,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),k3_xboole_0(sK15,sK16))
    | ~ r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_6229,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),k3_xboole_0(sK15,sK16))
    | r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),sK16) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_24802,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),sK16) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23990,c_3601,c_6229])).

cnf(c_16,plain,
    ( ~ r2_hidden(sK3(X0,X1,X2),X1)
    | ~ r2_hidden(sK3(X0,X1,X2),X0)
    | ~ r2_hidden(sK3(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f174])).

cnf(c_3588,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),k3_xboole_0(sK14,k3_xboole_0(sK15,sK16)))
    | ~ r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),k3_xboole_0(sK14,sK15))
    | ~ r2_hidden(sK3(k3_xboole_0(sK14,sK15),sK16,k3_xboole_0(sK14,k3_xboole_0(sK15,sK16))),sK16)
    | k3_xboole_0(k3_xboole_0(sK14,sK15),sK16) = k3_xboole_0(sK14,k3_xboole_0(sK15,sK16)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_35987,c_32493,c_32472,c_31598,c_26473,c_24802,c_3588,c_75])).

%------------------------------------------------------------------------------
