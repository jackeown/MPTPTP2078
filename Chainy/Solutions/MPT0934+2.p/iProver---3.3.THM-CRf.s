%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0934+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:58 EST 2020

% Result     : Theorem 39.16s
% Output     : CNFRefutation 39.16s
% Verified   : 
% Statistics : Number of formulae       :   38 (  92 expanded)
%              Number of clauses        :   15 (  17 expanded)
%              Number of leaves         :    6 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :  148 ( 568 expanded)
%              Number of equality atoms :   60 ( 258 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1413,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( ( k2_mcart_1(X0) = k2_mcart_1(X2)
            & k1_mcart_1(X0) = k1_mcart_1(X2)
            & r2_hidden(X0,X1)
            & r2_hidden(X2,X1) )
         => X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2847,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X0 = X2
          | k2_mcart_1(X0) != k2_mcart_1(X2)
          | k1_mcart_1(X0) != k1_mcart_1(X2)
          | ~ r2_hidden(X0,X1)
          | ~ r2_hidden(X2,X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1413])).

fof(f2848,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X0 = X2
          | k2_mcart_1(X0) != k2_mcart_1(X2)
          | k1_mcart_1(X0) != k1_mcart_1(X2)
          | ~ r2_hidden(X0,X1)
          | ~ r2_hidden(X2,X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2847])).

fof(f6514,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | k2_mcart_1(X0) != k2_mcart_1(X2)
      | k1_mcart_1(X0) != k1_mcart_1(X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2848])).

fof(f599,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1818,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f599])).

fof(f1819,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f1818])).

fof(f4924,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f1819])).

fof(f1414,conjecture,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ( k2_mcart_1(X1) = k2_mcart_1(X2)
                  & k1_mcart_1(X1) = k1_mcart_1(X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1415,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_relat_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ( ( k2_mcart_1(X1) = k2_mcart_1(X2)
                    & k1_mcart_1(X1) = k1_mcart_1(X2) )
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f1414])).

fof(f2849,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k2_mcart_1(X1) = k2_mcart_1(X2)
              & k1_mcart_1(X1) = k1_mcart_1(X2)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,X0) )
      & v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1415])).

fof(f2850,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k2_mcart_1(X1) = k2_mcart_1(X2)
              & k1_mcart_1(X1) = k1_mcart_1(X2)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,X0) )
      & v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f2849])).

fof(f3963,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k2_mcart_1(X1) = k2_mcart_1(X2)
          & k1_mcart_1(X1) = k1_mcart_1(X2)
          & m1_subset_1(X2,X0) )
     => ( sK460 != X1
        & k2_mcart_1(sK460) = k2_mcart_1(X1)
        & k1_mcart_1(sK460) = k1_mcart_1(X1)
        & m1_subset_1(sK460,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f3962,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k2_mcart_1(X1) = k2_mcart_1(X2)
              & k1_mcart_1(X1) = k1_mcart_1(X2)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,X0) )
     => ( ? [X2] :
            ( sK459 != X2
            & k2_mcart_1(sK459) = k2_mcart_1(X2)
            & k1_mcart_1(sK459) = k1_mcart_1(X2)
            & m1_subset_1(X2,X0) )
        & m1_subset_1(sK459,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f3961,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & k2_mcart_1(X1) = k2_mcart_1(X2)
                & k1_mcart_1(X1) = k1_mcart_1(X2)
                & m1_subset_1(X2,X0) )
            & m1_subset_1(X1,X0) )
        & v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k2_mcart_1(X1) = k2_mcart_1(X2)
              & k1_mcart_1(X1) = k1_mcart_1(X2)
              & m1_subset_1(X2,sK458) )
          & m1_subset_1(X1,sK458) )
      & v1_relat_1(sK458)
      & ~ v1_xboole_0(sK458) ) ),
    introduced(choice_axiom,[])).

fof(f3964,plain,
    ( sK459 != sK460
    & k2_mcart_1(sK459) = k2_mcart_1(sK460)
    & k1_mcart_1(sK459) = k1_mcart_1(sK460)
    & m1_subset_1(sK460,sK458)
    & m1_subset_1(sK459,sK458)
    & v1_relat_1(sK458)
    & ~ v1_xboole_0(sK458) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK458,sK459,sK460])],[f2850,f3963,f3962,f3961])).

fof(f6521,plain,(
    sK459 != sK460 ),
    inference(cnf_transformation,[],[f3964])).

fof(f6520,plain,(
    k2_mcart_1(sK459) = k2_mcart_1(sK460) ),
    inference(cnf_transformation,[],[f3964])).

fof(f6519,plain,(
    k1_mcart_1(sK459) = k1_mcart_1(sK460) ),
    inference(cnf_transformation,[],[f3964])).

fof(f6518,plain,(
    m1_subset_1(sK460,sK458) ),
    inference(cnf_transformation,[],[f3964])).

fof(f6517,plain,(
    m1_subset_1(sK459,sK458) ),
    inference(cnf_transformation,[],[f3964])).

fof(f6516,plain,(
    v1_relat_1(sK458) ),
    inference(cnf_transformation,[],[f3964])).

fof(f6515,plain,(
    ~ v1_xboole_0(sK458) ),
    inference(cnf_transformation,[],[f3964])).

cnf(c_2524,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ v1_relat_1(X1)
    | X2 = X0
    | k2_mcart_1(X2) != k2_mcart_1(X0)
    | k1_mcart_1(X2) != k1_mcart_1(X0) ),
    inference(cnf_transformation,[],[f6514])).

cnf(c_114526,plain,
    ( ~ r2_hidden(sK460,X0)
    | ~ r2_hidden(sK459,X0)
    | ~ v1_relat_1(X0)
    | k2_mcart_1(sK459) != k2_mcart_1(sK460)
    | k1_mcart_1(sK459) != k1_mcart_1(sK460)
    | sK459 = sK460 ),
    inference(instantiation,[status(thm)],[c_2524])).

cnf(c_144785,plain,
    ( ~ r2_hidden(sK460,sK458)
    | ~ r2_hidden(sK459,sK458)
    | ~ v1_relat_1(sK458)
    | k2_mcart_1(sK459) != k2_mcart_1(sK460)
    | k1_mcart_1(sK459) != k1_mcart_1(sK460)
    | sK459 = sK460 ),
    inference(instantiation,[status(thm)],[c_114526])).

cnf(c_943,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f4924])).

cnf(c_114967,plain,
    ( ~ m1_subset_1(X0,sK458)
    | r2_hidden(X0,sK458)
    | v1_xboole_0(sK458) ),
    inference(instantiation,[status(thm)],[c_943])).

cnf(c_136831,plain,
    ( ~ m1_subset_1(sK459,sK458)
    | r2_hidden(sK459,sK458)
    | v1_xboole_0(sK458) ),
    inference(instantiation,[status(thm)],[c_114967])).

cnf(c_136828,plain,
    ( ~ m1_subset_1(sK460,sK458)
    | r2_hidden(sK460,sK458)
    | v1_xboole_0(sK458) ),
    inference(instantiation,[status(thm)],[c_114967])).

cnf(c_2525,negated_conjecture,
    ( sK459 != sK460 ),
    inference(cnf_transformation,[],[f6521])).

cnf(c_2526,negated_conjecture,
    ( k2_mcart_1(sK459) = k2_mcart_1(sK460) ),
    inference(cnf_transformation,[],[f6520])).

cnf(c_2527,negated_conjecture,
    ( k1_mcart_1(sK459) = k1_mcart_1(sK460) ),
    inference(cnf_transformation,[],[f6519])).

cnf(c_2528,negated_conjecture,
    ( m1_subset_1(sK460,sK458) ),
    inference(cnf_transformation,[],[f6518])).

cnf(c_2529,negated_conjecture,
    ( m1_subset_1(sK459,sK458) ),
    inference(cnf_transformation,[],[f6517])).

cnf(c_2530,negated_conjecture,
    ( v1_relat_1(sK458) ),
    inference(cnf_transformation,[],[f6516])).

cnf(c_2531,negated_conjecture,
    ( ~ v1_xboole_0(sK458) ),
    inference(cnf_transformation,[],[f6515])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_144785,c_136831,c_136828,c_2525,c_2526,c_2527,c_2528,c_2529,c_2530,c_2531])).

%------------------------------------------------------------------------------
