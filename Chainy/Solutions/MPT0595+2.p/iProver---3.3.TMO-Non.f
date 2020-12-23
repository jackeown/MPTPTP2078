%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0595+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:47 EST 2020

% Result     : Timeout 59.43s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   33 (  79 expanded)
%              Number of clauses        :   17 (  19 expanded)
%              Number of leaves         :    6 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :   94 ( 353 expanded)
%              Number of equality atoms :   50 ( 164 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f789,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k2_relat_1(X0) = k2_relat_1(X1)
               => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f790,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => ( k2_relat_1(X0) = k2_relat_1(X1)
                 => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f789])).

fof(f1462,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) != k2_relat_1(k5_relat_1(X1,X2))
              & k2_relat_1(X0) = k2_relat_1(X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f790])).

fof(f1463,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) != k2_relat_1(k5_relat_1(X1,X2))
              & k2_relat_1(X0) = k2_relat_1(X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1462])).

fof(f2002,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k2_relat_1(k5_relat_1(X0,X2)) != k2_relat_1(k5_relat_1(X1,X2))
          & k2_relat_1(X0) = k2_relat_1(X1)
          & v1_relat_1(X2) )
     => ( k2_relat_1(k5_relat_1(X0,sK163)) != k2_relat_1(k5_relat_1(X1,sK163))
        & k2_relat_1(X0) = k2_relat_1(X1)
        & v1_relat_1(sK163) ) ) ),
    introduced(choice_axiom,[])).

fof(f2001,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) != k2_relat_1(k5_relat_1(X1,X2))
              & k2_relat_1(X0) = k2_relat_1(X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( k2_relat_1(k5_relat_1(sK162,X2)) != k2_relat_1(k5_relat_1(X0,X2))
            & k2_relat_1(sK162) = k2_relat_1(X0)
            & v1_relat_1(X2) )
        & v1_relat_1(sK162) ) ) ),
    introduced(choice_axiom,[])).

fof(f2000,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_relat_1(k5_relat_1(X0,X2)) != k2_relat_1(k5_relat_1(X1,X2))
                & k2_relat_1(X0) = k2_relat_1(X1)
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_relat_1(k5_relat_1(sK161,X2)) != k2_relat_1(k5_relat_1(X1,X2))
              & k2_relat_1(sK161) = k2_relat_1(X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK161) ) ),
    introduced(choice_axiom,[])).

fof(f2003,plain,
    ( k2_relat_1(k5_relat_1(sK161,sK163)) != k2_relat_1(k5_relat_1(sK162,sK163))
    & k2_relat_1(sK161) = k2_relat_1(sK162)
    & v1_relat_1(sK163)
    & v1_relat_1(sK162)
    & v1_relat_1(sK161) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK161,sK162,sK163])],[f1463,f2002,f2001,f2000])).

fof(f3239,plain,(
    v1_relat_1(sK163) ),
    inference(cnf_transformation,[],[f2003])).

fof(f3238,plain,(
    v1_relat_1(sK162) ),
    inference(cnf_transformation,[],[f2003])).

fof(f751,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1415,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f751])).

fof(f3192,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1415])).

fof(f3240,plain,(
    k2_relat_1(sK161) = k2_relat_1(sK162) ),
    inference(cnf_transformation,[],[f2003])).

fof(f3241,plain,(
    k2_relat_1(k5_relat_1(sK161,sK163)) != k2_relat_1(k5_relat_1(sK162,sK163)) ),
    inference(cnf_transformation,[],[f2003])).

fof(f3237,plain,(
    v1_relat_1(sK161) ),
    inference(cnf_transformation,[],[f2003])).

cnf(c_1207,negated_conjecture,
    ( v1_relat_1(sK163) ),
    inference(cnf_transformation,[],[f3239])).

cnf(c_35401,plain,
    ( v1_relat_1(sK163) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1207])).

cnf(c_1208,negated_conjecture,
    ( v1_relat_1(sK162) ),
    inference(cnf_transformation,[],[f3238])).

cnf(c_35400,plain,
    ( v1_relat_1(sK162) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1208])).

cnf(c_1160,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3192])).

cnf(c_35439,plain,
    ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1160])).

cnf(c_198128,plain,
    ( k2_relat_1(k5_relat_1(sK162,X0)) = k9_relat_1(X0,k2_relat_1(sK162))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_35400,c_35439])).

cnf(c_1206,negated_conjecture,
    ( k2_relat_1(sK161) = k2_relat_1(sK162) ),
    inference(cnf_transformation,[],[f3240])).

cnf(c_198149,plain,
    ( k2_relat_1(k5_relat_1(sK162,X0)) = k9_relat_1(X0,k2_relat_1(sK161))
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_198128,c_1206])).

cnf(c_198902,plain,
    ( k2_relat_1(k5_relat_1(sK162,sK163)) = k9_relat_1(sK163,k2_relat_1(sK161)) ),
    inference(superposition,[status(thm)],[c_35401,c_198149])).

cnf(c_63980,plain,
    ( ~ v1_relat_1(sK163)
    | ~ v1_relat_1(sK161)
    | k2_relat_1(k5_relat_1(sK161,sK163)) = k9_relat_1(sK163,k2_relat_1(sK161)) ),
    inference(instantiation,[status(thm)],[c_1160])).

cnf(c_17632,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_46434,plain,
    ( k2_relat_1(k5_relat_1(sK162,sK163)) != X0
    | k2_relat_1(k5_relat_1(sK161,sK163)) != X0
    | k2_relat_1(k5_relat_1(sK161,sK163)) = k2_relat_1(k5_relat_1(sK162,sK163)) ),
    inference(instantiation,[status(thm)],[c_17632])).

cnf(c_63979,plain,
    ( k2_relat_1(k5_relat_1(sK162,sK163)) != k9_relat_1(sK163,k2_relat_1(sK161))
    | k2_relat_1(k5_relat_1(sK161,sK163)) != k9_relat_1(sK163,k2_relat_1(sK161))
    | k2_relat_1(k5_relat_1(sK161,sK163)) = k2_relat_1(k5_relat_1(sK162,sK163)) ),
    inference(instantiation,[status(thm)],[c_46434])).

cnf(c_1205,negated_conjecture,
    ( k2_relat_1(k5_relat_1(sK161,sK163)) != k2_relat_1(k5_relat_1(sK162,sK163)) ),
    inference(cnf_transformation,[],[f3241])).

cnf(c_1209,negated_conjecture,
    ( v1_relat_1(sK161) ),
    inference(cnf_transformation,[],[f3237])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_198902,c_63980,c_63979,c_1205,c_1207,c_1209])).

%------------------------------------------------------------------------------
