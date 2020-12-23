%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0721+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:50 EST 2020

% Result     : Theorem 23.59s
% Output     : CNFRefutation 23.59s
% Verified   : 
% Statistics : Number of formulae       :   28 (  52 expanded)
%              Number of clauses        :   10 (  10 expanded)
%              Number of leaves         :    4 (  12 expanded)
%              Depth                    :    7
%              Number of atoms          :   86 ( 226 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f994,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1953,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f994])).

fof(f1954,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1953])).

fof(f4285,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1954])).

fof(f591,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1436,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f591])).

fof(f3659,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1436])).

fof(f998,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f999,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
       => ( r2_hidden(X1,k1_relat_1(X2))
         => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f998])).

fof(f1961,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_subset_1(k1_funct_1(X2,X1),X0)
      & r2_hidden(X1,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v5_relat_1(X2,X0)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f999])).

fof(f1962,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_subset_1(k1_funct_1(X2,X1),X0)
      & r2_hidden(X1,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v5_relat_1(X2,X0)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1961])).

fof(f2654,plain,
    ( ? [X0,X1,X2] :
        ( ~ m1_subset_1(k1_funct_1(X2,X1),X0)
        & r2_hidden(X1,k1_relat_1(X2))
        & v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
   => ( ~ m1_subset_1(k1_funct_1(sK220,sK219),sK218)
      & r2_hidden(sK219,k1_relat_1(sK220))
      & v1_funct_1(sK220)
      & v5_relat_1(sK220,sK218)
      & v1_relat_1(sK220) ) ),
    introduced(choice_axiom,[])).

fof(f2655,plain,
    ( ~ m1_subset_1(k1_funct_1(sK220,sK219),sK218)
    & r2_hidden(sK219,k1_relat_1(sK220))
    & v1_funct_1(sK220)
    & v5_relat_1(sK220,sK218)
    & v1_relat_1(sK220) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK218,sK219,sK220])],[f1962,f2654])).

fof(f4293,plain,(
    ~ m1_subset_1(k1_funct_1(sK220,sK219),sK218) ),
    inference(cnf_transformation,[],[f2655])).

fof(f4292,plain,(
    r2_hidden(sK219,k1_relat_1(sK220)) ),
    inference(cnf_transformation,[],[f2655])).

fof(f4291,plain,(
    v1_funct_1(sK220) ),
    inference(cnf_transformation,[],[f2655])).

fof(f4290,plain,(
    v5_relat_1(sK220,sK218) ),
    inference(cnf_transformation,[],[f2655])).

fof(f4289,plain,(
    v1_relat_1(sK220) ),
    inference(cnf_transformation,[],[f2655])).

cnf(c_1561,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4285])).

cnf(c_74148,plain,
    ( ~ v5_relat_1(sK220,sK218)
    | r2_hidden(k1_funct_1(sK220,sK219),sK218)
    | ~ r2_hidden(sK219,k1_relat_1(sK220))
    | ~ v1_funct_1(sK220)
    | ~ v1_relat_1(sK220) ),
    inference(instantiation,[status(thm)],[c_1561])).

cnf(c_935,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f3659])).

cnf(c_73551,plain,
    ( m1_subset_1(k1_funct_1(sK220,sK219),sK218)
    | ~ r2_hidden(k1_funct_1(sK220,sK219),sK218) ),
    inference(instantiation,[status(thm)],[c_935])).

cnf(c_1565,negated_conjecture,
    ( ~ m1_subset_1(k1_funct_1(sK220,sK219),sK218) ),
    inference(cnf_transformation,[],[f4293])).

cnf(c_1566,negated_conjecture,
    ( r2_hidden(sK219,k1_relat_1(sK220)) ),
    inference(cnf_transformation,[],[f4292])).

cnf(c_1567,negated_conjecture,
    ( v1_funct_1(sK220) ),
    inference(cnf_transformation,[],[f4291])).

cnf(c_1568,negated_conjecture,
    ( v5_relat_1(sK220,sK218) ),
    inference(cnf_transformation,[],[f4290])).

cnf(c_1569,negated_conjecture,
    ( v1_relat_1(sK220) ),
    inference(cnf_transformation,[],[f4289])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_74148,c_73551,c_1565,c_1566,c_1567,c_1568,c_1569])).

%------------------------------------------------------------------------------
