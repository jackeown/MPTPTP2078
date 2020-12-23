%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0826+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:54 EST 2020

% Result     : Theorem 23.68s
% Output     : CNFRefutation 23.68s
% Verified   : 
% Statistics : Number of formulae       :   25 (  25 expanded)
%              Number of clauses        :    7 (   7 expanded)
%              Number of leaves         :    6 (   6 expanded)
%              Depth                    :    8
%              Number of atoms          :   70 (  70 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1235,conjecture,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1236,negated_conjecture,(
    ~ ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(negated_conjecture,[],[f1235])).

fof(f2503,plain,(
    ? [X0] : ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(ennf_transformation,[],[f1236])).

fof(f3381,plain,
    ( ? [X0] : ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
   => ~ m1_subset_1(k6_relat_1(sK324),k1_zfmisc_1(k2_zfmisc_1(sK324,sK324))) ),
    introduced(choice_axiom,[])).

fof(f3382,plain,(
    ~ m1_subset_1(k6_relat_1(sK324),k1_zfmisc_1(k2_zfmisc_1(sK324,sK324))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK324])],[f2503,f3381])).

fof(f5509,plain,(
    ~ m1_subset_1(k6_relat_1(sK324),k1_zfmisc_1(k2_zfmisc_1(sK324,sK324))) ),
    inference(cnf_transformation,[],[f3382])).

fof(f591,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1633,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f591])).

fof(f4334,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1633])).

fof(f285,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2638,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f285])).

fof(f2639,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f2638])).

fof(f2640,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK43(X0,X1),X0)
          | ~ r2_hidden(sK43(X0,X1),X1) )
        & ( r1_tarski(sK43(X0,X1),X0)
          | r2_hidden(sK43(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2641,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK43(X0,X1),X0)
            | ~ r2_hidden(sK43(X0,X1),X1) )
          & ( r1_tarski(sK43(X0,X1),X0)
            | r2_hidden(sK43(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK43])],[f2639,f2640])).

fof(f3756,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2641])).

fof(f6255,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f3756])).

fof(f1234,axiom,(
    ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5508,plain,(
    ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) ),
    inference(cnf_transformation,[],[f1234])).

cnf(c_2109,negated_conjecture,
    ( ~ m1_subset_1(k6_relat_1(sK324),k1_zfmisc_1(k2_zfmisc_1(sK324,sK324))) ),
    inference(cnf_transformation,[],[f5509])).

cnf(c_935,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f4334])).

cnf(c_78272,plain,
    ( ~ r2_hidden(k6_relat_1(sK324),k1_zfmisc_1(k2_zfmisc_1(sK324,sK324))) ),
    inference(resolution,[status(thm)],[c_2109,c_935])).

cnf(c_360,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f6255])).

cnf(c_78278,plain,
    ( ~ r1_tarski(k6_relat_1(sK324),k2_zfmisc_1(sK324,sK324)) ),
    inference(resolution,[status(thm)],[c_78272,c_360])).

cnf(c_2108,plain,
    ( r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) ),
    inference(cnf_transformation,[],[f5508])).

cnf(c_78282,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_78278,c_2108])).

%------------------------------------------------------------------------------
