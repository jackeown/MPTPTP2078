%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1041+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:44 EST 2020

% Result     : Theorem 0.98s
% Output     : CNFRefutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 333 expanded)
%              Number of clauses        :   43 (  92 expanded)
%              Number of leaves         :    4 (  88 expanded)
%              Depth                    :   22
%              Number of atoms          :  286 (2174 expanded)
%              Number of equality atoms :   72 ( 154 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r1_partfun1(X1,X2)
           => r2_hidden(X2,k5_partfun1(X0,X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r1_partfun1(X1,X2)
             => r2_hidden(X2,k5_partfun1(X0,X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,k5_partfun1(X0,X0,X1))
          & r1_partfun1(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,k5_partfun1(X0,X0,X1))
          & r1_partfun1(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,k5_partfun1(X0,X0,X1))
          & r1_partfun1(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
     => ( ~ r2_hidden(sK2,k5_partfun1(X0,X0,X1))
        & r1_partfun1(X1,sK2)
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(sK2,X0,X0)
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_hidden(X2,k5_partfun1(X0,X0,X1))
            & r1_partfun1(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_hidden(X2,k5_partfun1(sK0,sK0,sK1))
          & r1_partfun1(sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,
    ( ~ r2_hidden(sK2,k5_partfun1(sK0,sK0,sK1))
    & r1_partfun1(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f9,f8])).

fof(f16,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f18,plain,(
    r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f5,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f4])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | k1_xboole_0 != X0
      | ~ r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,k5_partfun1(k1_xboole_0,X1,X2))
      | ~ r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f12])).

fof(f19,plain,(
    ~ r2_hidden(sK2,k5_partfun1(sK0,sK0,sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f15,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f13,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | k1_xboole_0 = X1
      | ~ r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f14,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f17,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_5,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_3,negated_conjecture,
    ( r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_0,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r1_partfun1(X2,X0)
    | r2_hidden(X0,k5_partfun1(k1_xboole_0,X1,X2))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_2,negated_conjecture,
    ( ~ r2_hidden(sK2,k5_partfun1(sK0,sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_96,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r1_partfun1(X2,X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k5_partfun1(k1_xboole_0,X1,X2) != k5_partfun1(sK0,sK0,sK1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_2])).

cnf(c_97,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ r1_partfun1(X1,sK2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(sK2)
    | k5_partfun1(k1_xboole_0,X0,X1) != k5_partfun1(sK0,sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_96])).

cnf(c_6,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_101,plain,
    ( ~ v1_funct_1(X1)
    | ~ r1_partfun1(X1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ v1_funct_2(sK2,k1_xboole_0,X0)
    | k5_partfun1(k1_xboole_0,X0,X1) != k5_partfun1(sK0,sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_97,c_6])).

cnf(c_102,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ r1_partfun1(X1,sK2)
    | ~ v1_funct_1(X1)
    | k5_partfun1(k1_xboole_0,X0,X1) != k5_partfun1(sK0,sK0,sK1) ),
    inference(renaming,[status(thm)],[c_101])).

cnf(c_201,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ v1_funct_1(X1)
    | k5_partfun1(k1_xboole_0,X0,X1) != k5_partfun1(sK0,sK0,sK1)
    | sK1 != X1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_102])).

cnf(c_202,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ v1_funct_1(sK1)
    | k5_partfun1(k1_xboole_0,X0,sK1) != k5_partfun1(sK0,sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_201])).

cnf(c_8,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_206,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ v1_funct_2(sK2,k1_xboole_0,X0)
    | k5_partfun1(k1_xboole_0,X0,sK1) != k5_partfun1(sK0,sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_202,c_8])).

cnf(c_207,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | k5_partfun1(k1_xboole_0,X0,sK1) != k5_partfun1(sK0,sK0,sK1) ),
    inference(renaming,[status(thm)],[c_206])).

cnf(c_236,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | k5_partfun1(k1_xboole_0,X0,sK1) != k5_partfun1(sK0,sK0,sK1)
    | sK0 != X0
    | sK0 != k1_xboole_0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_207])).

cnf(c_237,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | k5_partfun1(k1_xboole_0,sK0,sK1) != k5_partfun1(sK0,sK0,sK1)
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_236])).

cnf(c_297,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | k5_partfun1(k1_xboole_0,sK0,sK1) != k5_partfun1(sK0,sK0,sK1)
    | sK0 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_237])).

cnf(c_377,plain,
    ( k5_partfun1(k1_xboole_0,sK0,sK1) != k5_partfun1(sK0,sK0,sK1)
    | sK0 != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_297])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_partfun1(X3,X0)
    | r2_hidden(X0,k5_partfun1(X1,X2,X3))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f11])).

cnf(c_126,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_partfun1(X3,X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k5_partfun1(X1,X2,X3) != k5_partfun1(sK0,sK0,sK1)
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_127,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_partfun1(X2,sK2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(sK2)
    | k5_partfun1(X0,X1,X2) != k5_partfun1(sK0,sK0,sK1)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_126])).

cnf(c_131,plain,
    ( ~ v1_funct_1(X2)
    | ~ r1_partfun1(X2,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k5_partfun1(X0,X1,X2) != k5_partfun1(sK0,sK0,sK1)
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_127,c_6])).

cnf(c_132,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_partfun1(X2,sK2)
    | ~ v1_funct_1(X2)
    | k5_partfun1(X0,X1,X2) != k5_partfun1(sK0,sK0,sK1)
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_131])).

cnf(c_174,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | k5_partfun1(X0,X1,X2) != k5_partfun1(sK0,sK0,sK1)
    | sK1 != X2
    | sK2 != sK2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_132])).

cnf(c_175,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK1)
    | k5_partfun1(X0,X1,sK1) != k5_partfun1(sK0,sK0,sK1)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_174])).

cnf(c_179,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k5_partfun1(X0,X1,sK1) != k5_partfun1(sK0,sK0,sK1)
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_175,c_8])).

cnf(c_180,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k5_partfun1(X0,X1,sK1) != k5_partfun1(sK0,sK0,sK1)
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_179])).

cnf(c_252,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k5_partfun1(X0,X1,sK1) != k5_partfun1(sK0,sK0,sK1)
    | sK0 != X0
    | sK0 != X1
    | sK2 != sK2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_180])).

cnf(c_253,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k5_partfun1(sK0,sK0,sK1) != k5_partfun1(sK0,sK0,sK1)
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_252])).

cnf(c_7,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_4,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_255,plain,
    ( k5_partfun1(sK0,sK0,sK1) != k5_partfun1(sK0,sK0,sK1)
    | k1_xboole_0 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_253,c_7,c_4])).

cnf(c_273,plain,
    ( k1_xboole_0 = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_255])).

cnf(c_296,plain,
    ( k1_xboole_0 = sK0 ),
    inference(subtyping,[status(esa)],[c_273])).

cnf(c_386,plain,
    ( k5_partfun1(k1_xboole_0,k1_xboole_0,sK1) != k5_partfun1(k1_xboole_0,k1_xboole_0,sK1)
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_377,c_296])).

cnf(c_387,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_386])).

cnf(c_299,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_375,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_299])).

cnf(c_380,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_375,c_296])).

cnf(c_298,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_376,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_298])).

cnf(c_383,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_376,c_296])).

cnf(c_390,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_387,c_380,c_383])).


%------------------------------------------------------------------------------
