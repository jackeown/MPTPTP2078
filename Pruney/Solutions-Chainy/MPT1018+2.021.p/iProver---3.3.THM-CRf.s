%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:02 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :  198 (146719 expanded)
%              Number of clauses        :  151 (40751 expanded)
%              Number of leaves         :   12 (37788 expanded)
%              Depth                    :   45
%              Number of atoms          :  658 (951381 expanded)
%              Number of equality atoms :  455 (315064 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( sK2 != sK3
        & k1_funct_1(X1,sK2) = k1_funct_1(X1,sK3)
        & r2_hidden(sK3,X0)
        & r2_hidden(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        & v2_funct_1(X1)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X3,X2] :
          ( X2 != X3
          & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
          & r2_hidden(X3,sK0)
          & r2_hidden(X2,sK0) )
      & v2_funct_1(sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( sK2 != sK3
    & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    & r2_hidden(sK3,sK0)
    & r2_hidden(sK2,sK0)
    & v2_funct_1(sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f24,f23])).

fof(f44,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f13])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f46,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f48,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f49,plain,(
    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f17])).

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f19])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f11])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f39])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f59,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f37])).

fof(f50,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f25])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_21,negated_conjecture,
    ( v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_270,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
    | sK1 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_271,plain,
    ( ~ v1_funct_2(sK1,X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK1)
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X2)) = X2
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_270])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_275,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,X0)
    | ~ v1_funct_2(sK1,X0,X1)
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X2)) = X2
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_271,c_24])).

cnf(c_276,plain,
    ( ~ v1_funct_2(sK1,X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X2)) = X2
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_275])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_321,plain,
    ( ~ v1_funct_2(sK1,X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X2)) = X2
    | sK0 != X0
    | sK2 != X2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_276,c_20])).

cnf(c_322,plain,
    ( ~ v1_funct_2(sK1,sK0,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_321])).

cnf(c_888,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
    | sK0 != X0
    | sK0 != sK0
    | sK1 != sK1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_322])).

cnf(c_889,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_888])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_891,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
    | k1_xboole_0 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_889,c_22])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_303,plain,
    ( ~ v1_funct_2(sK1,X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X2)) = X2
    | sK0 != X0
    | sK3 != X2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_276,c_19])).

cnf(c_304,plain,
    ( ~ v1_funct_2(sK1,sK0,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) = sK3
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_899,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) = sK3
    | sK0 != X0
    | sK0 != sK0
    | sK1 != sK1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_304])).

cnf(c_900,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) = sK3
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_899])).

cnf(c_902,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) = sK3
    | k1_xboole_0 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_900,c_22])).

cnf(c_18,negated_conjecture,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1474,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3
    | sK0 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_902,c_18])).

cnf(c_1618,plain,
    ( sK0 = k1_xboole_0
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_891,c_1474])).

cnf(c_1449,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1451,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2366,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1449,c_1451])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1455,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4589,plain,
    ( k2_zfmisc_1(sK0,sK0) = sK1
    | r1_tarski(k2_zfmisc_1(sK0,sK0),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2366,c_1455])).

cnf(c_4833,plain,
    ( k2_zfmisc_1(sK0,sK0) = sK1
    | sK3 = sK2
    | r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1618,c_4589])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_4838,plain,
    ( k2_zfmisc_1(sK0,sK0) = sK1
    | sK3 = sK2
    | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4833,c_5])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_2122,plain,
    ( r1_tarski(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2125,plain,
    ( r1_tarski(k1_xboole_0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2122])).

cnf(c_5026,plain,
    ( sK3 = sK2
    | k2_zfmisc_1(sK0,sK0) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4838,c_2125])).

cnf(c_5027,plain,
    ( k2_zfmisc_1(sK0,sK0) = sK1
    | sK3 = sK2 ),
    inference(renaming,[status(thm)],[c_5026])).

cnf(c_5031,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = sK1
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_1618,c_5027])).

cnf(c_5083,plain,
    ( sK1 = k1_xboole_0
    | sK3 = sK2 ),
    inference(demodulation,[status(thm)],[c_5031,c_5])).

cnf(c_5361,plain,
    ( k1_funct_1(k1_xboole_0,sK3) = k1_funct_1(sK1,sK2)
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_5083,c_18])).

cnf(c_1703,plain,
    ( sK3 = sK2
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1618,c_1449])).

cnf(c_1972,plain,
    ( sK3 = sK2
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1703,c_5])).

cnf(c_2367,plain,
    ( sK3 = sK2
    | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1972,c_1451])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1452,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1450,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2515,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1452,c_1450])).

cnf(c_2945,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_2515])).

cnf(c_3098,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK1) = k1_relat_1(sK1)
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_2367,c_2945])).

cnf(c_13,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_870,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X3)))
    | X3 != X2
    | k1_relset_1(X1,X2,X0) != X1
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) = sK3
    | sK0 != X1
    | sK1 != X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_304])).

cnf(c_871,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | k1_relset_1(sK0,X0,sK1) != sK0
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) = sK3
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_870])).

cnf(c_1441,plain,
    ( k1_relset_1(sK0,X0,sK1) != sK0
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) = sK3
    | k1_xboole_0 = X0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_871])).

cnf(c_1528,plain,
    ( k1_relset_1(sK0,X0,sK1) != sK0
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3
    | k1_xboole_0 = X0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1441,c_18])).

cnf(c_1700,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK1) != sK0
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3
    | sK3 = sK2
    | k1_xboole_0 = X0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1618,c_1528])).

cnf(c_3325,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3
    | k1_relat_1(sK1) != sK0
    | sK3 = sK2
    | k1_xboole_0 = X0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3098,c_1700])).

cnf(c_12,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_817,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
    | X2 != X1
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) = sK3
    | sK0 != k1_xboole_0
    | sK1 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_304])).

cnf(c_818,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | k1_relset_1(k1_xboole_0,X0,sK1) != k1_xboole_0
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) = sK3
    | sK0 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_817])).

cnf(c_1078,plain,
    ( sP0_iProver_split
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) = sK3
    | sK0 != k1_xboole_0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_818])).

cnf(c_1443,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) = sK3
    | sK0 != k1_xboole_0
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1078])).

cnf(c_1497,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3
    | sK0 != k1_xboole_0
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1443,c_18])).

cnf(c_1501,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3
    | sP0_iProver_split = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1497,c_1474])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_780,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK0 != X1
    | sK0 != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_781,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | k1_relset_1(k1_xboole_0,sK0,sK1) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_780])).

cnf(c_1447,plain,
    ( k1_relset_1(k1_xboole_0,sK0,sK1) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_781])).

cnf(c_1520,plain,
    ( k1_relset_1(k1_xboole_0,sK0,sK1) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1447,c_5])).

cnf(c_2101,plain,
    ( k1_relset_1(k1_xboole_0,sK0,sK1) = k1_xboole_0
    | sK3 = sK2
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1618,c_1520])).

cnf(c_2233,plain,
    ( sK3 = sK2
    | k1_relset_1(k1_xboole_0,sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2101,c_1972])).

cnf(c_2234,plain,
    ( k1_relset_1(k1_xboole_0,sK0,sK1) = k1_xboole_0
    | sK3 = sK2 ),
    inference(renaming,[status(thm)],[c_2233])).

cnf(c_2237,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) = k1_xboole_0
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_1618,c_2234])).

cnf(c_2516,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1449,c_1450])).

cnf(c_2609,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) = k1_relat_1(sK1)
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_1618,c_2516])).

cnf(c_2765,plain,
    ( k1_relat_1(sK1) = k1_xboole_0
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_2237,c_2609])).

cnf(c_1077,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | k1_relset_1(k1_xboole_0,X0,sK1) != k1_xboole_0
    | k1_xboole_0 = X0
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_818])).

cnf(c_1444,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK1) != k1_xboole_0
    | k1_xboole_0 = X0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1077])).

cnf(c_1545,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK1) != k1_xboole_0
    | k1_xboole_0 = X0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1444,c_5])).

cnf(c_3323,plain,
    ( k1_relat_1(sK1) != k1_xboole_0
    | sK3 = sK2
    | k1_xboole_0 = X0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3098,c_1545])).

cnf(c_3548,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3
    | sK3 = sK2
    | k1_xboole_0 = X0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3325,c_1501,c_1972,c_2765,c_3323])).

cnf(c_3559,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3
    | sK3 = sK2
    | k1_xboole_0 = X0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1618,c_3548])).

cnf(c_3564,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3
    | sK3 = sK2
    | k1_xboole_0 = X0
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3559,c_5])).

cnf(c_3580,plain,
    ( k1_xboole_0 = X0
    | sK3 = sK2
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3564,c_1972])).

cnf(c_3581,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3
    | sK3 = sK2
    | k1_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_3580])).

cnf(c_3666,plain,
    ( k1_relset_1(sK0,sK0,k1_xboole_0) = k1_relat_1(sK1)
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_3581,c_2516])).

cnf(c_5517,plain,
    ( k1_relset_1(sK0,sK0,k1_xboole_0) = k1_relat_1(sK1)
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(k1_xboole_0,sK3)) = sK3
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_5361,c_3666])).

cnf(c_17,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1082,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1598,plain,
    ( sK3 != X0
    | sK2 != X0
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_1082])).

cnf(c_3525,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1598])).

cnf(c_5345,plain,
    ( k1_relset_1(sK0,sK0,k1_xboole_0) = k1_relat_1(sK1)
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_5083,c_2516])).

cnf(c_1081,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6002,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1081])).

cnf(c_6079,plain,
    ( k1_relset_1(sK0,sK0,k1_xboole_0) = k1_relat_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5517,c_17,c_3525,c_5345,c_6002])).

cnf(c_3681,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3
    | sK3 = sK2
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3581,c_1449])).

cnf(c_4818,plain,
    ( k1_relset_1(sK0,sK0,k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_3681,c_1450])).

cnf(c_5516,plain,
    ( k1_relset_1(sK0,sK0,k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(k1_xboole_0,sK3)) = sK3
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_5361,c_4818])).

cnf(c_5035,plain,
    ( k1_relset_1(sK0,sK0,X0) = k1_relat_1(X0)
    | sK3 = sK2
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5027,c_2515])).

cnf(c_5087,plain,
    ( k1_relset_1(sK0,sK0,k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | sK3 = sK2
    | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5035])).

cnf(c_6008,plain,
    ( k1_relset_1(sK0,sK0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5516,c_17,c_2125,c_3525,c_5087,c_6002])).

cnf(c_6081,plain,
    ( k1_relat_1(sK1) = k1_relat_1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_6079,c_6008])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_841,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK0 != X2
    | sK1 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_23])).

cnf(c_842,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_relset_1(sK0,sK0,sK1) = sK0
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_841])).

cnf(c_844,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0
    | k1_xboole_0 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_842,c_22])).

cnf(c_2611,plain,
    ( k1_relat_1(sK1) = sK0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2516,c_844])).

cnf(c_6110,plain,
    ( k1_relat_1(k1_xboole_0) = sK0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6081,c_2611])).

cnf(c_7402,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6110,c_17,c_1618,c_3525,c_6002])).

cnf(c_852,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X3)))
    | X3 != X2
    | k1_relset_1(X1,X2,X0) != X1
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
    | sK0 != X1
    | sK1 != X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_322])).

cnf(c_853,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | k1_relset_1(sK0,X0,sK1) != sK0
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_852])).

cnf(c_1442,plain,
    ( k1_relset_1(sK0,X0,sK1) != sK0
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
    | k1_xboole_0 = X0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_853])).

cnf(c_1795,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK1) != sK0
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
    | sK3 = sK2
    | k1_xboole_0 = X0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1618,c_1442])).

cnf(c_7413,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK1) != k1_xboole_0
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
    | sK3 = sK2
    | k1_xboole_0 = X0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7402,c_1795])).

cnf(c_7439,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK1) != k1_xboole_0
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
    | sK3 = sK2
    | k1_xboole_0 = X0
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7413,c_5])).

cnf(c_5187,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | k1_xboole_0 = X0
    | sK3 = sK2
    | sP0_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3323,c_1972,c_2765])).

cnf(c_5188,plain,
    ( sK3 = sK2
    | k1_xboole_0 = X0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(renaming,[status(thm)],[c_5187])).

cnf(c_5200,plain,
    ( sK3 = sK2
    | k1_xboole_0 = X0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1618,c_5188])).

cnf(c_5205,plain,
    ( sK3 = sK2
    | k1_xboole_0 = X0
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5200,c_5])).

cnf(c_7410,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = sK1
    | r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7402,c_4589])).

cnf(c_7454,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7410,c_5])).

cnf(c_4590,plain,
    ( sK1 = k1_xboole_0
    | sK3 = sK2
    | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2367,c_1455])).

cnf(c_7552,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7454,c_17,c_2125,c_3525,c_4590,c_6002])).

cnf(c_3594,plain,
    ( X0 = X1
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_3581,c_3581])).

cnf(c_6115,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3594,c_17,c_3525,c_6002])).

cnf(c_6116,plain,
    ( X0 = X1
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3 ),
    inference(renaming,[status(thm)],[c_6115])).

cnf(c_6130,plain,
    ( X0 = X1
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(k1_xboole_0,sK3)) = sK3
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_5361,c_6116])).

cnf(c_6989,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(k1_xboole_0,sK3)) = sK3
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6130,c_17,c_3525,c_6002])).

cnf(c_6990,plain,
    ( X0 = X1
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(k1_xboole_0,sK3)) = sK3 ),
    inference(renaming,[status(thm)],[c_6989])).

cnf(c_7310,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(k1_xboole_0,sK3)) = sK3
    | sK3 != X0 ),
    inference(equality_factoring,[status(thm)],[c_6990])).

cnf(c_7325,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(k1_xboole_0,sK3)) = sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7310,c_6990])).

cnf(c_7557,plain,
    ( k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK3)) = sK3 ),
    inference(demodulation,[status(thm)],[c_7552,c_7325])).

cnf(c_7569,plain,
    ( k1_funct_1(k1_xboole_0,sK3) = k1_funct_1(k1_xboole_0,sK2) ),
    inference(demodulation,[status(thm)],[c_7552,c_18])).

cnf(c_7588,plain,
    ( k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK2)) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_7557,c_7569])).

cnf(c_793,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
    | X2 != X1
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
    | sK0 != k1_xboole_0
    | sK1 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_322])).

cnf(c_794,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | k1_relset_1(k1_xboole_0,X0,sK1) != k1_xboole_0
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
    | sK0 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_793])).

cnf(c_1079,plain,
    ( sP0_iProver_split
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
    | sK0 != k1_xboole_0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_794])).

cnf(c_1445,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
    | sK0 != k1_xboole_0
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1079])).

cnf(c_27,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1103,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
    | sK0 != k1_xboole_0
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1079])).

cnf(c_1794,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
    | sK0 = k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_844,c_1442])).

cnf(c_2226,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
    | sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1445,c_27,c_1103,c_1794])).

cnf(c_7565,plain,
    ( k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK2)) = sK2
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_7552,c_2226])).

cnf(c_7590,plain,
    ( sK3 = sK2
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_7588,c_7565])).

cnf(c_7628,plain,
    ( k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7439,c_17,c_1972,c_3525,c_5205,c_6002,c_7590])).

cnf(c_7689,plain,
    ( X0 = X1 ),
    inference(superposition,[status(thm)],[c_7628,c_7628])).

cnf(c_7638,plain,
    ( sK3 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7628,c_17])).

cnf(c_8558,plain,
    ( k1_xboole_0 != X0 ),
    inference(superposition,[status(thm)],[c_7689,c_7638])).

cnf(c_8582,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8558,c_7689])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:49:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.78/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/0.98  
% 2.78/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.78/0.98  
% 2.78/0.98  ------  iProver source info
% 2.78/0.98  
% 2.78/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.78/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.78/0.98  git: non_committed_changes: false
% 2.78/0.98  git: last_make_outside_of_git: false
% 2.78/0.98  
% 2.78/0.98  ------ 
% 2.78/0.98  
% 2.78/0.98  ------ Input Options
% 2.78/0.98  
% 2.78/0.98  --out_options                           all
% 2.78/0.98  --tptp_safe_out                         true
% 2.78/0.98  --problem_path                          ""
% 2.78/0.98  --include_path                          ""
% 2.78/0.98  --clausifier                            res/vclausify_rel
% 2.78/0.98  --clausifier_options                    --mode clausify
% 2.78/0.98  --stdin                                 false
% 2.78/0.98  --stats_out                             all
% 2.78/0.98  
% 2.78/0.98  ------ General Options
% 2.78/0.98  
% 2.78/0.98  --fof                                   false
% 2.78/0.98  --time_out_real                         305.
% 2.78/0.98  --time_out_virtual                      -1.
% 2.78/0.98  --symbol_type_check                     false
% 2.78/0.98  --clausify_out                          false
% 2.78/0.98  --sig_cnt_out                           false
% 2.78/0.98  --trig_cnt_out                          false
% 2.78/0.98  --trig_cnt_out_tolerance                1.
% 2.78/0.98  --trig_cnt_out_sk_spl                   false
% 2.78/0.98  --abstr_cl_out                          false
% 2.78/0.98  
% 2.78/0.98  ------ Global Options
% 2.78/0.98  
% 2.78/0.98  --schedule                              default
% 2.78/0.98  --add_important_lit                     false
% 2.78/0.98  --prop_solver_per_cl                    1000
% 2.78/0.98  --min_unsat_core                        false
% 2.78/0.98  --soft_assumptions                      false
% 2.78/0.98  --soft_lemma_size                       3
% 2.78/0.98  --prop_impl_unit_size                   0
% 2.78/0.98  --prop_impl_unit                        []
% 2.78/0.98  --share_sel_clauses                     true
% 2.78/0.98  --reset_solvers                         false
% 2.78/0.98  --bc_imp_inh                            [conj_cone]
% 2.78/0.98  --conj_cone_tolerance                   3.
% 2.78/0.98  --extra_neg_conj                        none
% 2.78/0.98  --large_theory_mode                     true
% 2.78/0.98  --prolific_symb_bound                   200
% 2.78/0.98  --lt_threshold                          2000
% 2.78/0.98  --clause_weak_htbl                      true
% 2.78/0.98  --gc_record_bc_elim                     false
% 2.78/0.98  
% 2.78/0.98  ------ Preprocessing Options
% 2.78/0.98  
% 2.78/0.98  --preprocessing_flag                    true
% 2.78/0.98  --time_out_prep_mult                    0.1
% 2.78/0.98  --splitting_mode                        input
% 2.78/0.98  --splitting_grd                         true
% 2.78/0.98  --splitting_cvd                         false
% 2.78/0.98  --splitting_cvd_svl                     false
% 2.78/0.98  --splitting_nvd                         32
% 2.78/0.98  --sub_typing                            true
% 2.78/0.98  --prep_gs_sim                           true
% 2.78/0.98  --prep_unflatten                        true
% 2.78/0.98  --prep_res_sim                          true
% 2.78/0.98  --prep_upred                            true
% 2.78/0.98  --prep_sem_filter                       exhaustive
% 2.78/0.98  --prep_sem_filter_out                   false
% 2.78/0.98  --pred_elim                             true
% 2.78/0.98  --res_sim_input                         true
% 2.78/0.98  --eq_ax_congr_red                       true
% 2.78/0.98  --pure_diseq_elim                       true
% 2.78/0.98  --brand_transform                       false
% 2.78/0.98  --non_eq_to_eq                          false
% 2.78/0.98  --prep_def_merge                        true
% 2.78/0.98  --prep_def_merge_prop_impl              false
% 2.78/0.98  --prep_def_merge_mbd                    true
% 2.78/0.98  --prep_def_merge_tr_red                 false
% 2.78/0.98  --prep_def_merge_tr_cl                  false
% 2.78/0.98  --smt_preprocessing                     true
% 2.78/0.98  --smt_ac_axioms                         fast
% 2.78/0.98  --preprocessed_out                      false
% 2.78/0.98  --preprocessed_stats                    false
% 2.78/0.98  
% 2.78/0.98  ------ Abstraction refinement Options
% 2.78/0.98  
% 2.78/0.98  --abstr_ref                             []
% 2.78/0.98  --abstr_ref_prep                        false
% 2.78/0.98  --abstr_ref_until_sat                   false
% 2.78/0.98  --abstr_ref_sig_restrict                funpre
% 2.78/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.78/0.98  --abstr_ref_under                       []
% 2.78/0.98  
% 2.78/0.98  ------ SAT Options
% 2.78/0.98  
% 2.78/0.98  --sat_mode                              false
% 2.78/0.98  --sat_fm_restart_options                ""
% 2.78/0.98  --sat_gr_def                            false
% 2.78/0.98  --sat_epr_types                         true
% 2.78/0.98  --sat_non_cyclic_types                  false
% 2.78/0.98  --sat_finite_models                     false
% 2.78/0.98  --sat_fm_lemmas                         false
% 2.78/0.98  --sat_fm_prep                           false
% 2.78/0.98  --sat_fm_uc_incr                        true
% 2.78/0.98  --sat_out_model                         small
% 2.78/0.98  --sat_out_clauses                       false
% 2.78/0.98  
% 2.78/0.98  ------ QBF Options
% 2.78/0.98  
% 2.78/0.98  --qbf_mode                              false
% 2.78/0.98  --qbf_elim_univ                         false
% 2.78/0.98  --qbf_dom_inst                          none
% 2.78/0.98  --qbf_dom_pre_inst                      false
% 2.78/0.98  --qbf_sk_in                             false
% 2.78/0.98  --qbf_pred_elim                         true
% 2.78/0.98  --qbf_split                             512
% 2.78/0.98  
% 2.78/0.98  ------ BMC1 Options
% 2.78/0.98  
% 2.78/0.98  --bmc1_incremental                      false
% 2.78/0.98  --bmc1_axioms                           reachable_all
% 2.78/0.98  --bmc1_min_bound                        0
% 2.78/0.98  --bmc1_max_bound                        -1
% 2.78/0.98  --bmc1_max_bound_default                -1
% 2.78/0.98  --bmc1_symbol_reachability              true
% 2.78/0.98  --bmc1_property_lemmas                  false
% 2.78/0.98  --bmc1_k_induction                      false
% 2.78/0.98  --bmc1_non_equiv_states                 false
% 2.78/0.98  --bmc1_deadlock                         false
% 2.78/0.98  --bmc1_ucm                              false
% 2.78/0.98  --bmc1_add_unsat_core                   none
% 2.78/0.98  --bmc1_unsat_core_children              false
% 2.78/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.78/0.98  --bmc1_out_stat                         full
% 2.78/0.98  --bmc1_ground_init                      false
% 2.78/0.98  --bmc1_pre_inst_next_state              false
% 2.78/0.98  --bmc1_pre_inst_state                   false
% 2.78/0.98  --bmc1_pre_inst_reach_state             false
% 2.78/0.98  --bmc1_out_unsat_core                   false
% 2.78/0.98  --bmc1_aig_witness_out                  false
% 2.78/0.98  --bmc1_verbose                          false
% 2.78/0.98  --bmc1_dump_clauses_tptp                false
% 2.78/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.78/0.98  --bmc1_dump_file                        -
% 2.78/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.78/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.78/0.98  --bmc1_ucm_extend_mode                  1
% 2.78/0.98  --bmc1_ucm_init_mode                    2
% 2.78/0.98  --bmc1_ucm_cone_mode                    none
% 2.78/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.78/0.98  --bmc1_ucm_relax_model                  4
% 2.78/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.78/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.78/0.98  --bmc1_ucm_layered_model                none
% 2.78/0.98  --bmc1_ucm_max_lemma_size               10
% 2.78/0.98  
% 2.78/0.98  ------ AIG Options
% 2.78/0.98  
% 2.78/0.98  --aig_mode                              false
% 2.78/0.98  
% 2.78/0.98  ------ Instantiation Options
% 2.78/0.98  
% 2.78/0.98  --instantiation_flag                    true
% 2.78/0.98  --inst_sos_flag                         false
% 2.78/0.98  --inst_sos_phase                        true
% 2.78/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.78/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.78/0.98  --inst_lit_sel_side                     num_symb
% 2.78/0.98  --inst_solver_per_active                1400
% 2.78/0.98  --inst_solver_calls_frac                1.
% 2.78/0.98  --inst_passive_queue_type               priority_queues
% 2.78/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.78/0.98  --inst_passive_queues_freq              [25;2]
% 2.78/0.98  --inst_dismatching                      true
% 2.78/0.98  --inst_eager_unprocessed_to_passive     true
% 2.78/0.98  --inst_prop_sim_given                   true
% 2.78/0.98  --inst_prop_sim_new                     false
% 2.78/0.98  --inst_subs_new                         false
% 2.78/0.98  --inst_eq_res_simp                      false
% 2.78/0.98  --inst_subs_given                       false
% 2.78/0.98  --inst_orphan_elimination               true
% 2.78/0.98  --inst_learning_loop_flag               true
% 2.78/0.98  --inst_learning_start                   3000
% 2.78/0.98  --inst_learning_factor                  2
% 2.78/0.98  --inst_start_prop_sim_after_learn       3
% 2.78/0.98  --inst_sel_renew                        solver
% 2.78/0.98  --inst_lit_activity_flag                true
% 2.78/0.98  --inst_restr_to_given                   false
% 2.78/0.98  --inst_activity_threshold               500
% 2.78/0.98  --inst_out_proof                        true
% 2.78/0.98  
% 2.78/0.98  ------ Resolution Options
% 2.78/0.98  
% 2.78/0.98  --resolution_flag                       true
% 2.78/0.98  --res_lit_sel                           adaptive
% 2.78/0.98  --res_lit_sel_side                      none
% 2.78/0.98  --res_ordering                          kbo
% 2.78/0.98  --res_to_prop_solver                    active
% 2.78/0.98  --res_prop_simpl_new                    false
% 2.78/0.98  --res_prop_simpl_given                  true
% 2.78/0.98  --res_passive_queue_type                priority_queues
% 2.78/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.78/0.98  --res_passive_queues_freq               [15;5]
% 2.78/0.98  --res_forward_subs                      full
% 2.78/0.98  --res_backward_subs                     full
% 2.78/0.98  --res_forward_subs_resolution           true
% 2.78/0.98  --res_backward_subs_resolution          true
% 2.78/0.98  --res_orphan_elimination                true
% 2.78/0.98  --res_time_limit                        2.
% 2.78/0.98  --res_out_proof                         true
% 2.78/0.98  
% 2.78/0.98  ------ Superposition Options
% 2.78/0.98  
% 2.78/0.98  --superposition_flag                    true
% 2.78/0.98  --sup_passive_queue_type                priority_queues
% 2.78/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.78/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.78/0.98  --demod_completeness_check              fast
% 2.78/0.98  --demod_use_ground                      true
% 2.78/0.98  --sup_to_prop_solver                    passive
% 2.78/0.98  --sup_prop_simpl_new                    true
% 2.78/0.98  --sup_prop_simpl_given                  true
% 2.78/0.98  --sup_fun_splitting                     false
% 2.78/0.98  --sup_smt_interval                      50000
% 2.78/0.98  
% 2.78/0.98  ------ Superposition Simplification Setup
% 2.78/0.98  
% 2.78/0.98  --sup_indices_passive                   []
% 2.78/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.78/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/0.98  --sup_full_bw                           [BwDemod]
% 2.78/0.98  --sup_immed_triv                        [TrivRules]
% 2.78/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.78/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/0.98  --sup_immed_bw_main                     []
% 2.78/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.78/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/0.98  
% 2.78/0.98  ------ Combination Options
% 2.78/0.98  
% 2.78/0.98  --comb_res_mult                         3
% 2.78/0.98  --comb_sup_mult                         2
% 2.78/0.98  --comb_inst_mult                        10
% 2.78/0.98  
% 2.78/0.98  ------ Debug Options
% 2.78/0.98  
% 2.78/0.98  --dbg_backtrace                         false
% 2.78/0.98  --dbg_dump_prop_clauses                 false
% 2.78/0.98  --dbg_dump_prop_clauses_file            -
% 2.78/0.98  --dbg_out_stat                          false
% 2.78/0.98  ------ Parsing...
% 2.78/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.78/0.98  
% 2.78/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.78/0.98  
% 2.78/0.98  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.78/0.98  
% 2.78/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.78/0.98  ------ Proving...
% 2.78/0.98  ------ Problem Properties 
% 2.78/0.98  
% 2.78/0.98  
% 2.78/0.98  clauses                                 23
% 2.78/0.98  conjectures                             3
% 2.78/0.98  EPR                                     4
% 2.78/0.98  Horn                                    14
% 2.78/0.98  unary                                   7
% 2.78/0.98  binary                                  6
% 2.78/0.98  lits                                    56
% 2.78/0.98  lits eq                                 34
% 2.78/0.98  fd_pure                                 0
% 2.78/0.98  fd_pseudo                               0
% 2.78/0.98  fd_cond                                 5
% 2.78/0.98  fd_pseudo_cond                          1
% 2.78/0.98  AC symbols                              0
% 2.78/0.98  
% 2.78/0.98  ------ Schedule dynamic 5 is on 
% 2.78/0.98  
% 2.78/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.78/0.98  
% 2.78/0.98  
% 2.78/0.98  ------ 
% 2.78/0.98  Current options:
% 2.78/0.98  ------ 
% 2.78/0.98  
% 2.78/0.98  ------ Input Options
% 2.78/0.98  
% 2.78/0.98  --out_options                           all
% 2.78/0.98  --tptp_safe_out                         true
% 2.78/0.98  --problem_path                          ""
% 2.78/0.98  --include_path                          ""
% 2.78/0.98  --clausifier                            res/vclausify_rel
% 2.78/0.98  --clausifier_options                    --mode clausify
% 2.78/0.98  --stdin                                 false
% 2.78/0.98  --stats_out                             all
% 2.78/0.98  
% 2.78/0.98  ------ General Options
% 2.78/0.98  
% 2.78/0.98  --fof                                   false
% 2.78/0.98  --time_out_real                         305.
% 2.78/0.98  --time_out_virtual                      -1.
% 2.78/0.98  --symbol_type_check                     false
% 2.78/0.98  --clausify_out                          false
% 2.78/0.98  --sig_cnt_out                           false
% 2.78/0.98  --trig_cnt_out                          false
% 2.78/0.98  --trig_cnt_out_tolerance                1.
% 2.78/0.98  --trig_cnt_out_sk_spl                   false
% 2.78/0.98  --abstr_cl_out                          false
% 2.78/0.98  
% 2.78/0.98  ------ Global Options
% 2.78/0.98  
% 2.78/0.98  --schedule                              default
% 2.78/0.98  --add_important_lit                     false
% 2.78/0.98  --prop_solver_per_cl                    1000
% 2.78/0.98  --min_unsat_core                        false
% 2.78/0.98  --soft_assumptions                      false
% 2.78/0.98  --soft_lemma_size                       3
% 2.78/0.98  --prop_impl_unit_size                   0
% 2.78/0.98  --prop_impl_unit                        []
% 2.78/0.98  --share_sel_clauses                     true
% 2.78/0.98  --reset_solvers                         false
% 2.78/0.98  --bc_imp_inh                            [conj_cone]
% 2.78/0.98  --conj_cone_tolerance                   3.
% 2.78/0.98  --extra_neg_conj                        none
% 2.78/0.98  --large_theory_mode                     true
% 2.78/0.98  --prolific_symb_bound                   200
% 2.78/0.98  --lt_threshold                          2000
% 2.78/0.98  --clause_weak_htbl                      true
% 2.78/0.98  --gc_record_bc_elim                     false
% 2.78/0.98  
% 2.78/0.98  ------ Preprocessing Options
% 2.78/0.98  
% 2.78/0.98  --preprocessing_flag                    true
% 2.78/0.98  --time_out_prep_mult                    0.1
% 2.78/0.98  --splitting_mode                        input
% 2.78/0.98  --splitting_grd                         true
% 2.78/0.98  --splitting_cvd                         false
% 2.78/0.98  --splitting_cvd_svl                     false
% 2.78/0.98  --splitting_nvd                         32
% 2.78/0.98  --sub_typing                            true
% 2.78/0.98  --prep_gs_sim                           true
% 2.78/0.98  --prep_unflatten                        true
% 2.78/0.98  --prep_res_sim                          true
% 2.78/0.98  --prep_upred                            true
% 2.78/0.98  --prep_sem_filter                       exhaustive
% 2.78/0.98  --prep_sem_filter_out                   false
% 2.78/0.98  --pred_elim                             true
% 2.78/0.98  --res_sim_input                         true
% 2.78/0.98  --eq_ax_congr_red                       true
% 2.78/0.98  --pure_diseq_elim                       true
% 2.78/0.98  --brand_transform                       false
% 2.78/0.98  --non_eq_to_eq                          false
% 2.78/0.98  --prep_def_merge                        true
% 2.78/0.98  --prep_def_merge_prop_impl              false
% 2.78/0.98  --prep_def_merge_mbd                    true
% 2.78/0.98  --prep_def_merge_tr_red                 false
% 2.78/0.98  --prep_def_merge_tr_cl                  false
% 2.78/0.98  --smt_preprocessing                     true
% 2.78/0.98  --smt_ac_axioms                         fast
% 2.78/0.98  --preprocessed_out                      false
% 2.78/0.98  --preprocessed_stats                    false
% 2.78/0.98  
% 2.78/0.98  ------ Abstraction refinement Options
% 2.78/0.98  
% 2.78/0.98  --abstr_ref                             []
% 2.78/0.98  --abstr_ref_prep                        false
% 2.78/0.98  --abstr_ref_until_sat                   false
% 2.78/0.98  --abstr_ref_sig_restrict                funpre
% 2.78/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.78/0.98  --abstr_ref_under                       []
% 2.78/0.98  
% 2.78/0.98  ------ SAT Options
% 2.78/0.98  
% 2.78/0.98  --sat_mode                              false
% 2.78/0.98  --sat_fm_restart_options                ""
% 2.78/0.98  --sat_gr_def                            false
% 2.78/0.98  --sat_epr_types                         true
% 2.78/0.98  --sat_non_cyclic_types                  false
% 2.78/0.98  --sat_finite_models                     false
% 2.78/0.98  --sat_fm_lemmas                         false
% 2.78/0.98  --sat_fm_prep                           false
% 2.78/0.98  --sat_fm_uc_incr                        true
% 2.78/0.98  --sat_out_model                         small
% 2.78/0.98  --sat_out_clauses                       false
% 2.78/0.98  
% 2.78/0.98  ------ QBF Options
% 2.78/0.98  
% 2.78/0.98  --qbf_mode                              false
% 2.78/0.98  --qbf_elim_univ                         false
% 2.78/0.98  --qbf_dom_inst                          none
% 2.78/0.98  --qbf_dom_pre_inst                      false
% 2.78/0.98  --qbf_sk_in                             false
% 2.78/0.98  --qbf_pred_elim                         true
% 2.78/0.98  --qbf_split                             512
% 2.78/0.98  
% 2.78/0.98  ------ BMC1 Options
% 2.78/0.98  
% 2.78/0.98  --bmc1_incremental                      false
% 2.78/0.98  --bmc1_axioms                           reachable_all
% 2.78/0.98  --bmc1_min_bound                        0
% 2.78/0.98  --bmc1_max_bound                        -1
% 2.78/0.98  --bmc1_max_bound_default                -1
% 2.78/0.98  --bmc1_symbol_reachability              true
% 2.78/0.98  --bmc1_property_lemmas                  false
% 2.78/0.98  --bmc1_k_induction                      false
% 2.78/0.98  --bmc1_non_equiv_states                 false
% 2.78/0.98  --bmc1_deadlock                         false
% 2.78/0.98  --bmc1_ucm                              false
% 2.78/0.98  --bmc1_add_unsat_core                   none
% 2.78/0.98  --bmc1_unsat_core_children              false
% 2.78/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.78/0.98  --bmc1_out_stat                         full
% 2.78/0.98  --bmc1_ground_init                      false
% 2.78/0.98  --bmc1_pre_inst_next_state              false
% 2.78/0.98  --bmc1_pre_inst_state                   false
% 2.78/0.98  --bmc1_pre_inst_reach_state             false
% 2.78/0.98  --bmc1_out_unsat_core                   false
% 2.78/0.98  --bmc1_aig_witness_out                  false
% 2.78/0.98  --bmc1_verbose                          false
% 2.78/0.98  --bmc1_dump_clauses_tptp                false
% 2.78/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.78/0.98  --bmc1_dump_file                        -
% 2.78/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.78/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.78/0.98  --bmc1_ucm_extend_mode                  1
% 2.78/0.98  --bmc1_ucm_init_mode                    2
% 2.78/0.98  --bmc1_ucm_cone_mode                    none
% 2.78/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.78/0.98  --bmc1_ucm_relax_model                  4
% 2.78/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.78/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.78/0.98  --bmc1_ucm_layered_model                none
% 2.78/0.98  --bmc1_ucm_max_lemma_size               10
% 2.78/0.98  
% 2.78/0.98  ------ AIG Options
% 2.78/0.98  
% 2.78/0.98  --aig_mode                              false
% 2.78/0.98  
% 2.78/0.98  ------ Instantiation Options
% 2.78/0.98  
% 2.78/0.98  --instantiation_flag                    true
% 2.78/0.98  --inst_sos_flag                         false
% 2.78/0.98  --inst_sos_phase                        true
% 2.78/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.78/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.78/0.98  --inst_lit_sel_side                     none
% 2.78/0.98  --inst_solver_per_active                1400
% 2.78/0.98  --inst_solver_calls_frac                1.
% 2.78/0.98  --inst_passive_queue_type               priority_queues
% 2.78/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.78/0.98  --inst_passive_queues_freq              [25;2]
% 2.78/0.98  --inst_dismatching                      true
% 2.78/0.98  --inst_eager_unprocessed_to_passive     true
% 2.78/0.98  --inst_prop_sim_given                   true
% 2.78/0.98  --inst_prop_sim_new                     false
% 2.78/0.98  --inst_subs_new                         false
% 2.78/0.98  --inst_eq_res_simp                      false
% 2.78/0.98  --inst_subs_given                       false
% 2.78/0.98  --inst_orphan_elimination               true
% 2.78/0.98  --inst_learning_loop_flag               true
% 2.78/0.98  --inst_learning_start                   3000
% 2.78/0.98  --inst_learning_factor                  2
% 2.78/0.98  --inst_start_prop_sim_after_learn       3
% 2.78/0.98  --inst_sel_renew                        solver
% 2.78/0.98  --inst_lit_activity_flag                true
% 2.78/0.98  --inst_restr_to_given                   false
% 2.78/0.98  --inst_activity_threshold               500
% 2.78/0.98  --inst_out_proof                        true
% 2.78/0.98  
% 2.78/0.98  ------ Resolution Options
% 2.78/0.98  
% 2.78/0.98  --resolution_flag                       false
% 2.78/0.98  --res_lit_sel                           adaptive
% 2.78/0.98  --res_lit_sel_side                      none
% 2.78/0.98  --res_ordering                          kbo
% 2.78/0.98  --res_to_prop_solver                    active
% 2.78/0.98  --res_prop_simpl_new                    false
% 2.78/0.98  --res_prop_simpl_given                  true
% 2.78/0.98  --res_passive_queue_type                priority_queues
% 2.78/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.78/0.98  --res_passive_queues_freq               [15;5]
% 2.78/0.98  --res_forward_subs                      full
% 2.78/0.98  --res_backward_subs                     full
% 2.78/0.98  --res_forward_subs_resolution           true
% 2.78/0.98  --res_backward_subs_resolution          true
% 2.78/0.98  --res_orphan_elimination                true
% 2.78/0.98  --res_time_limit                        2.
% 2.78/0.98  --res_out_proof                         true
% 2.78/0.98  
% 2.78/0.98  ------ Superposition Options
% 2.78/0.98  
% 2.78/0.98  --superposition_flag                    true
% 2.78/0.98  --sup_passive_queue_type                priority_queues
% 2.78/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.78/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.78/0.98  --demod_completeness_check              fast
% 2.78/0.98  --demod_use_ground                      true
% 2.78/0.98  --sup_to_prop_solver                    passive
% 2.78/0.98  --sup_prop_simpl_new                    true
% 2.78/0.98  --sup_prop_simpl_given                  true
% 2.78/0.98  --sup_fun_splitting                     false
% 2.78/0.98  --sup_smt_interval                      50000
% 2.78/0.98  
% 2.78/0.98  ------ Superposition Simplification Setup
% 2.78/0.98  
% 2.78/0.98  --sup_indices_passive                   []
% 2.78/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.78/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/0.98  --sup_full_bw                           [BwDemod]
% 2.78/0.98  --sup_immed_triv                        [TrivRules]
% 2.78/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.78/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/0.98  --sup_immed_bw_main                     []
% 2.78/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.78/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/0.98  
% 2.78/0.98  ------ Combination Options
% 2.78/0.98  
% 2.78/0.98  --comb_res_mult                         3
% 2.78/0.98  --comb_sup_mult                         2
% 2.78/0.98  --comb_inst_mult                        10
% 2.78/0.98  
% 2.78/0.98  ------ Debug Options
% 2.78/0.98  
% 2.78/0.98  --dbg_backtrace                         false
% 2.78/0.98  --dbg_dump_prop_clauses                 false
% 2.78/0.98  --dbg_dump_prop_clauses_file            -
% 2.78/0.98  --dbg_out_stat                          false
% 2.78/0.98  
% 2.78/0.98  
% 2.78/0.98  
% 2.78/0.98  
% 2.78/0.98  ------ Proving...
% 2.78/0.98  
% 2.78/0.98  
% 2.78/0.98  % SZS status Theorem for theBenchmark.p
% 2.78/0.98  
% 2.78/0.98   Resolution empty clause
% 2.78/0.98  
% 2.78/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.78/0.98  
% 2.78/0.98  fof(f8,conjecture,(
% 2.78/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 2.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.98  
% 2.78/0.98  fof(f9,negated_conjecture,(
% 2.78/0.98    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 2.78/0.98    inference(negated_conjecture,[],[f8])).
% 2.78/0.98  
% 2.78/0.98  fof(f15,plain,(
% 2.78/0.98    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & (k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0))) & v2_funct_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.78/0.98    inference(ennf_transformation,[],[f9])).
% 2.78/0.98  
% 2.78/0.98  fof(f16,plain,(
% 2.78/0.98    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.78/0.98    inference(flattening,[],[f15])).
% 2.78/0.98  
% 2.78/0.98  fof(f24,plain,(
% 2.78/0.98    ( ! [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (sK2 != sK3 & k1_funct_1(X1,sK2) = k1_funct_1(X1,sK3) & r2_hidden(sK3,X0) & r2_hidden(sK2,X0))) )),
% 2.78/0.98    introduced(choice_axiom,[])).
% 2.78/0.98  
% 2.78/0.98  fof(f23,plain,(
% 2.78/0.98    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) & v2_funct_1(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 2.78/0.98    introduced(choice_axiom,[])).
% 2.78/0.98  
% 2.78/0.98  fof(f25,plain,(
% 2.78/0.98    (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0)) & v2_funct_1(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 2.78/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f24,f23])).
% 2.78/0.98  
% 2.78/0.98  fof(f44,plain,(
% 2.78/0.98    v1_funct_2(sK1,sK0,sK0)),
% 2.78/0.98    inference(cnf_transformation,[],[f25])).
% 2.78/0.98  
% 2.78/0.98  fof(f7,axiom,(
% 2.78/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 2.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.98  
% 2.78/0.98  fof(f13,plain,(
% 2.78/0.98    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.78/0.98    inference(ennf_transformation,[],[f7])).
% 2.78/0.98  
% 2.78/0.98  fof(f14,plain,(
% 2.78/0.98    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.78/0.98    inference(flattening,[],[f13])).
% 2.78/0.98  
% 2.78/0.98  fof(f42,plain,(
% 2.78/0.98    ( ! [X2,X0,X3,X1] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.78/0.98    inference(cnf_transformation,[],[f14])).
% 2.78/0.98  
% 2.78/0.98  fof(f46,plain,(
% 2.78/0.98    v2_funct_1(sK1)),
% 2.78/0.98    inference(cnf_transformation,[],[f25])).
% 2.78/0.98  
% 2.78/0.98  fof(f43,plain,(
% 2.78/0.98    v1_funct_1(sK1)),
% 2.78/0.98    inference(cnf_transformation,[],[f25])).
% 2.78/0.98  
% 2.78/0.98  fof(f47,plain,(
% 2.78/0.98    r2_hidden(sK2,sK0)),
% 2.78/0.98    inference(cnf_transformation,[],[f25])).
% 2.78/0.98  
% 2.78/0.98  fof(f45,plain,(
% 2.78/0.98    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.78/0.98    inference(cnf_transformation,[],[f25])).
% 2.78/0.98  
% 2.78/0.98  fof(f48,plain,(
% 2.78/0.98    r2_hidden(sK3,sK0)),
% 2.78/0.98    inference(cnf_transformation,[],[f25])).
% 2.78/0.98  
% 2.78/0.98  fof(f49,plain,(
% 2.78/0.98    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 2.78/0.98    inference(cnf_transformation,[],[f25])).
% 2.78/0.98  
% 2.78/0.98  fof(f4,axiom,(
% 2.78/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.98  
% 2.78/0.98  fof(f21,plain,(
% 2.78/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.78/0.98    inference(nnf_transformation,[],[f4])).
% 2.78/0.98  
% 2.78/0.98  fof(f33,plain,(
% 2.78/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.78/0.98    inference(cnf_transformation,[],[f21])).
% 2.78/0.98  
% 2.78/0.98  fof(f1,axiom,(
% 2.78/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.98  
% 2.78/0.98  fof(f17,plain,(
% 2.78/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.78/0.98    inference(nnf_transformation,[],[f1])).
% 2.78/0.98  
% 2.78/0.98  fof(f18,plain,(
% 2.78/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.78/0.98    inference(flattening,[],[f17])).
% 2.78/0.98  
% 2.78/0.98  fof(f28,plain,(
% 2.78/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.78/0.98    inference(cnf_transformation,[],[f18])).
% 2.78/0.98  
% 2.78/0.98  fof(f3,axiom,(
% 2.78/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.98  
% 2.78/0.98  fof(f19,plain,(
% 2.78/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.78/0.98    inference(nnf_transformation,[],[f3])).
% 2.78/0.98  
% 2.78/0.98  fof(f20,plain,(
% 2.78/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.78/0.98    inference(flattening,[],[f19])).
% 2.78/0.98  
% 2.78/0.98  fof(f31,plain,(
% 2.78/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.78/0.98    inference(cnf_transformation,[],[f20])).
% 2.78/0.98  
% 2.78/0.98  fof(f54,plain,(
% 2.78/0.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.78/0.98    inference(equality_resolution,[],[f31])).
% 2.78/0.98  
% 2.78/0.98  fof(f2,axiom,(
% 2.78/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.98  
% 2.78/0.98  fof(f29,plain,(
% 2.78/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.78/0.98    inference(cnf_transformation,[],[f2])).
% 2.78/0.98  
% 2.78/0.98  fof(f34,plain,(
% 2.78/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.78/0.98    inference(cnf_transformation,[],[f21])).
% 2.78/0.98  
% 2.78/0.98  fof(f5,axiom,(
% 2.78/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.98  
% 2.78/0.98  fof(f10,plain,(
% 2.78/0.98    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.78/0.98    inference(ennf_transformation,[],[f5])).
% 2.78/0.98  
% 2.78/0.98  fof(f35,plain,(
% 2.78/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.78/0.98    inference(cnf_transformation,[],[f10])).
% 2.78/0.98  
% 2.78/0.98  fof(f6,axiom,(
% 2.78/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.98  
% 2.78/0.98  fof(f11,plain,(
% 2.78/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.78/0.98    inference(ennf_transformation,[],[f6])).
% 2.78/0.98  
% 2.78/0.98  fof(f12,plain,(
% 2.78/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.78/0.98    inference(flattening,[],[f11])).
% 2.78/0.98  
% 2.78/0.98  fof(f22,plain,(
% 2.78/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.78/0.98    inference(nnf_transformation,[],[f12])).
% 2.78/0.98  
% 2.78/0.98  fof(f38,plain,(
% 2.78/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.78/0.98    inference(cnf_transformation,[],[f22])).
% 2.78/0.98  
% 2.78/0.98  fof(f39,plain,(
% 2.78/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.78/0.98    inference(cnf_transformation,[],[f22])).
% 2.78/0.98  
% 2.78/0.98  fof(f58,plain,(
% 2.78/0.98    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.78/0.98    inference(equality_resolution,[],[f39])).
% 2.78/0.98  
% 2.78/0.98  fof(f37,plain,(
% 2.78/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.78/0.98    inference(cnf_transformation,[],[f22])).
% 2.78/0.98  
% 2.78/0.98  fof(f59,plain,(
% 2.78/0.98    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.78/0.98    inference(equality_resolution,[],[f37])).
% 2.78/0.98  
% 2.78/0.98  fof(f50,plain,(
% 2.78/0.98    sK2 != sK3),
% 2.78/0.98    inference(cnf_transformation,[],[f25])).
% 2.78/0.98  
% 2.78/0.98  fof(f36,plain,(
% 2.78/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.78/0.98    inference(cnf_transformation,[],[f22])).
% 2.78/0.98  
% 2.78/0.98  cnf(c_23,negated_conjecture,
% 2.78/0.98      ( v1_funct_2(sK1,sK0,sK0) ),
% 2.78/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_16,plain,
% 2.78/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.78/0.98      | ~ r2_hidden(X3,X1)
% 2.78/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/0.98      | ~ v1_funct_1(X0)
% 2.78/0.98      | ~ v2_funct_1(X0)
% 2.78/0.98      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
% 2.78/0.98      | k1_xboole_0 = X2 ),
% 2.78/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_21,negated_conjecture,
% 2.78/0.98      ( v2_funct_1(sK1) ),
% 2.78/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_270,plain,
% 2.78/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.78/0.98      | ~ r2_hidden(X3,X1)
% 2.78/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/0.98      | ~ v1_funct_1(X0)
% 2.78/0.98      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
% 2.78/0.98      | sK1 != X0
% 2.78/0.98      | k1_xboole_0 = X2 ),
% 2.78/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_271,plain,
% 2.78/0.98      ( ~ v1_funct_2(sK1,X0,X1)
% 2.78/0.98      | ~ r2_hidden(X2,X0)
% 2.78/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.78/0.98      | ~ v1_funct_1(sK1)
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X2)) = X2
% 2.78/0.98      | k1_xboole_0 = X1 ),
% 2.78/0.98      inference(unflattening,[status(thm)],[c_270]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_24,negated_conjecture,
% 2.78/0.98      ( v1_funct_1(sK1) ),
% 2.78/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_275,plain,
% 2.78/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.78/0.98      | ~ r2_hidden(X2,X0)
% 2.78/0.98      | ~ v1_funct_2(sK1,X0,X1)
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X2)) = X2
% 2.78/0.98      | k1_xboole_0 = X1 ),
% 2.78/0.98      inference(global_propositional_subsumption,[status(thm)],[c_271,c_24]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_276,plain,
% 2.78/0.98      ( ~ v1_funct_2(sK1,X0,X1)
% 2.78/0.98      | ~ r2_hidden(X2,X0)
% 2.78/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X2)) = X2
% 2.78/0.98      | k1_xboole_0 = X1 ),
% 2.78/0.98      inference(renaming,[status(thm)],[c_275]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_20,negated_conjecture,
% 2.78/0.98      ( r2_hidden(sK2,sK0) ),
% 2.78/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_321,plain,
% 2.78/0.98      ( ~ v1_funct_2(sK1,X0,X1)
% 2.78/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X2)) = X2
% 2.78/0.98      | sK0 != X0
% 2.78/0.98      | sK2 != X2
% 2.78/0.98      | k1_xboole_0 = X1 ),
% 2.78/0.98      inference(resolution_lifted,[status(thm)],[c_276,c_20]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_322,plain,
% 2.78/0.98      ( ~ v1_funct_2(sK1,sK0,X0)
% 2.78/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
% 2.78/0.98      | k1_xboole_0 = X0 ),
% 2.78/0.98      inference(unflattening,[status(thm)],[c_321]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_888,plain,
% 2.78/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
% 2.78/0.98      | sK0 != X0
% 2.78/0.98      | sK0 != sK0
% 2.78/0.98      | sK1 != sK1
% 2.78/0.98      | k1_xboole_0 = X0 ),
% 2.78/0.98      inference(resolution_lifted,[status(thm)],[c_23,c_322]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_889,plain,
% 2.78/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
% 2.78/0.98      | k1_xboole_0 = sK0 ),
% 2.78/0.98      inference(unflattening,[status(thm)],[c_888]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_22,negated_conjecture,
% 2.78/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.78/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_891,plain,
% 2.78/0.98      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
% 2.78/0.98      | k1_xboole_0 = sK0 ),
% 2.78/0.98      inference(global_propositional_subsumption,[status(thm)],[c_889,c_22]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_19,negated_conjecture,
% 2.78/0.98      ( r2_hidden(sK3,sK0) ),
% 2.78/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_303,plain,
% 2.78/0.98      ( ~ v1_funct_2(sK1,X0,X1)
% 2.78/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X2)) = X2
% 2.78/0.98      | sK0 != X0
% 2.78/0.98      | sK3 != X2
% 2.78/0.98      | k1_xboole_0 = X1 ),
% 2.78/0.98      inference(resolution_lifted,[status(thm)],[c_276,c_19]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_304,plain,
% 2.78/0.98      ( ~ v1_funct_2(sK1,sK0,X0)
% 2.78/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) = sK3
% 2.78/0.98      | k1_xboole_0 = X0 ),
% 2.78/0.98      inference(unflattening,[status(thm)],[c_303]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_899,plain,
% 2.78/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) = sK3
% 2.78/0.98      | sK0 != X0
% 2.78/0.98      | sK0 != sK0
% 2.78/0.98      | sK1 != sK1
% 2.78/0.98      | k1_xboole_0 = X0 ),
% 2.78/0.98      inference(resolution_lifted,[status(thm)],[c_23,c_304]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_900,plain,
% 2.78/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) = sK3
% 2.78/0.98      | k1_xboole_0 = sK0 ),
% 2.78/0.98      inference(unflattening,[status(thm)],[c_899]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_902,plain,
% 2.78/0.98      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) = sK3
% 2.78/0.98      | k1_xboole_0 = sK0 ),
% 2.78/0.98      inference(global_propositional_subsumption,[status(thm)],[c_900,c_22]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_18,negated_conjecture,
% 2.78/0.98      ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
% 2.78/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1474,plain,
% 2.78/0.98      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3
% 2.78/0.98      | sK0 = k1_xboole_0 ),
% 2.78/0.98      inference(light_normalisation,[status(thm)],[c_902,c_18]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1618,plain,
% 2.78/0.98      ( sK0 = k1_xboole_0 | sK3 = sK2 ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_891,c_1474]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1449,plain,
% 2.78/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_8,plain,
% 2.78/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.78/0.98      inference(cnf_transformation,[],[f33]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1451,plain,
% 2.78/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.78/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2366,plain,
% 2.78/0.98      ( r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_1449,c_1451]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_0,plain,
% 2.78/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.78/0.98      inference(cnf_transformation,[],[f28]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1455,plain,
% 2.78/0.98      ( X0 = X1
% 2.78/0.98      | r1_tarski(X0,X1) != iProver_top
% 2.78/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_4589,plain,
% 2.78/0.98      ( k2_zfmisc_1(sK0,sK0) = sK1
% 2.78/0.98      | r1_tarski(k2_zfmisc_1(sK0,sK0),sK1) != iProver_top ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_2366,c_1455]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_4833,plain,
% 2.78/0.98      ( k2_zfmisc_1(sK0,sK0) = sK1
% 2.78/0.98      | sK3 = sK2
% 2.78/0.98      | r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK1) != iProver_top ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_1618,c_4589]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_5,plain,
% 2.78/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.78/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_4838,plain,
% 2.78/0.98      ( k2_zfmisc_1(sK0,sK0) = sK1
% 2.78/0.98      | sK3 = sK2
% 2.78/0.98      | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 2.78/0.98      inference(demodulation,[status(thm)],[c_4833,c_5]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_3,plain,
% 2.78/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 2.78/0.98      inference(cnf_transformation,[],[f29]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2122,plain,
% 2.78/0.98      ( r1_tarski(k1_xboole_0,sK1) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2125,plain,
% 2.78/0.98      ( r1_tarski(k1_xboole_0,sK1) = iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_2122]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_5026,plain,
% 2.78/0.98      ( sK3 = sK2 | k2_zfmisc_1(sK0,sK0) = sK1 ),
% 2.78/0.98      inference(global_propositional_subsumption,[status(thm)],[c_4838,c_2125]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_5027,plain,
% 2.78/0.98      ( k2_zfmisc_1(sK0,sK0) = sK1 | sK3 = sK2 ),
% 2.78/0.98      inference(renaming,[status(thm)],[c_5026]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_5031,plain,
% 2.78/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = sK1 | sK3 = sK2 ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_1618,c_5027]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_5083,plain,
% 2.78/0.98      ( sK1 = k1_xboole_0 | sK3 = sK2 ),
% 2.78/0.98      inference(demodulation,[status(thm)],[c_5031,c_5]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_5361,plain,
% 2.78/0.98      ( k1_funct_1(k1_xboole_0,sK3) = k1_funct_1(sK1,sK2) | sK3 = sK2 ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_5083,c_18]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1703,plain,
% 2.78/0.98      ( sK3 = sK2
% 2.78/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_1618,c_1449]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1972,plain,
% 2.78/0.98      ( sK3 = sK2 | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.78/0.98      inference(demodulation,[status(thm)],[c_1703,c_5]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2367,plain,
% 2.78/0.98      ( sK3 = sK2 | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_1972,c_1451]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_7,plain,
% 2.78/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.78/0.98      inference(cnf_transformation,[],[f34]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1452,plain,
% 2.78/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.78/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_9,plain,
% 2.78/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.78/0.98      inference(cnf_transformation,[],[f35]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1450,plain,
% 2.78/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.78/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2515,plain,
% 2.78/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.78/0.98      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_1452,c_1450]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2945,plain,
% 2.78/0.98      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 2.78/0.98      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_5,c_2515]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_3098,plain,
% 2.78/0.98      ( k1_relset_1(k1_xboole_0,X0,sK1) = k1_relat_1(sK1) | sK3 = sK2 ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_2367,c_2945]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_13,plain,
% 2.78/0.98      ( v1_funct_2(X0,X1,X2)
% 2.78/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/0.98      | k1_relset_1(X1,X2,X0) != X1
% 2.78/0.98      | k1_xboole_0 = X2 ),
% 2.78/0.98      inference(cnf_transformation,[],[f38]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_870,plain,
% 2.78/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X3)))
% 2.78/0.98      | X3 != X2
% 2.78/0.98      | k1_relset_1(X1,X2,X0) != X1
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) = sK3
% 2.78/0.98      | sK0 != X1
% 2.78/0.98      | sK1 != X0
% 2.78/0.98      | k1_xboole_0 = X2
% 2.78/0.98      | k1_xboole_0 = X3 ),
% 2.78/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_304]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_871,plain,
% 2.78/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 2.78/0.98      | k1_relset_1(sK0,X0,sK1) != sK0
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) = sK3
% 2.78/0.98      | k1_xboole_0 = X0 ),
% 2.78/0.98      inference(unflattening,[status(thm)],[c_870]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1441,plain,
% 2.78/0.98      ( k1_relset_1(sK0,X0,sK1) != sK0
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) = sK3
% 2.78/0.98      | k1_xboole_0 = X0
% 2.78/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_871]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1528,plain,
% 2.78/0.98      ( k1_relset_1(sK0,X0,sK1) != sK0
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3
% 2.78/0.98      | k1_xboole_0 = X0
% 2.78/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top ),
% 2.78/0.98      inference(light_normalisation,[status(thm)],[c_1441,c_18]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1700,plain,
% 2.78/0.98      ( k1_relset_1(k1_xboole_0,X0,sK1) != sK0
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3
% 2.78/0.98      | sK3 = sK2
% 2.78/0.98      | k1_xboole_0 = X0
% 2.78/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_1618,c_1528]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_3325,plain,
% 2.78/0.98      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3
% 2.78/0.98      | k1_relat_1(sK1) != sK0
% 2.78/0.98      | sK3 = sK2
% 2.78/0.98      | k1_xboole_0 = X0
% 2.78/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_3098,c_1700]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_12,plain,
% 2.78/0.98      ( v1_funct_2(X0,k1_xboole_0,X1)
% 2.78/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.78/0.98      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 2.78/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_817,plain,
% 2.78/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.78/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
% 2.78/0.98      | X2 != X1
% 2.78/0.98      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) = sK3
% 2.78/0.98      | sK0 != k1_xboole_0
% 2.78/0.98      | sK1 != X0
% 2.78/0.98      | k1_xboole_0 = X2 ),
% 2.78/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_304]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_818,plain,
% 2.78/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 2.78/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 2.78/0.98      | k1_relset_1(k1_xboole_0,X0,sK1) != k1_xboole_0
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) = sK3
% 2.78/0.98      | sK0 != k1_xboole_0
% 2.78/0.98      | k1_xboole_0 = X0 ),
% 2.78/0.98      inference(unflattening,[status(thm)],[c_817]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1078,plain,
% 2.78/0.98      ( sP0_iProver_split
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) = sK3
% 2.78/0.98      | sK0 != k1_xboole_0 ),
% 2.78/0.98      inference(splitting,
% 2.78/0.98                [splitting(split),new_symbols(definition,[])],
% 2.78/0.98                [c_818]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1443,plain,
% 2.78/0.98      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) = sK3
% 2.78/0.98      | sK0 != k1_xboole_0
% 2.78/0.98      | sP0_iProver_split = iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_1078]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1497,plain,
% 2.78/0.98      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3
% 2.78/0.98      | sK0 != k1_xboole_0
% 2.78/0.98      | sP0_iProver_split = iProver_top ),
% 2.78/0.98      inference(light_normalisation,[status(thm)],[c_1443,c_18]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1501,plain,
% 2.78/0.98      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3
% 2.78/0.98      | sP0_iProver_split = iProver_top ),
% 2.78/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_1497,c_1474]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_14,plain,
% 2.78/0.98      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.78/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.78/0.98      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.78/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_780,plain,
% 2.78/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.78/0.98      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 2.78/0.98      | sK0 != X1
% 2.78/0.98      | sK0 != k1_xboole_0
% 2.78/0.98      | sK1 != X0 ),
% 2.78/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_781,plain,
% 2.78/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 2.78/0.98      | k1_relset_1(k1_xboole_0,sK0,sK1) = k1_xboole_0
% 2.78/0.98      | sK0 != k1_xboole_0 ),
% 2.78/0.98      inference(unflattening,[status(thm)],[c_780]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1447,plain,
% 2.78/0.98      ( k1_relset_1(k1_xboole_0,sK0,sK1) = k1_xboole_0
% 2.78/0.98      | sK0 != k1_xboole_0
% 2.78/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_781]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1520,plain,
% 2.78/0.98      ( k1_relset_1(k1_xboole_0,sK0,sK1) = k1_xboole_0
% 2.78/0.98      | sK0 != k1_xboole_0
% 2.78/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.78/0.98      inference(demodulation,[status(thm)],[c_1447,c_5]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2101,plain,
% 2.78/0.98      ( k1_relset_1(k1_xboole_0,sK0,sK1) = k1_xboole_0
% 2.78/0.98      | sK3 = sK2
% 2.78/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_1618,c_1520]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2233,plain,
% 2.78/0.98      ( sK3 = sK2 | k1_relset_1(k1_xboole_0,sK0,sK1) = k1_xboole_0 ),
% 2.78/0.98      inference(global_propositional_subsumption,[status(thm)],[c_2101,c_1972]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2234,plain,
% 2.78/0.98      ( k1_relset_1(k1_xboole_0,sK0,sK1) = k1_xboole_0 | sK3 = sK2 ),
% 2.78/0.98      inference(renaming,[status(thm)],[c_2233]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2237,plain,
% 2.78/0.98      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) = k1_xboole_0 | sK3 = sK2 ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_1618,c_2234]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2516,plain,
% 2.78/0.98      ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_1449,c_1450]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2609,plain,
% 2.78/0.98      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) = k1_relat_1(sK1)
% 2.78/0.98      | sK3 = sK2 ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_1618,c_2516]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2765,plain,
% 2.78/0.98      ( k1_relat_1(sK1) = k1_xboole_0 | sK3 = sK2 ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_2237,c_2609]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1077,plain,
% 2.78/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 2.78/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 2.78/0.98      | k1_relset_1(k1_xboole_0,X0,sK1) != k1_xboole_0
% 2.78/0.98      | k1_xboole_0 = X0
% 2.78/0.98      | ~ sP0_iProver_split ),
% 2.78/0.98      inference(splitting,
% 2.78/0.98                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.78/0.98                [c_818]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1444,plain,
% 2.78/0.98      ( k1_relset_1(k1_xboole_0,X0,sK1) != k1_xboole_0
% 2.78/0.98      | k1_xboole_0 = X0
% 2.78/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 2.78/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 2.78/0.98      | sP0_iProver_split != iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_1077]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1545,plain,
% 2.78/0.98      ( k1_relset_1(k1_xboole_0,X0,sK1) != k1_xboole_0
% 2.78/0.98      | k1_xboole_0 = X0
% 2.78/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 2.78/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.78/0.98      | sP0_iProver_split != iProver_top ),
% 2.78/0.98      inference(light_normalisation,[status(thm)],[c_1444,c_5]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_3323,plain,
% 2.78/0.98      ( k1_relat_1(sK1) != k1_xboole_0
% 2.78/0.98      | sK3 = sK2
% 2.78/0.98      | k1_xboole_0 = X0
% 2.78/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 2.78/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.78/0.98      | sP0_iProver_split != iProver_top ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_3098,c_1545]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_3548,plain,
% 2.78/0.98      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3
% 2.78/0.98      | sK3 = sK2
% 2.78/0.98      | k1_xboole_0 = X0
% 2.78/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top ),
% 2.78/0.98      inference(global_propositional_subsumption,
% 2.78/0.98                [status(thm)],
% 2.78/0.98                [c_3325,c_1501,c_1972,c_2765,c_3323]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_3559,plain,
% 2.78/0.98      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3
% 2.78/0.98      | sK3 = sK2
% 2.78/0.98      | k1_xboole_0 = X0
% 2.78/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_1618,c_3548]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_3564,plain,
% 2.78/0.98      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3
% 2.78/0.98      | sK3 = sK2
% 2.78/0.98      | k1_xboole_0 = X0
% 2.78/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.78/0.98      inference(light_normalisation,[status(thm)],[c_3559,c_5]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_3580,plain,
% 2.78/0.98      ( k1_xboole_0 = X0
% 2.78/0.98      | sK3 = sK2
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3 ),
% 2.78/0.98      inference(global_propositional_subsumption,[status(thm)],[c_3564,c_1972]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_3581,plain,
% 2.78/0.98      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3
% 2.78/0.98      | sK3 = sK2
% 2.78/0.98      | k1_xboole_0 = X0 ),
% 2.78/0.98      inference(renaming,[status(thm)],[c_3580]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_3666,plain,
% 2.78/0.98      ( k1_relset_1(sK0,sK0,k1_xboole_0) = k1_relat_1(sK1)
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3
% 2.78/0.98      | sK3 = sK2 ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_3581,c_2516]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_5517,plain,
% 2.78/0.98      ( k1_relset_1(sK0,sK0,k1_xboole_0) = k1_relat_1(sK1)
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(k1_xboole_0,sK3)) = sK3
% 2.78/0.98      | sK3 = sK2 ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_5361,c_3666]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_17,negated_conjecture,
% 2.78/0.98      ( sK2 != sK3 ),
% 2.78/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1082,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1598,plain,
% 2.78/0.98      ( sK3 != X0 | sK2 != X0 | sK2 = sK3 ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_1082]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_3525,plain,
% 2.78/0.98      ( sK3 != sK2 | sK2 = sK3 | sK2 != sK2 ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_1598]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_5345,plain,
% 2.78/0.98      ( k1_relset_1(sK0,sK0,k1_xboole_0) = k1_relat_1(sK1) | sK3 = sK2 ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_5083,c_2516]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1081,plain,( X0 = X0 ),theory(equality) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_6002,plain,
% 2.78/0.98      ( sK2 = sK2 ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_1081]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_6079,plain,
% 2.78/0.98      ( k1_relset_1(sK0,sK0,k1_xboole_0) = k1_relat_1(sK1) ),
% 2.78/0.98      inference(global_propositional_subsumption,
% 2.78/0.98                [status(thm)],
% 2.78/0.98                [c_5517,c_17,c_3525,c_5345,c_6002]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_3681,plain,
% 2.78/0.98      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3
% 2.78/0.98      | sK3 = sK2
% 2.78/0.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_3581,c_1449]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_4818,plain,
% 2.78/0.98      ( k1_relset_1(sK0,sK0,k1_xboole_0) = k1_relat_1(k1_xboole_0)
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3
% 2.78/0.98      | sK3 = sK2 ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_3681,c_1450]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_5516,plain,
% 2.78/0.98      ( k1_relset_1(sK0,sK0,k1_xboole_0) = k1_relat_1(k1_xboole_0)
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(k1_xboole_0,sK3)) = sK3
% 2.78/0.98      | sK3 = sK2 ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_5361,c_4818]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_5035,plain,
% 2.78/0.98      ( k1_relset_1(sK0,sK0,X0) = k1_relat_1(X0)
% 2.78/0.98      | sK3 = sK2
% 2.78/0.98      | r1_tarski(X0,sK1) != iProver_top ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_5027,c_2515]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_5087,plain,
% 2.78/0.98      ( k1_relset_1(sK0,sK0,k1_xboole_0) = k1_relat_1(k1_xboole_0)
% 2.78/0.98      | sK3 = sK2
% 2.78/0.98      | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_5035]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_6008,plain,
% 2.78/0.98      ( k1_relset_1(sK0,sK0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 2.78/0.98      inference(global_propositional_subsumption,
% 2.78/0.98                [status(thm)],
% 2.78/0.98                [c_5516,c_17,c_2125,c_3525,c_5087,c_6002]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_6081,plain,
% 2.78/0.98      ( k1_relat_1(sK1) = k1_relat_1(k1_xboole_0) ),
% 2.78/0.98      inference(light_normalisation,[status(thm)],[c_6079,c_6008]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_15,plain,
% 2.78/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.78/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.78/0.98      | k1_xboole_0 = X2 ),
% 2.78/0.98      inference(cnf_transformation,[],[f36]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_841,plain,
% 2.78/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.78/0.98      | sK0 != X1
% 2.78/0.98      | sK0 != X2
% 2.78/0.98      | sK1 != X0
% 2.78/0.98      | k1_xboole_0 = X2 ),
% 2.78/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_23]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_842,plain,
% 2.78/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.78/0.98      | k1_relset_1(sK0,sK0,sK1) = sK0
% 2.78/0.98      | k1_xboole_0 = sK0 ),
% 2.78/0.98      inference(unflattening,[status(thm)],[c_841]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_844,plain,
% 2.78/0.98      ( k1_relset_1(sK0,sK0,sK1) = sK0 | k1_xboole_0 = sK0 ),
% 2.78/0.98      inference(global_propositional_subsumption,[status(thm)],[c_842,c_22]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2611,plain,
% 2.78/0.98      ( k1_relat_1(sK1) = sK0 | sK0 = k1_xboole_0 ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_2516,c_844]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_6110,plain,
% 2.78/0.98      ( k1_relat_1(k1_xboole_0) = sK0 | sK0 = k1_xboole_0 ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_6081,c_2611]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_7402,plain,
% 2.78/0.98      ( sK0 = k1_xboole_0 ),
% 2.78/0.98      inference(global_propositional_subsumption,
% 2.78/0.98                [status(thm)],
% 2.78/0.98                [c_6110,c_17,c_1618,c_3525,c_6002]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_852,plain,
% 2.78/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X3)))
% 2.78/0.98      | X3 != X2
% 2.78/0.98      | k1_relset_1(X1,X2,X0) != X1
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
% 2.78/0.98      | sK0 != X1
% 2.78/0.98      | sK1 != X0
% 2.78/0.98      | k1_xboole_0 = X2
% 2.78/0.98      | k1_xboole_0 = X3 ),
% 2.78/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_322]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_853,plain,
% 2.78/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 2.78/0.98      | k1_relset_1(sK0,X0,sK1) != sK0
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
% 2.78/0.98      | k1_xboole_0 = X0 ),
% 2.78/0.98      inference(unflattening,[status(thm)],[c_852]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1442,plain,
% 2.78/0.98      ( k1_relset_1(sK0,X0,sK1) != sK0
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
% 2.78/0.98      | k1_xboole_0 = X0
% 2.78/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_853]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1795,plain,
% 2.78/0.98      ( k1_relset_1(k1_xboole_0,X0,sK1) != sK0
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
% 2.78/0.98      | sK3 = sK2
% 2.78/0.98      | k1_xboole_0 = X0
% 2.78/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_1618,c_1442]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_7413,plain,
% 2.78/0.98      ( k1_relset_1(k1_xboole_0,X0,sK1) != k1_xboole_0
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
% 2.78/0.98      | sK3 = sK2
% 2.78/0.98      | k1_xboole_0 = X0
% 2.78/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 2.78/0.98      inference(demodulation,[status(thm)],[c_7402,c_1795]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_7439,plain,
% 2.78/0.98      ( k1_relset_1(k1_xboole_0,X0,sK1) != k1_xboole_0
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
% 2.78/0.98      | sK3 = sK2
% 2.78/0.98      | k1_xboole_0 = X0
% 2.78/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.78/0.98      inference(light_normalisation,[status(thm)],[c_7413,c_5]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_5187,plain,
% 2.78/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 2.78/0.98      | k1_xboole_0 = X0
% 2.78/0.98      | sK3 = sK2
% 2.78/0.98      | sP0_iProver_split != iProver_top ),
% 2.78/0.98      inference(global_propositional_subsumption,
% 2.78/0.98                [status(thm)],
% 2.78/0.98                [c_3323,c_1972,c_2765]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_5188,plain,
% 2.78/0.98      ( sK3 = sK2
% 2.78/0.98      | k1_xboole_0 = X0
% 2.78/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 2.78/0.98      | sP0_iProver_split != iProver_top ),
% 2.78/0.98      inference(renaming,[status(thm)],[c_5187]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_5200,plain,
% 2.78/0.98      ( sK3 = sK2
% 2.78/0.98      | k1_xboole_0 = X0
% 2.78/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 2.78/0.98      | sP0_iProver_split != iProver_top ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_1618,c_5188]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_5205,plain,
% 2.78/0.98      ( sK3 = sK2
% 2.78/0.98      | k1_xboole_0 = X0
% 2.78/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.78/0.98      | sP0_iProver_split != iProver_top ),
% 2.78/0.98      inference(light_normalisation,[status(thm)],[c_5200,c_5]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_7410,plain,
% 2.78/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = sK1
% 2.78/0.98      | r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK1) != iProver_top ),
% 2.78/0.98      inference(demodulation,[status(thm)],[c_7402,c_4589]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_7454,plain,
% 2.78/0.98      ( sK1 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 2.78/0.98      inference(demodulation,[status(thm)],[c_7410,c_5]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_4590,plain,
% 2.78/0.98      ( sK1 = k1_xboole_0
% 2.78/0.98      | sK3 = sK2
% 2.78/0.98      | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_2367,c_1455]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_7552,plain,
% 2.78/0.98      ( sK1 = k1_xboole_0 ),
% 2.78/0.98      inference(global_propositional_subsumption,
% 2.78/0.98                [status(thm)],
% 2.78/0.98                [c_7454,c_17,c_2125,c_3525,c_4590,c_6002]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_3594,plain,
% 2.78/0.98      ( X0 = X1
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3
% 2.78/0.98      | sK3 = sK2 ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_3581,c_3581]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_6115,plain,
% 2.78/0.98      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3 | X0 = X1 ),
% 2.78/0.98      inference(global_propositional_subsumption,
% 2.78/0.98                [status(thm)],
% 2.78/0.98                [c_3594,c_17,c_3525,c_6002]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_6116,plain,
% 2.78/0.98      ( X0 = X1 | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK3 ),
% 2.78/0.98      inference(renaming,[status(thm)],[c_6115]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_6130,plain,
% 2.78/0.98      ( X0 = X1
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(k1_xboole_0,sK3)) = sK3
% 2.78/0.98      | sK3 = sK2 ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_5361,c_6116]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_6989,plain,
% 2.78/0.98      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(k1_xboole_0,sK3)) = sK3
% 2.78/0.98      | X0 = X1 ),
% 2.78/0.98      inference(global_propositional_subsumption,
% 2.78/0.98                [status(thm)],
% 2.78/0.98                [c_6130,c_17,c_3525,c_6002]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_6990,plain,
% 2.78/0.98      ( X0 = X1
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(k1_xboole_0,sK3)) = sK3 ),
% 2.78/0.98      inference(renaming,[status(thm)],[c_6989]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_7310,plain,
% 2.78/0.98      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(k1_xboole_0,sK3)) = sK3
% 2.78/0.98      | sK3 != X0 ),
% 2.78/0.98      inference(equality_factoring,[status(thm)],[c_6990]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_7325,plain,
% 2.78/0.98      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(k1_xboole_0,sK3)) = sK3 ),
% 2.78/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_7310,c_6990]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_7557,plain,
% 2.78/0.98      ( k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK3)) = sK3 ),
% 2.78/0.98      inference(demodulation,[status(thm)],[c_7552,c_7325]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_7569,plain,
% 2.78/0.98      ( k1_funct_1(k1_xboole_0,sK3) = k1_funct_1(k1_xboole_0,sK2) ),
% 2.78/0.98      inference(demodulation,[status(thm)],[c_7552,c_18]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_7588,plain,
% 2.78/0.98      ( k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK2)) = sK3 ),
% 2.78/0.98      inference(light_normalisation,[status(thm)],[c_7557,c_7569]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_793,plain,
% 2.78/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.78/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
% 2.78/0.98      | X2 != X1
% 2.78/0.98      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
% 2.78/0.98      | sK0 != k1_xboole_0
% 2.78/0.98      | sK1 != X0
% 2.78/0.98      | k1_xboole_0 = X2 ),
% 2.78/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_322]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_794,plain,
% 2.78/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 2.78/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 2.78/0.98      | k1_relset_1(k1_xboole_0,X0,sK1) != k1_xboole_0
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
% 2.78/0.98      | sK0 != k1_xboole_0
% 2.78/0.98      | k1_xboole_0 = X0 ),
% 2.78/0.98      inference(unflattening,[status(thm)],[c_793]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1079,plain,
% 2.78/0.98      ( sP0_iProver_split
% 2.78/0.98      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
% 2.78/0.98      | sK0 != k1_xboole_0 ),
% 2.78/0.98      inference(splitting,
% 2.78/0.98                [splitting(split),new_symbols(definition,[])],
% 2.78/0.98                [c_794]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1445,plain,
% 2.78/0.98      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
% 2.78/0.98      | sK0 != k1_xboole_0
% 2.78/0.98      | sP0_iProver_split = iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_1079]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_27,plain,
% 2.78/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1103,plain,
% 2.78/0.98      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
% 2.78/0.98      | sK0 != k1_xboole_0
% 2.78/0.98      | sP0_iProver_split = iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_1079]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1794,plain,
% 2.78/0.98      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
% 2.78/0.98      | sK0 = k1_xboole_0
% 2.78/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_844,c_1442]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2226,plain,
% 2.78/0.98      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) = sK2
% 2.78/0.98      | sP0_iProver_split = iProver_top ),
% 2.78/0.98      inference(global_propositional_subsumption,
% 2.78/0.98                [status(thm)],
% 2.78/0.98                [c_1445,c_27,c_1103,c_1794]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_7565,plain,
% 2.78/0.98      ( k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK2)) = sK2
% 2.78/0.98      | sP0_iProver_split = iProver_top ),
% 2.78/0.98      inference(demodulation,[status(thm)],[c_7552,c_2226]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_7590,plain,
% 2.78/0.98      ( sK3 = sK2 | sP0_iProver_split = iProver_top ),
% 2.78/0.98      inference(demodulation,[status(thm)],[c_7588,c_7565]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_7628,plain,
% 2.78/0.98      ( k1_xboole_0 = X0 ),
% 2.78/0.98      inference(global_propositional_subsumption,
% 2.78/0.98                [status(thm)],
% 2.78/0.98                [c_7439,c_17,c_1972,c_3525,c_5205,c_6002,c_7590]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_7689,plain,
% 2.78/0.98      ( X0 = X1 ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_7628,c_7628]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_7638,plain,
% 2.78/0.98      ( sK3 != k1_xboole_0 ),
% 2.78/0.98      inference(demodulation,[status(thm)],[c_7628,c_17]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_8558,plain,
% 2.78/0.98      ( k1_xboole_0 != X0 ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_7689,c_7638]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_8582,plain,
% 2.78/0.98      ( $false ),
% 2.78/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_8558,c_7689]) ).
% 2.78/0.98  
% 2.78/0.98  
% 2.78/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.78/0.98  
% 2.78/0.98  ------                               Statistics
% 2.78/0.98  
% 2.78/0.98  ------ General
% 2.78/0.98  
% 2.78/0.98  abstr_ref_over_cycles:                  0
% 2.78/0.98  abstr_ref_under_cycles:                 0
% 2.78/0.98  gc_basic_clause_elim:                   0
% 2.78/0.98  forced_gc_time:                         0
% 2.78/0.98  parsing_time:                           0.014
% 2.78/0.98  unif_index_cands_time:                  0.
% 2.78/0.98  unif_index_add_time:                    0.
% 2.78/0.98  orderings_time:                         0.
% 2.78/0.98  out_proof_time:                         0.013
% 2.78/0.98  total_time:                             0.307
% 2.78/0.98  num_of_symbols:                         49
% 2.78/0.98  num_of_terms:                           4023
% 2.78/0.98  
% 2.78/0.98  ------ Preprocessing
% 2.78/0.98  
% 2.78/0.98  num_of_splits:                          2
% 2.78/0.98  num_of_split_atoms:                     1
% 2.78/0.98  num_of_reused_defs:                     1
% 2.78/0.98  num_eq_ax_congr_red:                    9
% 2.78/0.98  num_of_sem_filtered_clauses:            1
% 2.78/0.98  num_of_subtypes:                        0
% 2.78/0.98  monotx_restored_types:                  0
% 2.78/0.98  sat_num_of_epr_types:                   0
% 2.78/0.98  sat_num_of_non_cyclic_types:            0
% 2.78/0.98  sat_guarded_non_collapsed_types:        0
% 2.78/0.98  num_pure_diseq_elim:                    0
% 2.78/0.98  simp_replaced_by:                       0
% 2.78/0.98  res_preprocessed:                       108
% 2.78/0.98  prep_upred:                             0
% 2.78/0.98  prep_unflattend:                        64
% 2.78/0.98  smt_new_axioms:                         0
% 2.78/0.98  pred_elim_cands:                        2
% 2.78/0.98  pred_elim:                              4
% 2.78/0.98  pred_elim_cl:                           3
% 2.78/0.98  pred_elim_cycles:                       7
% 2.78/0.98  merged_defs:                            8
% 2.78/0.98  merged_defs_ncl:                        0
% 2.78/0.98  bin_hyper_res:                          8
% 2.78/0.98  prep_cycles:                            4
% 2.78/0.98  pred_elim_time:                         0.014
% 2.78/0.98  splitting_time:                         0.
% 2.78/0.98  sem_filter_time:                        0.
% 2.78/0.98  monotx_time:                            0.
% 2.78/0.98  subtype_inf_time:                       0.
% 2.78/0.98  
% 2.78/0.98  ------ Problem properties
% 2.78/0.98  
% 2.78/0.98  clauses:                                23
% 2.78/0.98  conjectures:                            3
% 2.78/0.98  epr:                                    4
% 2.78/0.98  horn:                                   14
% 2.78/0.98  ground:                                 10
% 2.78/0.98  unary:                                  7
% 2.78/0.98  binary:                                 6
% 2.78/0.98  lits:                                   56
% 2.78/0.98  lits_eq:                                34
% 2.78/0.98  fd_pure:                                0
% 2.78/0.98  fd_pseudo:                              0
% 2.78/0.98  fd_cond:                                5
% 2.78/0.98  fd_pseudo_cond:                         1
% 2.78/0.98  ac_symbols:                             0
% 2.78/0.98  
% 2.78/0.98  ------ Propositional Solver
% 2.78/0.98  
% 2.78/0.98  prop_solver_calls:                      30
% 2.78/0.98  prop_fast_solver_calls:                 1103
% 2.78/0.98  smt_solver_calls:                       0
% 2.78/0.98  smt_fast_solver_calls:                  0
% 2.78/0.98  prop_num_of_clauses:                    1875
% 2.78/0.98  prop_preprocess_simplified:             4909
% 2.78/0.98  prop_fo_subsumed:                       105
% 2.78/0.98  prop_solver_time:                       0.
% 2.78/0.98  smt_solver_time:                        0.
% 2.78/0.98  smt_fast_solver_time:                   0.
% 2.78/0.99  prop_fast_solver_time:                  0.
% 2.78/0.99  prop_unsat_core_time:                   0.
% 2.78/0.99  
% 2.78/0.99  ------ QBF
% 2.78/0.99  
% 2.78/0.99  qbf_q_res:                              0
% 2.78/0.99  qbf_num_tautologies:                    0
% 2.78/0.99  qbf_prep_cycles:                        0
% 2.78/0.99  
% 2.78/0.99  ------ BMC1
% 2.78/0.99  
% 2.78/0.99  bmc1_current_bound:                     -1
% 2.78/0.99  bmc1_last_solved_bound:                 -1
% 2.78/0.99  bmc1_unsat_core_size:                   -1
% 2.78/0.99  bmc1_unsat_core_parents_size:           -1
% 2.78/0.99  bmc1_merge_next_fun:                    0
% 2.78/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.78/0.99  
% 2.78/0.99  ------ Instantiation
% 2.78/0.99  
% 2.78/0.99  inst_num_of_clauses:                    538
% 2.78/0.99  inst_num_in_passive:                    72
% 2.78/0.99  inst_num_in_active:                     371
% 2.78/0.99  inst_num_in_unprocessed:                95
% 2.78/0.99  inst_num_of_loops:                      490
% 2.78/0.99  inst_num_of_learning_restarts:          0
% 2.78/0.99  inst_num_moves_active_passive:          113
% 2.78/0.99  inst_lit_activity:                      0
% 2.78/0.99  inst_lit_activity_moves:                0
% 2.78/0.99  inst_num_tautologies:                   0
% 2.78/0.99  inst_num_prop_implied:                  0
% 2.78/0.99  inst_num_existing_simplified:           0
% 2.78/0.99  inst_num_eq_res_simplified:             0
% 2.78/0.99  inst_num_child_elim:                    0
% 2.78/0.99  inst_num_of_dismatching_blockings:      446
% 2.78/0.99  inst_num_of_non_proper_insts:           1141
% 2.78/0.99  inst_num_of_duplicates:                 0
% 2.78/0.99  inst_inst_num_from_inst_to_res:         0
% 2.78/0.99  inst_dismatching_checking_time:         0.
% 2.78/0.99  
% 2.78/0.99  ------ Resolution
% 2.78/0.99  
% 2.78/0.99  res_num_of_clauses:                     0
% 2.78/0.99  res_num_in_passive:                     0
% 2.78/0.99  res_num_in_active:                      0
% 2.78/0.99  res_num_of_loops:                       112
% 2.78/0.99  res_forward_subset_subsumed:            49
% 2.78/0.99  res_backward_subset_subsumed:           4
% 2.78/0.99  res_forward_subsumed:                   1
% 2.78/0.99  res_backward_subsumed:                  0
% 2.78/0.99  res_forward_subsumption_resolution:     1
% 2.78/0.99  res_backward_subsumption_resolution:    0
% 2.78/0.99  res_clause_to_clause_subsumption:       682
% 2.78/0.99  res_orphan_elimination:                 0
% 2.78/0.99  res_tautology_del:                      245
% 2.78/0.99  res_num_eq_res_simplified:              0
% 2.78/0.99  res_num_sel_changes:                    0
% 2.78/0.99  res_moves_from_active_to_pass:          0
% 2.78/0.99  
% 2.78/0.99  ------ Superposition
% 2.78/0.99  
% 2.78/0.99  sup_time_total:                         0.
% 2.78/0.99  sup_time_generating:                    0.
% 2.78/0.99  sup_time_sim_full:                      0.
% 2.78/0.99  sup_time_sim_immed:                     0.
% 2.78/0.99  
% 2.78/0.99  sup_num_of_clauses:                     32
% 2.78/0.99  sup_num_in_active:                      18
% 2.78/0.99  sup_num_in_passive:                     14
% 2.78/0.99  sup_num_of_loops:                       96
% 2.78/0.99  sup_fw_superposition:                   177
% 2.78/0.99  sup_bw_superposition:                   1265
% 2.78/0.99  sup_immediate_simplified:               517
% 2.78/0.99  sup_given_eliminated:                   4
% 2.78/0.99  comparisons_done:                       0
% 2.78/0.99  comparisons_avoided:                    81
% 2.78/0.99  
% 2.78/0.99  ------ Simplifications
% 2.78/0.99  
% 2.78/0.99  
% 2.78/0.99  sim_fw_subset_subsumed:                 374
% 2.78/0.99  sim_bw_subset_subsumed:                 61
% 2.78/0.99  sim_fw_subsumed:                        155
% 2.78/0.99  sim_bw_subsumed:                        30
% 2.78/0.99  sim_fw_subsumption_res:                 11
% 2.78/0.99  sim_bw_subsumption_res:                 11
% 2.78/0.99  sim_tautology_del:                      8
% 2.78/0.99  sim_eq_tautology_del:                   28
% 2.78/0.99  sim_eq_res_simp:                        4
% 2.78/0.99  sim_fw_demodulated:                     23
% 2.78/0.99  sim_bw_demodulated:                     56
% 2.78/0.99  sim_light_normalised:                   31
% 2.78/0.99  sim_joinable_taut:                      0
% 2.78/0.99  sim_joinable_simp:                      0
% 2.78/0.99  sim_ac_normalised:                      0
% 2.78/0.99  sim_smt_subsumption:                    0
% 2.78/0.99  
%------------------------------------------------------------------------------
