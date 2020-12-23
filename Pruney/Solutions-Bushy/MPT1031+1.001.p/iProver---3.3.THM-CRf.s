%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1031+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:42 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :  161 (2854 expanded)
%              Number of clauses        :   89 ( 821 expanded)
%              Number of leaves         :   19 ( 686 expanded)
%              Depth                    :   26
%              Number of atoms          :  641 (19326 expanded)
%              Number of equality atoms :  211 (5141 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ~ ( ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X3,X0,X1)
                & v1_funct_1(X3) )
             => ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          & ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ~ ( ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X3,X0,X1)
                  & v1_funct_1(X3) )
               => ? [X4] :
                    ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                    & r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
            & ( k1_xboole_0 = X1
             => k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f46,plain,(
    ! [X2,X0,X1,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
     => ( k1_funct_1(X2,sK6(X3)) != k1_funct_1(X3,sK6(X3))
        & r2_hidden(sK6(X3),k1_relset_1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0,X1,X2] :
        ( ! [X3] :
            ( ? [X4] :
                ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            | ~ v1_funct_2(X3,X0,X1)
            | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK5,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,k1_relset_1(sK3,sK4,sK5)) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
          | ~ v1_funct_2(X3,sK3,sK4)
          | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = sK3
        | k1_xboole_0 != sK4 )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ! [X3] :
        ( ( k1_funct_1(sK5,sK6(X3)) != k1_funct_1(X3,sK6(X3))
          & r2_hidden(sK6(X3),k1_relset_1(sK3,sK4,sK5)) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
        | ~ v1_funct_2(X3,sK3,sK4)
        | ~ v1_funct_1(X3) )
    & ( k1_xboole_0 = sK3
      | k1_xboole_0 != sK4 )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f35,f46,f45])).

fof(f72,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ( r2_hidden(X3,X0)
           => ( ( ~ r2_hidden(X3,k1_relset_1(X0,X1,X2))
               => r2_hidden(o_1_1_funct_2(X1),X1) )
              & ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
               => r2_hidden(k1_funct_1(X2,X3),X1) ) ) )
       => ? [X3] :
            ( ! [X4] :
                ( r2_hidden(X4,X0)
               => ( ( ~ r2_hidden(X4,k1_relset_1(X0,X1,X2))
                   => o_1_1_funct_2(X1) = k1_funct_1(X3,X4) )
                  & ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                   => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ( r2_hidden(X3,X0)
           => ( ( ~ r2_hidden(X3,k1_relset_1(X0,X1,X2))
               => r2_hidden(o_1_1_funct_2(X1),X1) )
              & ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
               => r2_hidden(k1_funct_1(X2,X3),X1) ) ) )
       => ? [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,X0)
               => ( ( ~ r2_hidden(X5,k1_relset_1(X0,X1,X2))
                   => o_1_1_funct_2(X1) = k1_funct_1(X4,X5) )
                  & ( r2_hidden(X5,k1_relset_1(X0,X1,X2))
                   => k1_funct_1(X2,X5) = k1_funct_1(X4,X5) ) ) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X4,X0,X1)
            & v1_funct_1(X4) ) ) ) ),
    inference(rectify,[],[f9])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ? [X4] :
          ( ! [X5] :
              ( ( ( o_1_1_funct_2(X1) = k1_funct_1(X4,X5)
                  | r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
                & ( k1_funct_1(X2,X5) = k1_funct_1(X4,X5)
                  | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) ) )
              | ~ r2_hidden(X5,X0) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X4,X0,X1)
          & v1_funct_1(X4) )
      | ? [X3] :
          ( ( ( ~ r2_hidden(o_1_1_funct_2(X1),X1)
              & ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
            | ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
              & r2_hidden(X3,k1_relset_1(X0,X1,X2)) ) )
          & r2_hidden(X3,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ? [X4] :
          ( ! [X5] :
              ( ( ( o_1_1_funct_2(X1) = k1_funct_1(X4,X5)
                  | r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
                & ( k1_funct_1(X2,X5) = k1_funct_1(X4,X5)
                  | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) ) )
              | ~ r2_hidden(X5,X0) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X4,X0,X1)
          & v1_funct_1(X4) )
      | ? [X3] :
          ( ( ( ~ r2_hidden(o_1_1_funct_2(X1),X1)
              & ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
            | ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
              & r2_hidden(X3,k1_relset_1(X0,X1,X2)) ) )
          & r2_hidden(X3,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f36,plain,(
    ! [X1,X2,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(o_1_1_funct_2(X1),X1)
              & ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
            | ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
              & r2_hidden(X3,k1_relset_1(X0,X1,X2)) ) )
          & r2_hidden(X3,X0) )
      | ~ sP0(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ? [X4] :
          ( ! [X5] :
              ( ( ( o_1_1_funct_2(X1) = k1_funct_1(X4,X5)
                  | r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
                & ( k1_funct_1(X2,X5) = k1_funct_1(X4,X5)
                  | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) ) )
              | ~ r2_hidden(X5,X0) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X4,X0,X1)
          & v1_funct_1(X4) )
      | sP0(X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f26,f36])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ! [X4] :
              ( ( ( o_1_1_funct_2(X1) = k1_funct_1(X3,X4)
                  | r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
                & ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                  | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      | sP0(X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(rectify,[],[f37])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ( ( o_1_1_funct_2(X1) = k1_funct_1(X3,X4)
                  | r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
                & ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                  | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ! [X4] :
            ( ( ( o_1_1_funct_2(X1) = k1_funct_1(sK2(X0,X1,X2),X4)
                | r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
              & ( k1_funct_1(X2,X4) = k1_funct_1(sK2(X0,X1,X2),X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
            | ~ r2_hidden(X4,X0) )
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK2(X0,X1,X2),X0,X1)
        & v1_funct_1(sK2(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X4] :
            ( ( ( o_1_1_funct_2(X1) = k1_funct_1(sK2(X0,X1,X2),X4)
                | r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
              & ( k1_funct_1(X2,X4) = k1_funct_1(sK2(X0,X1,X2),X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
            | ~ r2_hidden(X4,X0) )
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK2(X0,X1,X2),X0,X1)
        & v1_funct_1(sK2(X0,X1,X2)) )
      | sP0(X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(sK2(X0,X1,X2),X0,X1)
      | sP0(X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f74,plain,(
    ! [X3] :
      ( r2_hidden(sK6(X3),k1_relset_1(sK3,sK4,sK5))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      | ~ v1_funct_2(X3,sK3,sK4)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(sK2(X0,X1,X2))
      | sP0(X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( k1_funct_1(X2,X4) = k1_funct_1(sK2(X0,X1,X2),X4)
      | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2))
      | ~ r2_hidden(X4,X0)
      | sP0(X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f71,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f47])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f18])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f75,plain,(
    ! [X3] :
      ( k1_funct_1(sK5,sK6(X3)) != k1_funct_1(X3,sK6(X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      | ~ v1_funct_2(X3,sK3,sK4)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(o_1_1_funct_2(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : m1_subset_1(o_1_1_funct_2(X0),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X1,X2,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(o_1_1_funct_2(X1),X1)
              & ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
            | ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
              & r2_hidden(X3,k1_relset_1(X0,X1,X2)) ) )
          & r2_hidden(X3,X0) )
      | ~ sP0(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(o_1_1_funct_2(X0),X0)
              & ~ r2_hidden(X3,k1_relset_1(X2,X0,X1)) )
            | ( ~ r2_hidden(k1_funct_1(X1,X3),X0)
              & r2_hidden(X3,k1_relset_1(X2,X0,X1)) ) )
          & r2_hidden(X3,X2) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(o_1_1_funct_2(X0),X0)
              & ~ r2_hidden(X3,k1_relset_1(X2,X0,X1)) )
            | ( ~ r2_hidden(k1_funct_1(X1,X3),X0)
              & r2_hidden(X3,k1_relset_1(X2,X0,X1)) ) )
          & r2_hidden(X3,X2) )
     => ( ( ( ~ r2_hidden(o_1_1_funct_2(X0),X0)
            & ~ r2_hidden(sK1(X0,X1,X2),k1_relset_1(X2,X0,X1)) )
          | ( ~ r2_hidden(k1_funct_1(X1,sK1(X0,X1,X2)),X0)
            & r2_hidden(sK1(X0,X1,X2),k1_relset_1(X2,X0,X1)) ) )
        & r2_hidden(sK1(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ~ r2_hidden(o_1_1_funct_2(X0),X0)
            & ~ r2_hidden(sK1(X0,X1,X2),k1_relset_1(X2,X0,X1)) )
          | ( ~ r2_hidden(k1_funct_1(X1,sK1(X0,X1,X2)),X0)
            & r2_hidden(sK1(X0,X1,X2),k1_relset_1(X2,X0,X1)) ) )
        & r2_hidden(sK1(X0,X1,X2),X2) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(o_1_1_funct_2(X0),X0)
      | r2_hidden(sK1(X0,X1,X2),k1_relset_1(X2,X0,X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => r2_hidden(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(o_1_1_funct_2(X0),X0)
      | ~ r2_hidden(k1_funct_1(X1,sK1(X0,X1,X2)),X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f70,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f76,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f70,f53])).

fof(f73,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f47])).

fof(f77,plain,
    ( o_0_0_xboole_0 = sK3
    | o_0_0_xboole_0 != sK4 ),
    inference(definition_unfolding,[],[f73,f53,f53])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2439,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2451,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3087,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2439,c_2451])).

cnf(c_16,plain,
    ( sP0(X0,X1,X2)
    | v1_funct_2(sK2(X2,X0,X1),X2,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_23,negated_conjecture,
    ( ~ v1_funct_2(X0,sK3,sK4)
    | r2_hidden(sK6(X0),k1_relset_1(sK3,sK4,sK5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_445,plain,
    ( sP0(X0,X1,X2)
    | r2_hidden(sK6(X3),k1_relset_1(sK3,sK4,sK5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X3)
    | sK2(X2,X0,X1) != X3
    | sK4 != X0
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_446,plain,
    ( sP0(sK4,X0,sK3)
    | r2_hidden(sK6(sK2(sK3,sK4,X0)),k1_relset_1(sK3,sK4,sK5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ m1_subset_1(sK2(sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK2(sK3,sK4,X0)) ),
    inference(unflattening,[status(thm)],[c_445])).

cnf(c_17,plain,
    ( sP0(X0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
    | ~ v1_funct_1(X1)
    | v1_funct_1(sK2(X2,X0,X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_15,plain,
    ( sP0(X0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
    | m1_subset_1(sK2(X2,X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_462,plain,
    ( sP0(sK4,X0,sK3)
    | r2_hidden(sK6(sK2(sK3,sK4,X0)),k1_relset_1(sK3,sK4,sK5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_446,c_17,c_15])).

cnf(c_2434,plain,
    ( sP0(sK4,X0,sK3) = iProver_top
    | r2_hidden(sK6(sK2(sK3,sK4,X0)),k1_relset_1(sK3,sK4,sK5)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_462])).

cnf(c_3116,plain,
    ( sP0(sK4,X0,sK3) = iProver_top
    | r2_hidden(sK6(sK2(sK3,sK4,X0)),k1_relat_1(sK5)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3087,c_2434])).

cnf(c_14,plain,
    ( sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,k1_relset_1(X2,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
    | ~ v1_funct_1(X1)
    | k1_funct_1(sK2(X2,X0,X1),X3) = k1_funct_1(X1,X3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2445,plain,
    ( k1_funct_1(sK2(X0,X1,X2),X3) = k1_funct_1(X2,X3)
    | sP0(X1,X2,X0) = iProver_top
    | r2_hidden(X3,X0) != iProver_top
    | r2_hidden(X3,k1_relset_1(X0,X1,X2)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4149,plain,
    ( k1_funct_1(sK2(sK3,sK4,sK5),X0) = k1_funct_1(sK5,X0)
    | sP0(sK4,sK5,sK3) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3087,c_2445])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_27,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_28,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4380,plain,
    ( k1_funct_1(sK2(sK3,sK4,sK5),X0) = k1_funct_1(sK5,X0)
    | sP0(sK4,sK5,sK3) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4149,c_27,c_28])).

cnf(c_4393,plain,
    ( k1_funct_1(sK2(sK3,sK4,sK5),sK6(sK2(sK3,sK4,X0))) = k1_funct_1(sK5,sK6(sK2(sK3,sK4,X0)))
    | sP0(sK4,X0,sK3) = iProver_top
    | sP0(sK4,sK5,sK3) = iProver_top
    | r2_hidden(sK6(sK2(sK3,sK4,X0)),sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3116,c_4380])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_partfun1(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_0,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_286,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_xboole_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(resolution,[status(thm)],[c_2,c_0])).

cnf(c_290,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_funct_2(X0,X1,X2)
    | ~ v1_xboole_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_286,c_2,c_0])).

cnf(c_291,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_290])).

cnf(c_22,negated_conjecture,
    ( ~ v1_funct_2(X0,sK3,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(X0)
    | k1_funct_1(sK5,sK6(X0)) != k1_funct_1(X0,sK6(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_427,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | X3 != X0
    | k1_funct_1(X3,sK6(X3)) != k1_funct_1(sK5,sK6(X3))
    | sK4 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_291,c_22])).

cnf(c_428,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_xboole_0(sK3)
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK6(X0)) != k1_funct_1(sK5,sK6(X0)) ),
    inference(unflattening,[status(thm)],[c_427])).

cnf(c_2435,plain,
    ( k1_funct_1(X0,sK6(X0)) != k1_funct_1(sK5,sK6(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_xboole_0(sK3) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_428])).

cnf(c_2712,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_xboole_0(sK3) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2435])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2453,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3164,plain,
    ( m1_subset_1(k1_relat_1(sK5),k1_zfmisc_1(sK3)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3087,c_2453])).

cnf(c_3305,plain,
    ( m1_subset_1(k1_relat_1(sK5),k1_zfmisc_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3164,c_28])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2441,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3319,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | m1_subset_1(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3305,c_2441])).

cnf(c_3875,plain,
    ( sP0(sK4,X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | m1_subset_1(sK6(sK2(sK3,sK4,X0)),sK3) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3116,c_3319])).

cnf(c_19,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2442,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4734,plain,
    ( sP0(sK4,X0,sK3) = iProver_top
    | r2_hidden(sK6(sK2(sK3,sK4,X0)),sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3875,c_2442])).

cnf(c_5543,plain,
    ( sP0(sK4,sK5,sK3) = iProver_top
    | sP0(sK4,X0,sK3) = iProver_top
    | k1_funct_1(sK2(sK3,sK4,sK5),sK6(sK2(sK3,sK4,X0))) = k1_funct_1(sK5,sK6(sK2(sK3,sK4,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4393,c_27,c_28,c_2712,c_4734])).

cnf(c_5544,plain,
    ( k1_funct_1(sK2(sK3,sK4,sK5),sK6(sK2(sK3,sK4,X0))) = k1_funct_1(sK5,sK6(sK2(sK3,sK4,X0)))
    | sP0(sK4,X0,sK3) = iProver_top
    | sP0(sK4,sK5,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5543])).

cnf(c_5557,plain,
    ( k1_funct_1(sK2(sK3,sK4,sK5),sK6(sK2(sK3,sK4,sK5))) = k1_funct_1(sK5,sK6(sK2(sK3,sK4,sK5)))
    | sP0(sK4,sK5,sK3) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2439,c_5544])).

cnf(c_470,plain,
    ( sP0(X0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X3)
    | sK2(X2,X0,X1) != X3
    | k1_funct_1(X3,sK6(X3)) != k1_funct_1(sK5,sK6(X3))
    | sK4 != X0
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_471,plain,
    ( sP0(sK4,X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ m1_subset_1(sK2(sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK2(sK3,sK4,X0))
    | k1_funct_1(sK2(sK3,sK4,X0),sK6(sK2(sK3,sK4,X0))) != k1_funct_1(sK5,sK6(sK2(sK3,sK4,X0))) ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_487,plain,
    ( sP0(sK4,X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(X0)
    | k1_funct_1(sK2(sK3,sK4,X0),sK6(sK2(sK3,sK4,X0))) != k1_funct_1(sK5,sK6(sK2(sK3,sK4,X0))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_471,c_17,c_15])).

cnf(c_2640,plain,
    ( sP0(sK4,sK5,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK5)
    | k1_funct_1(sK2(sK3,sK4,sK5),sK6(sK2(sK3,sK4,sK5))) != k1_funct_1(sK5,sK6(sK2(sK3,sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_487])).

cnf(c_2641,plain,
    ( k1_funct_1(sK2(sK3,sK4,sK5),sK6(sK2(sK3,sK4,sK5))) != k1_funct_1(sK5,sK6(sK2(sK3,sK4,sK5)))
    | sP0(sK4,sK5,sK3) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2640])).

cnf(c_5727,plain,
    ( sP0(sK4,sK5,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5557,c_27,c_28,c_2641])).

cnf(c_6,plain,
    ( m1_subset_1(o_1_1_funct_2(X0),X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2452,plain,
    ( m1_subset_1(o_1_1_funct_2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2984,plain,
    ( r2_hidden(o_1_1_funct_2(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2452,c_2442])).

cnf(c_9,plain,
    ( ~ sP0(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),k1_relset_1(X2,X0,X1))
    | ~ r2_hidden(o_1_1_funct_2(X0),X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2449,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),k1_relset_1(X2,X0,X1)) = iProver_top
    | r2_hidden(o_1_1_funct_2(X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3401,plain,
    ( sP0(sK4,sK5,sK3) != iProver_top
    | r2_hidden(sK1(sK4,sK5,sK3),k1_relat_1(sK5)) = iProver_top
    | r2_hidden(o_1_1_funct_2(sK4),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3087,c_2449])).

cnf(c_4,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_338,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | X1 != X3
    | X2 != X5 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_18])).

cnf(c_339,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_353,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_339,c_3])).

cnf(c_2437,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_353])).

cnf(c_2806,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),sK4) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2439,c_2437])).

cnf(c_2999,plain,
    ( r2_hidden(k1_funct_1(sK5,X0),sK4) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2806,c_27])).

cnf(c_3000,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_2999])).

cnf(c_8,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(k1_funct_1(X1,sK1(X0,X1,X2)),X0)
    | ~ r2_hidden(o_1_1_funct_2(X0),X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2450,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(k1_funct_1(X1,sK1(X0,X1,X2)),X0) != iProver_top
    | r2_hidden(o_1_1_funct_2(X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3423,plain,
    ( sP0(sK4,sK5,X0) != iProver_top
    | r2_hidden(sK1(sK4,sK5,X0),k1_relat_1(sK5)) != iProver_top
    | r2_hidden(o_1_1_funct_2(sK4),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3000,c_2450])).

cnf(c_3425,plain,
    ( sP0(sK4,sK5,sK3) != iProver_top
    | r2_hidden(sK1(sK4,sK5,sK3),k1_relat_1(sK5)) != iProver_top
    | r2_hidden(o_1_1_funct_2(sK4),sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3423])).

cnf(c_3737,plain,
    ( sP0(sK4,sK5,sK3) != iProver_top
    | r2_hidden(o_1_1_funct_2(sK4),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3401,c_3425])).

cnf(c_4200,plain,
    ( sP0(sK4,sK5,sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2984,c_3737])).

cnf(c_5732,plain,
    ( v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5727,c_4200])).

cnf(c_21,plain,
    ( ~ v1_xboole_0(X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2440,plain,
    ( o_0_0_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5736,plain,
    ( sK4 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_5732,c_2440])).

cnf(c_24,negated_conjecture,
    ( o_0_0_xboole_0 != sK4
    | o_0_0_xboole_0 = sK3 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_5926,plain,
    ( sK3 = o_0_0_xboole_0
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5736,c_24])).

cnf(c_5927,plain,
    ( sK3 = o_0_0_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5926])).

cnf(c_2715,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2712,c_27,c_28])).

cnf(c_6217,plain,
    ( v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5927,c_2715])).

cnf(c_5898,plain,
    ( sP0(o_0_0_xboole_0,sK5,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5736,c_5727])).

cnf(c_6117,plain,
    ( sP0(o_0_0_xboole_0,sK5,o_0_0_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5898,c_5927])).

cnf(c_5910,plain,
    ( sP0(o_0_0_xboole_0,sK5,sK3) != iProver_top
    | v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5736,c_4200])).

cnf(c_6013,plain,
    ( sP0(o_0_0_xboole_0,sK5,o_0_0_xboole_0) != iProver_top
    | v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5910,c_5927])).

cnf(c_6122,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_6117,c_6013])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6217,c_6122])).


%------------------------------------------------------------------------------
