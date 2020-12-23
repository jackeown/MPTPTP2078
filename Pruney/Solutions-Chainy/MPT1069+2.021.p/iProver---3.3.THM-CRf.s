%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:46 EST 2020

% Result     : Theorem 7.47s
% Output     : CNFRefutation 7.47s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 679 expanded)
%              Number of clauses        :   97 ( 185 expanded)
%              Number of leaves         :   20 ( 234 expanded)
%              Depth                    :   19
%              Number of atoms          :  634 (5250 expanded)
%              Number of equality atoms :  262 (1418 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                  & v1_funct_1(X4) )
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f45,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f46,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f45])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k7_partfun1(X0,X4,k1_funct_1(X3,sK7)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK7)
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK7,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
              & k1_xboole_0 != X1
              & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( k7_partfun1(X0,sK6,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK6),X5)
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK6))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( k7_partfun1(X0,X4,k1_funct_1(sK5,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK5,X4),X5)
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK5),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK5,X1,X2)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                    & k1_xboole_0 != X1
                    & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                    & m1_subset_1(X5,X1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k7_partfun1(sK2,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,X3,X4),X5)
                  & k1_xboole_0 != sK3
                  & r1_tarski(k2_relset_1(sK3,sK4,X3),k1_relset_1(sK4,sK2,X4))
                  & m1_subset_1(X5,sK3) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
          & v1_funct_2(X3,sK3,sK4)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7)
    & k1_xboole_0 != sK3
    & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))
    & m1_subset_1(sK7,sK3)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f46,f64,f63,f62,f61])).

fof(f110,plain,(
    m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f65])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f112,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f65])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f72,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f109,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f65])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f111,plain,(
    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
    inference(cnf_transformation,[],[f65])).

fof(f107,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f65])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f43])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f104,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f105,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f65])).

fof(f106,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f41])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f108,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f65])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f39])).

fof(f96,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f57])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f117,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f77])).

fof(f113,plain,(
    k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f65])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_funct_2(X2,X0,X1)
              & ~ v1_xboole_0(X2)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1702,plain,
    ( m1_subset_1(sK7,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1717,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4159,plain,
    ( r2_hidden(sK7,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1702,c_1717])).

cnf(c_54,plain,
    ( m1_subset_1(sK7,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_39,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2020,plain,
    ( ~ v1_xboole_0(sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2021,plain,
    ( k1_xboole_0 = sK3
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2020])).

cnf(c_2190,plain,
    ( ~ m1_subset_1(X0,sK3)
    | r2_hidden(X0,sK3)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2651,plain,
    ( ~ m1_subset_1(sK7,sK3)
    | r2_hidden(sK7,sK3)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2190])).

cnf(c_2652,plain,
    ( m1_subset_1(sK7,sK3) != iProver_top
    | r2_hidden(sK7,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2651])).

cnf(c_4533,plain,
    ( r2_hidden(sK7,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4159,c_54,c_39,c_2021,c_2652])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1701,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1711,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3654,plain,
    ( k1_relset_1(sK4,sK2,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1701,c_1711])).

cnf(c_40,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1703,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_3735,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relat_1(sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3654,c_1703])).

cnf(c_44,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1699,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_33,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1706,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
    | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4063,plain,
    ( sK4 = k1_xboole_0
    | v1_funct_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1699,c_1706])).

cnf(c_47,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_46,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_49,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_45,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_50,plain,
    ( v1_funct_2(sK5,sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_876,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2036,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_876])).

cnf(c_2038,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2036])).

cnf(c_4666,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4063,c_47,c_49,c_50,c_5,c_2038])).

cnf(c_4667,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4666])).

cnf(c_4675,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK6)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3735,c_4667])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1708,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5441,plain,
    ( k1_relat_1(sK6) = k1_xboole_0
    | v1_funct_2(sK5,sK3,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4675,c_1708])).

cnf(c_35,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1704,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X1,X2,X3) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3312,plain,
    ( sK4 = k1_xboole_0
    | v1_funct_2(sK5,sK3,X0) = iProver_top
    | v1_funct_2(sK5,sK3,sK4) != iProver_top
    | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1699,c_1704])).

cnf(c_3891,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
    | v1_funct_2(sK5,sK3,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3312,c_47,c_49,c_50,c_5,c_2038])).

cnf(c_3892,plain,
    ( v1_funct_2(sK5,sK3,X0) = iProver_top
    | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3891])).

cnf(c_3900,plain,
    ( v1_funct_2(sK5,sK3,k1_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3735,c_3892])).

cnf(c_30458,plain,
    ( r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | k1_relat_1(sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5441,c_49,c_3900])).

cnf(c_30459,plain,
    ( k1_relat_1(sK6) = k1_xboole_0
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_30458])).

cnf(c_22,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_29,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_536,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(resolution,[status(thm)],[c_22,c_29])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_540,plain,
    ( ~ v1_funct_1(X0)
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_536,c_21])).

cnf(c_541,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(renaming,[status(thm)],[c_540])).

cnf(c_1693,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_541])).

cnf(c_2371,plain,
    ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1701,c_1693])).

cnf(c_43,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_52,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_2570,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2371,c_52])).

cnf(c_2571,plain,
    ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2570])).

cnf(c_30474,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | k1_relat_1(sK6) = k1_xboole_0
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_30459,c_2571])).

cnf(c_31215,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(sK6,k1_funct_1(sK5,sK7))
    | k1_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4533,c_30474])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1709,plain,
    ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
    | k1_xboole_0 = X0
    | v1_funct_2(X3,X0,X1) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5905,plain,
    ( k1_funct_1(k8_funct_2(X0,sK4,sK2,X1,sK6),X2) = k1_funct_1(sK6,k1_funct_1(X1,X2))
    | k1_xboole_0 = X0
    | v1_funct_2(X1,X0,sK4) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | r1_tarski(k2_relset_1(X0,sK4,X1),k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3654,c_1709])).

cnf(c_48,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_53,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_12197,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | v1_funct_2(X1,X0,sK4) != iProver_top
    | k1_xboole_0 = X0
    | k1_funct_1(k8_funct_2(X0,sK4,sK2,X1,sK6),X2) = k1_funct_1(sK6,k1_funct_1(X1,X2))
    | r1_tarski(k2_relset_1(X0,sK4,X1),k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5905,c_48,c_52,c_53])).

cnf(c_12198,plain,
    ( k1_funct_1(k8_funct_2(X0,sK4,sK2,X1,sK6),X2) = k1_funct_1(sK6,k1_funct_1(X1,X2))
    | k1_xboole_0 = X0
    | v1_funct_2(X1,X0,sK4) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) != iProver_top
    | r1_tarski(k2_relset_1(X0,sK4,X1),k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_12197])).

cnf(c_12209,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | sK3 = k1_xboole_0
    | v1_funct_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(X0,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3735,c_12198])).

cnf(c_51,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_12,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_107,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_11,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_108,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_875,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2076,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_875])).

cnf(c_2077,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2076])).

cnf(c_12241,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12209,c_49,c_50,c_51,c_39,c_107,c_108,c_2077])).

cnf(c_12250,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_1702,c_12241])).

cnf(c_38,negated_conjecture,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_12379,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(demodulation,[status(thm)],[c_12250,c_38])).

cnf(c_31415,plain,
    ( k1_relat_1(sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_31215,c_12379])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1712,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5440,plain,
    ( v1_xboole_0(k1_relat_1(sK6)) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4675,c_1712])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2189,plain,
    ( ~ v1_funct_2(X0,sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_2846,plain,
    ( ~ v1_funct_2(X0,sK3,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2189])).

cnf(c_2930,plain,
    ( ~ v1_funct_2(sK5,sK3,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3)
    | ~ v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2846])).

cnf(c_2931,plain,
    ( v1_funct_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2930])).

cnf(c_10402,plain,
    ( v1_xboole_0(k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5440,c_48,c_49,c_50,c_51,c_39,c_2021,c_2931])).

cnf(c_31442,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_31415,c_10402])).

cnf(c_119,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_31442,c_119])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 18:10:57 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.47/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.47/1.48  
% 7.47/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.47/1.48  
% 7.47/1.48  ------  iProver source info
% 7.47/1.48  
% 7.47/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.47/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.47/1.48  git: non_committed_changes: false
% 7.47/1.48  git: last_make_outside_of_git: false
% 7.47/1.48  
% 7.47/1.48  ------ 
% 7.47/1.48  
% 7.47/1.48  ------ Input Options
% 7.47/1.48  
% 7.47/1.48  --out_options                           all
% 7.47/1.48  --tptp_safe_out                         true
% 7.47/1.48  --problem_path                          ""
% 7.47/1.48  --include_path                          ""
% 7.47/1.48  --clausifier                            res/vclausify_rel
% 7.47/1.48  --clausifier_options                    --mode clausify
% 7.47/1.48  --stdin                                 false
% 7.47/1.48  --stats_out                             all
% 7.47/1.48  
% 7.47/1.48  ------ General Options
% 7.47/1.48  
% 7.47/1.48  --fof                                   false
% 7.47/1.48  --time_out_real                         305.
% 7.47/1.48  --time_out_virtual                      -1.
% 7.47/1.48  --symbol_type_check                     false
% 7.47/1.48  --clausify_out                          false
% 7.47/1.48  --sig_cnt_out                           false
% 7.47/1.48  --trig_cnt_out                          false
% 7.47/1.48  --trig_cnt_out_tolerance                1.
% 7.47/1.48  --trig_cnt_out_sk_spl                   false
% 7.47/1.48  --abstr_cl_out                          false
% 7.47/1.48  
% 7.47/1.48  ------ Global Options
% 7.47/1.48  
% 7.47/1.48  --schedule                              default
% 7.47/1.48  --add_important_lit                     false
% 7.47/1.48  --prop_solver_per_cl                    1000
% 7.47/1.48  --min_unsat_core                        false
% 7.47/1.48  --soft_assumptions                      false
% 7.47/1.48  --soft_lemma_size                       3
% 7.47/1.48  --prop_impl_unit_size                   0
% 7.47/1.48  --prop_impl_unit                        []
% 7.47/1.48  --share_sel_clauses                     true
% 7.47/1.48  --reset_solvers                         false
% 7.47/1.48  --bc_imp_inh                            [conj_cone]
% 7.47/1.48  --conj_cone_tolerance                   3.
% 7.47/1.48  --extra_neg_conj                        none
% 7.47/1.48  --large_theory_mode                     true
% 7.47/1.48  --prolific_symb_bound                   200
% 7.47/1.48  --lt_threshold                          2000
% 7.47/1.48  --clause_weak_htbl                      true
% 7.47/1.48  --gc_record_bc_elim                     false
% 7.47/1.48  
% 7.47/1.48  ------ Preprocessing Options
% 7.47/1.48  
% 7.47/1.48  --preprocessing_flag                    true
% 7.47/1.48  --time_out_prep_mult                    0.1
% 7.47/1.48  --splitting_mode                        input
% 7.47/1.48  --splitting_grd                         true
% 7.47/1.48  --splitting_cvd                         false
% 7.47/1.48  --splitting_cvd_svl                     false
% 7.47/1.48  --splitting_nvd                         32
% 7.47/1.48  --sub_typing                            true
% 7.47/1.48  --prep_gs_sim                           true
% 7.47/1.48  --prep_unflatten                        true
% 7.47/1.48  --prep_res_sim                          true
% 7.47/1.48  --prep_upred                            true
% 7.47/1.48  --prep_sem_filter                       exhaustive
% 7.47/1.48  --prep_sem_filter_out                   false
% 7.47/1.48  --pred_elim                             true
% 7.47/1.48  --res_sim_input                         true
% 7.47/1.48  --eq_ax_congr_red                       true
% 7.47/1.48  --pure_diseq_elim                       true
% 7.47/1.48  --brand_transform                       false
% 7.47/1.48  --non_eq_to_eq                          false
% 7.47/1.48  --prep_def_merge                        true
% 7.47/1.48  --prep_def_merge_prop_impl              false
% 7.47/1.48  --prep_def_merge_mbd                    true
% 7.47/1.48  --prep_def_merge_tr_red                 false
% 7.47/1.48  --prep_def_merge_tr_cl                  false
% 7.47/1.48  --smt_preprocessing                     true
% 7.47/1.48  --smt_ac_axioms                         fast
% 7.47/1.48  --preprocessed_out                      false
% 7.47/1.48  --preprocessed_stats                    false
% 7.47/1.48  
% 7.47/1.48  ------ Abstraction refinement Options
% 7.47/1.48  
% 7.47/1.48  --abstr_ref                             []
% 7.47/1.48  --abstr_ref_prep                        false
% 7.47/1.48  --abstr_ref_until_sat                   false
% 7.47/1.48  --abstr_ref_sig_restrict                funpre
% 7.47/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.47/1.48  --abstr_ref_under                       []
% 7.47/1.48  
% 7.47/1.48  ------ SAT Options
% 7.47/1.48  
% 7.47/1.48  --sat_mode                              false
% 7.47/1.48  --sat_fm_restart_options                ""
% 7.47/1.48  --sat_gr_def                            false
% 7.47/1.48  --sat_epr_types                         true
% 7.47/1.48  --sat_non_cyclic_types                  false
% 7.47/1.48  --sat_finite_models                     false
% 7.47/1.48  --sat_fm_lemmas                         false
% 7.47/1.48  --sat_fm_prep                           false
% 7.47/1.48  --sat_fm_uc_incr                        true
% 7.47/1.48  --sat_out_model                         small
% 7.47/1.48  --sat_out_clauses                       false
% 7.47/1.48  
% 7.47/1.48  ------ QBF Options
% 7.47/1.48  
% 7.47/1.48  --qbf_mode                              false
% 7.47/1.48  --qbf_elim_univ                         false
% 7.47/1.48  --qbf_dom_inst                          none
% 7.47/1.48  --qbf_dom_pre_inst                      false
% 7.47/1.48  --qbf_sk_in                             false
% 7.47/1.48  --qbf_pred_elim                         true
% 7.47/1.48  --qbf_split                             512
% 7.47/1.48  
% 7.47/1.48  ------ BMC1 Options
% 7.47/1.48  
% 7.47/1.48  --bmc1_incremental                      false
% 7.47/1.48  --bmc1_axioms                           reachable_all
% 7.47/1.48  --bmc1_min_bound                        0
% 7.47/1.48  --bmc1_max_bound                        -1
% 7.47/1.48  --bmc1_max_bound_default                -1
% 7.47/1.48  --bmc1_symbol_reachability              true
% 7.47/1.48  --bmc1_property_lemmas                  false
% 7.47/1.48  --bmc1_k_induction                      false
% 7.47/1.48  --bmc1_non_equiv_states                 false
% 7.47/1.48  --bmc1_deadlock                         false
% 7.47/1.48  --bmc1_ucm                              false
% 7.47/1.48  --bmc1_add_unsat_core                   none
% 7.47/1.48  --bmc1_unsat_core_children              false
% 7.47/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.47/1.48  --bmc1_out_stat                         full
% 7.47/1.48  --bmc1_ground_init                      false
% 7.47/1.48  --bmc1_pre_inst_next_state              false
% 7.47/1.48  --bmc1_pre_inst_state                   false
% 7.47/1.48  --bmc1_pre_inst_reach_state             false
% 7.47/1.48  --bmc1_out_unsat_core                   false
% 7.47/1.48  --bmc1_aig_witness_out                  false
% 7.47/1.48  --bmc1_verbose                          false
% 7.47/1.48  --bmc1_dump_clauses_tptp                false
% 7.47/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.47/1.48  --bmc1_dump_file                        -
% 7.47/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.47/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.47/1.48  --bmc1_ucm_extend_mode                  1
% 7.47/1.48  --bmc1_ucm_init_mode                    2
% 7.47/1.48  --bmc1_ucm_cone_mode                    none
% 7.47/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.47/1.48  --bmc1_ucm_relax_model                  4
% 7.47/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.47/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.47/1.48  --bmc1_ucm_layered_model                none
% 7.47/1.48  --bmc1_ucm_max_lemma_size               10
% 7.47/1.48  
% 7.47/1.48  ------ AIG Options
% 7.47/1.48  
% 7.47/1.48  --aig_mode                              false
% 7.47/1.48  
% 7.47/1.48  ------ Instantiation Options
% 7.47/1.48  
% 7.47/1.48  --instantiation_flag                    true
% 7.47/1.48  --inst_sos_flag                         false
% 7.47/1.48  --inst_sos_phase                        true
% 7.47/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.47/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.47/1.48  --inst_lit_sel_side                     num_symb
% 7.47/1.48  --inst_solver_per_active                1400
% 7.47/1.48  --inst_solver_calls_frac                1.
% 7.47/1.48  --inst_passive_queue_type               priority_queues
% 7.47/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.47/1.48  --inst_passive_queues_freq              [25;2]
% 7.47/1.48  --inst_dismatching                      true
% 7.47/1.48  --inst_eager_unprocessed_to_passive     true
% 7.47/1.48  --inst_prop_sim_given                   true
% 7.47/1.48  --inst_prop_sim_new                     false
% 7.47/1.48  --inst_subs_new                         false
% 7.47/1.48  --inst_eq_res_simp                      false
% 7.47/1.48  --inst_subs_given                       false
% 7.47/1.48  --inst_orphan_elimination               true
% 7.47/1.48  --inst_learning_loop_flag               true
% 7.47/1.48  --inst_learning_start                   3000
% 7.47/1.48  --inst_learning_factor                  2
% 7.47/1.48  --inst_start_prop_sim_after_learn       3
% 7.47/1.48  --inst_sel_renew                        solver
% 7.47/1.48  --inst_lit_activity_flag                true
% 7.47/1.48  --inst_restr_to_given                   false
% 7.47/1.48  --inst_activity_threshold               500
% 7.47/1.48  --inst_out_proof                        true
% 7.47/1.48  
% 7.47/1.48  ------ Resolution Options
% 7.47/1.48  
% 7.47/1.48  --resolution_flag                       true
% 7.47/1.48  --res_lit_sel                           adaptive
% 7.47/1.48  --res_lit_sel_side                      none
% 7.47/1.48  --res_ordering                          kbo
% 7.47/1.48  --res_to_prop_solver                    active
% 7.47/1.48  --res_prop_simpl_new                    false
% 7.47/1.48  --res_prop_simpl_given                  true
% 7.47/1.48  --res_passive_queue_type                priority_queues
% 7.47/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.47/1.48  --res_passive_queues_freq               [15;5]
% 7.47/1.48  --res_forward_subs                      full
% 7.47/1.48  --res_backward_subs                     full
% 7.47/1.48  --res_forward_subs_resolution           true
% 7.47/1.48  --res_backward_subs_resolution          true
% 7.47/1.48  --res_orphan_elimination                true
% 7.47/1.48  --res_time_limit                        2.
% 7.47/1.48  --res_out_proof                         true
% 7.47/1.48  
% 7.47/1.48  ------ Superposition Options
% 7.47/1.48  
% 7.47/1.48  --superposition_flag                    true
% 7.47/1.48  --sup_passive_queue_type                priority_queues
% 7.47/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.47/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.47/1.48  --demod_completeness_check              fast
% 7.47/1.48  --demod_use_ground                      true
% 7.47/1.48  --sup_to_prop_solver                    passive
% 7.47/1.48  --sup_prop_simpl_new                    true
% 7.47/1.48  --sup_prop_simpl_given                  true
% 7.47/1.48  --sup_fun_splitting                     false
% 7.47/1.48  --sup_smt_interval                      50000
% 7.47/1.48  
% 7.47/1.48  ------ Superposition Simplification Setup
% 7.47/1.48  
% 7.47/1.48  --sup_indices_passive                   []
% 7.47/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.47/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.47/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.47/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.47/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.47/1.48  --sup_full_bw                           [BwDemod]
% 7.47/1.48  --sup_immed_triv                        [TrivRules]
% 7.47/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.47/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.47/1.48  --sup_immed_bw_main                     []
% 7.47/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.47/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.47/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.47/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.47/1.48  
% 7.47/1.48  ------ Combination Options
% 7.47/1.48  
% 7.47/1.48  --comb_res_mult                         3
% 7.47/1.48  --comb_sup_mult                         2
% 7.47/1.48  --comb_inst_mult                        10
% 7.47/1.48  
% 7.47/1.48  ------ Debug Options
% 7.47/1.48  
% 7.47/1.48  --dbg_backtrace                         false
% 7.47/1.48  --dbg_dump_prop_clauses                 false
% 7.47/1.48  --dbg_dump_prop_clauses_file            -
% 7.47/1.48  --dbg_out_stat                          false
% 7.47/1.48  ------ Parsing...
% 7.47/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.47/1.48  
% 7.47/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.47/1.48  
% 7.47/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.47/1.48  
% 7.47/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.47/1.48  ------ Proving...
% 7.47/1.48  ------ Problem Properties 
% 7.47/1.48  
% 7.47/1.48  
% 7.47/1.48  clauses                                 41
% 7.47/1.48  conjectures                             10
% 7.47/1.48  EPR                                     17
% 7.47/1.48  Horn                                    32
% 7.47/1.48  unary                                   14
% 7.47/1.48  binary                                  9
% 7.47/1.48  lits                                    110
% 7.47/1.48  lits eq                                 16
% 7.47/1.48  fd_pure                                 0
% 7.47/1.48  fd_pseudo                               0
% 7.47/1.48  fd_cond                                 6
% 7.47/1.48  fd_pseudo_cond                          1
% 7.47/1.48  AC symbols                              0
% 7.47/1.48  
% 7.47/1.48  ------ Schedule dynamic 5 is on 
% 7.47/1.48  
% 7.47/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.47/1.48  
% 7.47/1.48  
% 7.47/1.48  ------ 
% 7.47/1.48  Current options:
% 7.47/1.48  ------ 
% 7.47/1.48  
% 7.47/1.48  ------ Input Options
% 7.47/1.48  
% 7.47/1.48  --out_options                           all
% 7.47/1.48  --tptp_safe_out                         true
% 7.47/1.48  --problem_path                          ""
% 7.47/1.48  --include_path                          ""
% 7.47/1.48  --clausifier                            res/vclausify_rel
% 7.47/1.48  --clausifier_options                    --mode clausify
% 7.47/1.48  --stdin                                 false
% 7.47/1.48  --stats_out                             all
% 7.47/1.48  
% 7.47/1.48  ------ General Options
% 7.47/1.48  
% 7.47/1.48  --fof                                   false
% 7.47/1.48  --time_out_real                         305.
% 7.47/1.48  --time_out_virtual                      -1.
% 7.47/1.48  --symbol_type_check                     false
% 7.47/1.48  --clausify_out                          false
% 7.47/1.48  --sig_cnt_out                           false
% 7.47/1.48  --trig_cnt_out                          false
% 7.47/1.48  --trig_cnt_out_tolerance                1.
% 7.47/1.48  --trig_cnt_out_sk_spl                   false
% 7.47/1.48  --abstr_cl_out                          false
% 7.47/1.48  
% 7.47/1.48  ------ Global Options
% 7.47/1.48  
% 7.47/1.48  --schedule                              default
% 7.47/1.48  --add_important_lit                     false
% 7.47/1.48  --prop_solver_per_cl                    1000
% 7.47/1.48  --min_unsat_core                        false
% 7.47/1.48  --soft_assumptions                      false
% 7.47/1.48  --soft_lemma_size                       3
% 7.47/1.48  --prop_impl_unit_size                   0
% 7.47/1.48  --prop_impl_unit                        []
% 7.47/1.48  --share_sel_clauses                     true
% 7.47/1.48  --reset_solvers                         false
% 7.47/1.48  --bc_imp_inh                            [conj_cone]
% 7.47/1.48  --conj_cone_tolerance                   3.
% 7.47/1.48  --extra_neg_conj                        none
% 7.47/1.48  --large_theory_mode                     true
% 7.47/1.48  --prolific_symb_bound                   200
% 7.47/1.48  --lt_threshold                          2000
% 7.47/1.48  --clause_weak_htbl                      true
% 7.47/1.48  --gc_record_bc_elim                     false
% 7.47/1.48  
% 7.47/1.48  ------ Preprocessing Options
% 7.47/1.48  
% 7.47/1.48  --preprocessing_flag                    true
% 7.47/1.48  --time_out_prep_mult                    0.1
% 7.47/1.48  --splitting_mode                        input
% 7.47/1.48  --splitting_grd                         true
% 7.47/1.48  --splitting_cvd                         false
% 7.47/1.48  --splitting_cvd_svl                     false
% 7.47/1.48  --splitting_nvd                         32
% 7.47/1.48  --sub_typing                            true
% 7.47/1.48  --prep_gs_sim                           true
% 7.47/1.48  --prep_unflatten                        true
% 7.47/1.48  --prep_res_sim                          true
% 7.47/1.48  --prep_upred                            true
% 7.47/1.48  --prep_sem_filter                       exhaustive
% 7.47/1.48  --prep_sem_filter_out                   false
% 7.47/1.48  --pred_elim                             true
% 7.47/1.48  --res_sim_input                         true
% 7.47/1.48  --eq_ax_congr_red                       true
% 7.47/1.48  --pure_diseq_elim                       true
% 7.47/1.48  --brand_transform                       false
% 7.47/1.48  --non_eq_to_eq                          false
% 7.47/1.48  --prep_def_merge                        true
% 7.47/1.48  --prep_def_merge_prop_impl              false
% 7.47/1.48  --prep_def_merge_mbd                    true
% 7.47/1.48  --prep_def_merge_tr_red                 false
% 7.47/1.48  --prep_def_merge_tr_cl                  false
% 7.47/1.48  --smt_preprocessing                     true
% 7.47/1.48  --smt_ac_axioms                         fast
% 7.47/1.48  --preprocessed_out                      false
% 7.47/1.48  --preprocessed_stats                    false
% 7.47/1.48  
% 7.47/1.48  ------ Abstraction refinement Options
% 7.47/1.48  
% 7.47/1.48  --abstr_ref                             []
% 7.47/1.48  --abstr_ref_prep                        false
% 7.47/1.48  --abstr_ref_until_sat                   false
% 7.47/1.48  --abstr_ref_sig_restrict                funpre
% 7.47/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.47/1.48  --abstr_ref_under                       []
% 7.47/1.48  
% 7.47/1.48  ------ SAT Options
% 7.47/1.48  
% 7.47/1.48  --sat_mode                              false
% 7.47/1.48  --sat_fm_restart_options                ""
% 7.47/1.48  --sat_gr_def                            false
% 7.47/1.48  --sat_epr_types                         true
% 7.47/1.48  --sat_non_cyclic_types                  false
% 7.47/1.48  --sat_finite_models                     false
% 7.47/1.48  --sat_fm_lemmas                         false
% 7.47/1.48  --sat_fm_prep                           false
% 7.47/1.48  --sat_fm_uc_incr                        true
% 7.47/1.48  --sat_out_model                         small
% 7.47/1.48  --sat_out_clauses                       false
% 7.47/1.48  
% 7.47/1.48  ------ QBF Options
% 7.47/1.48  
% 7.47/1.48  --qbf_mode                              false
% 7.47/1.48  --qbf_elim_univ                         false
% 7.47/1.48  --qbf_dom_inst                          none
% 7.47/1.48  --qbf_dom_pre_inst                      false
% 7.47/1.48  --qbf_sk_in                             false
% 7.47/1.48  --qbf_pred_elim                         true
% 7.47/1.48  --qbf_split                             512
% 7.47/1.48  
% 7.47/1.48  ------ BMC1 Options
% 7.47/1.48  
% 7.47/1.48  --bmc1_incremental                      false
% 7.47/1.48  --bmc1_axioms                           reachable_all
% 7.47/1.48  --bmc1_min_bound                        0
% 7.47/1.48  --bmc1_max_bound                        -1
% 7.47/1.48  --bmc1_max_bound_default                -1
% 7.47/1.48  --bmc1_symbol_reachability              true
% 7.47/1.48  --bmc1_property_lemmas                  false
% 7.47/1.48  --bmc1_k_induction                      false
% 7.47/1.48  --bmc1_non_equiv_states                 false
% 7.47/1.48  --bmc1_deadlock                         false
% 7.47/1.48  --bmc1_ucm                              false
% 7.47/1.48  --bmc1_add_unsat_core                   none
% 7.47/1.48  --bmc1_unsat_core_children              false
% 7.47/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.47/1.48  --bmc1_out_stat                         full
% 7.47/1.48  --bmc1_ground_init                      false
% 7.47/1.48  --bmc1_pre_inst_next_state              false
% 7.47/1.48  --bmc1_pre_inst_state                   false
% 7.47/1.48  --bmc1_pre_inst_reach_state             false
% 7.47/1.48  --bmc1_out_unsat_core                   false
% 7.47/1.48  --bmc1_aig_witness_out                  false
% 7.47/1.48  --bmc1_verbose                          false
% 7.47/1.48  --bmc1_dump_clauses_tptp                false
% 7.47/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.47/1.48  --bmc1_dump_file                        -
% 7.47/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.47/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.47/1.48  --bmc1_ucm_extend_mode                  1
% 7.47/1.48  --bmc1_ucm_init_mode                    2
% 7.47/1.48  --bmc1_ucm_cone_mode                    none
% 7.47/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.47/1.48  --bmc1_ucm_relax_model                  4
% 7.47/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.47/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.47/1.48  --bmc1_ucm_layered_model                none
% 7.47/1.48  --bmc1_ucm_max_lemma_size               10
% 7.47/1.48  
% 7.47/1.48  ------ AIG Options
% 7.47/1.48  
% 7.47/1.48  --aig_mode                              false
% 7.47/1.48  
% 7.47/1.48  ------ Instantiation Options
% 7.47/1.48  
% 7.47/1.48  --instantiation_flag                    true
% 7.47/1.48  --inst_sos_flag                         false
% 7.47/1.48  --inst_sos_phase                        true
% 7.47/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.47/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.47/1.48  --inst_lit_sel_side                     none
% 7.47/1.48  --inst_solver_per_active                1400
% 7.47/1.48  --inst_solver_calls_frac                1.
% 7.47/1.48  --inst_passive_queue_type               priority_queues
% 7.47/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.47/1.48  --inst_passive_queues_freq              [25;2]
% 7.47/1.48  --inst_dismatching                      true
% 7.47/1.48  --inst_eager_unprocessed_to_passive     true
% 7.47/1.48  --inst_prop_sim_given                   true
% 7.47/1.48  --inst_prop_sim_new                     false
% 7.47/1.48  --inst_subs_new                         false
% 7.47/1.48  --inst_eq_res_simp                      false
% 7.47/1.48  --inst_subs_given                       false
% 7.47/1.48  --inst_orphan_elimination               true
% 7.47/1.48  --inst_learning_loop_flag               true
% 7.47/1.48  --inst_learning_start                   3000
% 7.47/1.48  --inst_learning_factor                  2
% 7.47/1.48  --inst_start_prop_sim_after_learn       3
% 7.47/1.48  --inst_sel_renew                        solver
% 7.47/1.48  --inst_lit_activity_flag                true
% 7.47/1.48  --inst_restr_to_given                   false
% 7.47/1.48  --inst_activity_threshold               500
% 7.47/1.48  --inst_out_proof                        true
% 7.47/1.48  
% 7.47/1.48  ------ Resolution Options
% 7.47/1.48  
% 7.47/1.48  --resolution_flag                       false
% 7.47/1.48  --res_lit_sel                           adaptive
% 7.47/1.48  --res_lit_sel_side                      none
% 7.47/1.48  --res_ordering                          kbo
% 7.47/1.48  --res_to_prop_solver                    active
% 7.47/1.48  --res_prop_simpl_new                    false
% 7.47/1.48  --res_prop_simpl_given                  true
% 7.47/1.48  --res_passive_queue_type                priority_queues
% 7.47/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.47/1.48  --res_passive_queues_freq               [15;5]
% 7.47/1.48  --res_forward_subs                      full
% 7.47/1.48  --res_backward_subs                     full
% 7.47/1.48  --res_forward_subs_resolution           true
% 7.47/1.48  --res_backward_subs_resolution          true
% 7.47/1.48  --res_orphan_elimination                true
% 7.47/1.48  --res_time_limit                        2.
% 7.47/1.48  --res_out_proof                         true
% 7.47/1.48  
% 7.47/1.48  ------ Superposition Options
% 7.47/1.48  
% 7.47/1.48  --superposition_flag                    true
% 7.47/1.48  --sup_passive_queue_type                priority_queues
% 7.47/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.47/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.47/1.48  --demod_completeness_check              fast
% 7.47/1.48  --demod_use_ground                      true
% 7.47/1.48  --sup_to_prop_solver                    passive
% 7.47/1.48  --sup_prop_simpl_new                    true
% 7.47/1.48  --sup_prop_simpl_given                  true
% 7.47/1.48  --sup_fun_splitting                     false
% 7.47/1.48  --sup_smt_interval                      50000
% 7.47/1.48  
% 7.47/1.48  ------ Superposition Simplification Setup
% 7.47/1.48  
% 7.47/1.48  --sup_indices_passive                   []
% 7.47/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.47/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.47/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.47/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.47/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.47/1.48  --sup_full_bw                           [BwDemod]
% 7.47/1.48  --sup_immed_triv                        [TrivRules]
% 7.47/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.47/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.47/1.48  --sup_immed_bw_main                     []
% 7.47/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.47/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.47/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.47/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.47/1.48  
% 7.47/1.48  ------ Combination Options
% 7.47/1.48  
% 7.47/1.48  --comb_res_mult                         3
% 7.47/1.48  --comb_sup_mult                         2
% 7.47/1.48  --comb_inst_mult                        10
% 7.47/1.48  
% 7.47/1.48  ------ Debug Options
% 7.47/1.48  
% 7.47/1.48  --dbg_backtrace                         false
% 7.47/1.48  --dbg_dump_prop_clauses                 false
% 7.47/1.48  --dbg_dump_prop_clauses_file            -
% 7.47/1.48  --dbg_out_stat                          false
% 7.47/1.48  
% 7.47/1.48  
% 7.47/1.48  
% 7.47/1.48  
% 7.47/1.48  ------ Proving...
% 7.47/1.48  
% 7.47/1.48  
% 7.47/1.48  % SZS status Theorem for theBenchmark.p
% 7.47/1.48  
% 7.47/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.47/1.48  
% 7.47/1.48  fof(f21,conjecture,(
% 7.47/1.48    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 7.47/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.48  
% 7.47/1.48  fof(f22,negated_conjecture,(
% 7.47/1.48    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 7.47/1.48    inference(negated_conjecture,[],[f21])).
% 7.47/1.48  
% 7.47/1.48  fof(f45,plain,(
% 7.47/1.48    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 7.47/1.48    inference(ennf_transformation,[],[f22])).
% 7.47/1.48  
% 7.47/1.48  fof(f46,plain,(
% 7.47/1.48    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 7.47/1.48    inference(flattening,[],[f45])).
% 7.47/1.48  
% 7.47/1.48  fof(f64,plain,(
% 7.47/1.48    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k7_partfun1(X0,X4,k1_funct_1(X3,sK7)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK7) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK7,X1))) )),
% 7.47/1.48    introduced(choice_axiom,[])).
% 7.47/1.48  
% 7.47/1.48  fof(f63,plain,(
% 7.47/1.48    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k7_partfun1(X0,sK6,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK6),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK6)) & m1_subset_1(X5,X1)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK6))) )),
% 7.47/1.48    introduced(choice_axiom,[])).
% 7.47/1.48  
% 7.47/1.48  fof(f62,plain,(
% 7.47/1.48    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(sK5,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK5,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK5),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK5,X1,X2) & v1_funct_1(sK5))) )),
% 7.47/1.48    introduced(choice_axiom,[])).
% 7.47/1.48  
% 7.47/1.48  fof(f61,plain,(
% 7.47/1.48    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(sK2,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,X3,X4),X5) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,X3),k1_relset_1(sK4,sK2,X4)) & m1_subset_1(X5,sK3)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & ~v1_xboole_0(sK4))),
% 7.47/1.48    introduced(choice_axiom,[])).
% 7.47/1.48  
% 7.47/1.48  fof(f65,plain,(
% 7.47/1.48    (((k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) & m1_subset_1(sK7,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)) & ~v1_xboole_0(sK4)),
% 7.47/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f46,f64,f63,f62,f61])).
% 7.47/1.48  
% 7.47/1.48  fof(f110,plain,(
% 7.47/1.48    m1_subset_1(sK7,sK3)),
% 7.47/1.48    inference(cnf_transformation,[],[f65])).
% 7.47/1.48  
% 7.47/1.48  fof(f7,axiom,(
% 7.47/1.48    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 7.47/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.48  
% 7.47/1.48  fof(f26,plain,(
% 7.47/1.48    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 7.47/1.48    inference(ennf_transformation,[],[f7])).
% 7.47/1.48  
% 7.47/1.48  fof(f59,plain,(
% 7.47/1.48    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 7.47/1.48    inference(nnf_transformation,[],[f26])).
% 7.47/1.48  
% 7.47/1.48  fof(f79,plain,(
% 7.47/1.48    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.47/1.48    inference(cnf_transformation,[],[f59])).
% 7.47/1.48  
% 7.47/1.48  fof(f112,plain,(
% 7.47/1.48    k1_xboole_0 != sK3),
% 7.47/1.48    inference(cnf_transformation,[],[f65])).
% 7.47/1.48  
% 7.47/1.48  fof(f4,axiom,(
% 7.47/1.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 7.47/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.48  
% 7.47/1.48  fof(f25,plain,(
% 7.47/1.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 7.47/1.48    inference(ennf_transformation,[],[f4])).
% 7.47/1.48  
% 7.47/1.48  fof(f72,plain,(
% 7.47/1.48    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 7.47/1.48    inference(cnf_transformation,[],[f25])).
% 7.47/1.48  
% 7.47/1.48  fof(f109,plain,(
% 7.47/1.48    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))),
% 7.47/1.48    inference(cnf_transformation,[],[f65])).
% 7.47/1.48  
% 7.47/1.48  fof(f15,axiom,(
% 7.47/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 7.47/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.48  
% 7.47/1.48  fof(f34,plain,(
% 7.47/1.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.47/1.48    inference(ennf_transformation,[],[f15])).
% 7.47/1.48  
% 7.47/1.48  fof(f91,plain,(
% 7.47/1.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.47/1.48    inference(cnf_transformation,[],[f34])).
% 7.47/1.48  
% 7.47/1.48  fof(f111,plain,(
% 7.47/1.48    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))),
% 7.47/1.48    inference(cnf_transformation,[],[f65])).
% 7.47/1.48  
% 7.47/1.48  fof(f107,plain,(
% 7.47/1.48    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 7.47/1.48    inference(cnf_transformation,[],[f65])).
% 7.47/1.48  
% 7.47/1.48  fof(f20,axiom,(
% 7.47/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.47/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.48  
% 7.47/1.48  fof(f43,plain,(
% 7.47/1.48    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.47/1.48    inference(ennf_transformation,[],[f20])).
% 7.47/1.48  
% 7.47/1.48  fof(f44,plain,(
% 7.47/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.47/1.48    inference(flattening,[],[f43])).
% 7.47/1.48  
% 7.47/1.48  fof(f102,plain,(
% 7.47/1.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.47/1.48    inference(cnf_transformation,[],[f44])).
% 7.47/1.48  
% 7.47/1.48  fof(f104,plain,(
% 7.47/1.48    ~v1_xboole_0(sK4)),
% 7.47/1.48    inference(cnf_transformation,[],[f65])).
% 7.47/1.48  
% 7.47/1.48  fof(f105,plain,(
% 7.47/1.48    v1_funct_1(sK5)),
% 7.47/1.48    inference(cnf_transformation,[],[f65])).
% 7.47/1.48  
% 7.47/1.48  fof(f106,plain,(
% 7.47/1.48    v1_funct_2(sK5,sK3,sK4)),
% 7.47/1.48    inference(cnf_transformation,[],[f65])).
% 7.47/1.48  
% 7.47/1.48  fof(f3,axiom,(
% 7.47/1.48    v1_xboole_0(k1_xboole_0)),
% 7.47/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.48  
% 7.47/1.48  fof(f71,plain,(
% 7.47/1.48    v1_xboole_0(k1_xboole_0)),
% 7.47/1.48    inference(cnf_transformation,[],[f3])).
% 7.47/1.48  
% 7.47/1.48  fof(f19,axiom,(
% 7.47/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 7.47/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.48  
% 7.47/1.48  fof(f41,plain,(
% 7.47/1.48    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.47/1.48    inference(ennf_transformation,[],[f19])).
% 7.47/1.48  
% 7.47/1.48  fof(f42,plain,(
% 7.47/1.48    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.47/1.48    inference(flattening,[],[f41])).
% 7.47/1.48  
% 7.47/1.48  fof(f97,plain,(
% 7.47/1.48    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.47/1.48    inference(cnf_transformation,[],[f42])).
% 7.47/1.48  
% 7.47/1.48  fof(f100,plain,(
% 7.47/1.48    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.47/1.48    inference(cnf_transformation,[],[f44])).
% 7.47/1.48  
% 7.47/1.48  fof(f12,axiom,(
% 7.47/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.47/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.48  
% 7.47/1.48  fof(f23,plain,(
% 7.47/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 7.47/1.48    inference(pure_predicate_removal,[],[f12])).
% 7.47/1.48  
% 7.47/1.48  fof(f31,plain,(
% 7.47/1.48    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.47/1.48    inference(ennf_transformation,[],[f23])).
% 7.47/1.48  
% 7.47/1.48  fof(f88,plain,(
% 7.47/1.48    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.47/1.48    inference(cnf_transformation,[],[f31])).
% 7.47/1.48  
% 7.47/1.48  fof(f17,axiom,(
% 7.47/1.48    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 7.47/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.48  
% 7.47/1.48  fof(f37,plain,(
% 7.47/1.48    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.47/1.48    inference(ennf_transformation,[],[f17])).
% 7.47/1.48  
% 7.47/1.48  fof(f38,plain,(
% 7.47/1.48    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.47/1.48    inference(flattening,[],[f37])).
% 7.47/1.48  
% 7.47/1.48  fof(f95,plain,(
% 7.47/1.48    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.47/1.48    inference(cnf_transformation,[],[f38])).
% 7.47/1.48  
% 7.47/1.48  fof(f11,axiom,(
% 7.47/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.47/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.48  
% 7.47/1.48  fof(f30,plain,(
% 7.47/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.47/1.48    inference(ennf_transformation,[],[f11])).
% 7.47/1.48  
% 7.47/1.48  fof(f87,plain,(
% 7.47/1.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.47/1.48    inference(cnf_transformation,[],[f30])).
% 7.47/1.48  
% 7.47/1.48  fof(f108,plain,(
% 7.47/1.48    v1_funct_1(sK6)),
% 7.47/1.48    inference(cnf_transformation,[],[f65])).
% 7.47/1.48  
% 7.47/1.48  fof(f18,axiom,(
% 7.47/1.48    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 7.47/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.48  
% 7.47/1.48  fof(f39,plain,(
% 7.47/1.48    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 7.47/1.48    inference(ennf_transformation,[],[f18])).
% 7.47/1.48  
% 7.47/1.48  fof(f40,plain,(
% 7.47/1.48    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 7.47/1.48    inference(flattening,[],[f39])).
% 7.47/1.48  
% 7.47/1.48  fof(f96,plain,(
% 7.47/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 7.47/1.48    inference(cnf_transformation,[],[f40])).
% 7.47/1.48  
% 7.47/1.48  fof(f6,axiom,(
% 7.47/1.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.47/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.48  
% 7.47/1.48  fof(f57,plain,(
% 7.47/1.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.47/1.48    inference(nnf_transformation,[],[f6])).
% 7.47/1.48  
% 7.47/1.48  fof(f58,plain,(
% 7.47/1.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.47/1.48    inference(flattening,[],[f57])).
% 7.47/1.48  
% 7.47/1.48  fof(f76,plain,(
% 7.47/1.48    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 7.47/1.48    inference(cnf_transformation,[],[f58])).
% 7.47/1.48  
% 7.47/1.48  fof(f77,plain,(
% 7.47/1.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.47/1.48    inference(cnf_transformation,[],[f58])).
% 7.47/1.48  
% 7.47/1.48  fof(f117,plain,(
% 7.47/1.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.47/1.48    inference(equality_resolution,[],[f77])).
% 7.47/1.48  
% 7.47/1.48  fof(f113,plain,(
% 7.47/1.48    k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7)),
% 7.47/1.48    inference(cnf_transformation,[],[f65])).
% 7.47/1.48  
% 7.47/1.48  fof(f14,axiom,(
% 7.47/1.48    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 7.47/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.48  
% 7.47/1.48  fof(f33,plain,(
% 7.47/1.48    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 7.47/1.48    inference(ennf_transformation,[],[f14])).
% 7.47/1.48  
% 7.47/1.48  fof(f90,plain,(
% 7.47/1.48    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 7.47/1.48    inference(cnf_transformation,[],[f33])).
% 7.47/1.48  
% 7.47/1.48  fof(f16,axiom,(
% 7.47/1.48    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 7.47/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.48  
% 7.47/1.48  fof(f35,plain,(
% 7.47/1.48    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.47/1.48    inference(ennf_transformation,[],[f16])).
% 7.47/1.48  
% 7.47/1.48  fof(f36,plain,(
% 7.47/1.48    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.47/1.48    inference(flattening,[],[f35])).
% 7.47/1.48  
% 7.47/1.48  fof(f93,plain,(
% 7.47/1.48    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.47/1.48    inference(cnf_transformation,[],[f36])).
% 7.47/1.48  
% 7.47/1.48  cnf(c_41,negated_conjecture,
% 7.47/1.48      ( m1_subset_1(sK7,sK3) ),
% 7.47/1.48      inference(cnf_transformation,[],[f110]) ).
% 7.47/1.48  
% 7.47/1.48  cnf(c_1702,plain,
% 7.47/1.48      ( m1_subset_1(sK7,sK3) = iProver_top ),
% 7.47/1.48      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.47/1.48  
% 7.47/1.48  cnf(c_16,plain,
% 7.47/1.48      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.47/1.48      inference(cnf_transformation,[],[f79]) ).
% 7.47/1.48  
% 7.47/1.48  cnf(c_1717,plain,
% 7.47/1.48      ( m1_subset_1(X0,X1) != iProver_top
% 7.47/1.48      | r2_hidden(X0,X1) = iProver_top
% 7.47/1.48      | v1_xboole_0(X1) = iProver_top ),
% 7.47/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.47/1.48  
% 7.47/1.48  cnf(c_4159,plain,
% 7.47/1.48      ( r2_hidden(sK7,sK3) = iProver_top
% 7.47/1.48      | v1_xboole_0(sK3) = iProver_top ),
% 7.47/1.48      inference(superposition,[status(thm)],[c_1702,c_1717]) ).
% 7.47/1.48  
% 7.47/1.48  cnf(c_54,plain,
% 7.47/1.48      ( m1_subset_1(sK7,sK3) = iProver_top ),
% 7.47/1.48      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.47/1.48  
% 7.47/1.48  cnf(c_39,negated_conjecture,
% 7.47/1.48      ( k1_xboole_0 != sK3 ),
% 7.47/1.48      inference(cnf_transformation,[],[f112]) ).
% 7.47/1.48  
% 7.47/1.48  cnf(c_6,plain,
% 7.47/1.48      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 7.47/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.47/1.48  
% 7.47/1.48  cnf(c_2020,plain,
% 7.47/1.48      ( ~ v1_xboole_0(sK3) | k1_xboole_0 = sK3 ),
% 7.47/1.48      inference(instantiation,[status(thm)],[c_6]) ).
% 7.47/1.48  
% 7.47/1.48  cnf(c_2021,plain,
% 7.47/1.48      ( k1_xboole_0 = sK3 | v1_xboole_0(sK3) != iProver_top ),
% 7.47/1.48      inference(predicate_to_equality,[status(thm)],[c_2020]) ).
% 7.47/1.48  
% 7.47/1.48  cnf(c_2190,plain,
% 7.47/1.48      ( ~ m1_subset_1(X0,sK3) | r2_hidden(X0,sK3) | v1_xboole_0(sK3) ),
% 7.47/1.48      inference(instantiation,[status(thm)],[c_16]) ).
% 7.47/1.48  
% 7.47/1.48  cnf(c_2651,plain,
% 7.47/1.48      ( ~ m1_subset_1(sK7,sK3) | r2_hidden(sK7,sK3) | v1_xboole_0(sK3) ),
% 7.47/1.48      inference(instantiation,[status(thm)],[c_2190]) ).
% 7.47/1.48  
% 7.47/1.48  cnf(c_2652,plain,
% 7.47/1.48      ( m1_subset_1(sK7,sK3) != iProver_top
% 7.47/1.48      | r2_hidden(sK7,sK3) = iProver_top
% 7.47/1.48      | v1_xboole_0(sK3) = iProver_top ),
% 7.47/1.48      inference(predicate_to_equality,[status(thm)],[c_2651]) ).
% 7.47/1.48  
% 7.47/1.48  cnf(c_4533,plain,
% 7.47/1.48      ( r2_hidden(sK7,sK3) = iProver_top ),
% 7.47/1.48      inference(global_propositional_subsumption,
% 7.47/1.48                [status(thm)],
% 7.47/1.48                [c_4159,c_54,c_39,c_2021,c_2652]) ).
% 7.47/1.48  
% 7.47/1.48  cnf(c_42,negated_conjecture,
% 7.47/1.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
% 7.47/1.48      inference(cnf_transformation,[],[f109]) ).
% 7.47/1.48  
% 7.47/1.48  cnf(c_1701,plain,
% 7.47/1.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 7.47/1.48      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.47/1.48  
% 7.47/1.48  cnf(c_25,plain,
% 7.47/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.47/1.48      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.47/1.48      inference(cnf_transformation,[],[f91]) ).
% 7.47/1.48  
% 7.47/1.48  cnf(c_1711,plain,
% 7.47/1.48      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.47/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.47/1.48      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.47/1.48  
% 7.47/1.48  cnf(c_3654,plain,
% 7.47/1.48      ( k1_relset_1(sK4,sK2,sK6) = k1_relat_1(sK6) ),
% 7.47/1.48      inference(superposition,[status(thm)],[c_1701,c_1711]) ).
% 7.47/1.48  
% 7.47/1.48  cnf(c_40,negated_conjecture,
% 7.47/1.48      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
% 7.47/1.48      inference(cnf_transformation,[],[f111]) ).
% 7.47/1.48  
% 7.47/1.48  cnf(c_1703,plain,
% 7.47/1.48      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
% 7.47/1.48      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.47/1.48  
% 7.47/1.48  cnf(c_3735,plain,
% 7.47/1.48      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relat_1(sK6)) = iProver_top ),
% 7.47/1.48      inference(demodulation,[status(thm)],[c_3654,c_1703]) ).
% 7.47/1.48  
% 7.47/1.48  cnf(c_44,negated_conjecture,
% 7.47/1.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 7.47/1.48      inference(cnf_transformation,[],[f107]) ).
% 7.47/1.48  
% 7.47/1.48  cnf(c_1699,plain,
% 7.47/1.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 7.47/1.48      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.47/1.48  
% 7.47/1.48  cnf(c_33,plain,
% 7.47/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.47/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.47/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 7.47/1.48      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 7.47/1.48      | ~ v1_funct_1(X0)
% 7.47/1.48      | k1_xboole_0 = X2 ),
% 7.47/1.48      inference(cnf_transformation,[],[f102]) ).
% 7.47/1.48  
% 7.47/1.48  cnf(c_1706,plain,
% 7.47/1.48      ( k1_xboole_0 = X0
% 7.47/1.48      | v1_funct_2(X1,X2,X0) != iProver_top
% 7.47/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 7.47/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
% 7.47/1.48      | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
% 7.47/1.48      | v1_funct_1(X1) != iProver_top ),
% 7.47/1.48      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.47/1.48  
% 7.47/1.48  cnf(c_4063,plain,
% 7.47/1.48      ( sK4 = k1_xboole_0
% 7.47/1.48      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 7.47/1.48      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 7.47/1.48      | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
% 7.47/1.48      | v1_funct_1(sK5) != iProver_top ),
% 7.47/1.48      inference(superposition,[status(thm)],[c_1699,c_1706]) ).
% 7.47/1.48  
% 7.47/1.48  cnf(c_47,negated_conjecture,
% 7.47/1.48      ( ~ v1_xboole_0(sK4) ),
% 7.47/1.48      inference(cnf_transformation,[],[f104]) ).
% 7.47/1.48  
% 7.47/1.48  cnf(c_46,negated_conjecture,
% 7.47/1.48      ( v1_funct_1(sK5) ),
% 7.47/1.48      inference(cnf_transformation,[],[f105]) ).
% 7.47/1.48  
% 7.47/1.48  cnf(c_49,plain,
% 7.47/1.48      ( v1_funct_1(sK5) = iProver_top ),
% 7.47/1.48      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 7.47/1.48  
% 7.47/1.48  cnf(c_45,negated_conjecture,
% 7.47/1.48      ( v1_funct_2(sK5,sK3,sK4) ),
% 7.47/1.48      inference(cnf_transformation,[],[f106]) ).
% 7.47/1.48  
% 7.47/1.48  cnf(c_50,plain,
% 7.47/1.48      ( v1_funct_2(sK5,sK3,sK4) = iProver_top ),
% 7.47/1.48      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_5,plain,
% 7.47/1.49      ( v1_xboole_0(k1_xboole_0) ),
% 7.47/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_876,plain,
% 7.47/1.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 7.47/1.49      theory(equality) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2036,plain,
% 7.47/1.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK4) | sK4 != X0 ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_876]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2038,plain,
% 7.47/1.49      ( v1_xboole_0(sK4)
% 7.47/1.49      | ~ v1_xboole_0(k1_xboole_0)
% 7.47/1.49      | sK4 != k1_xboole_0 ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_2036]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_4666,plain,
% 7.47/1.49      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
% 7.47/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top ),
% 7.47/1.49      inference(global_propositional_subsumption,
% 7.47/1.49                [status(thm)],
% 7.47/1.49                [c_4063,c_47,c_49,c_50,c_5,c_2038]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_4667,plain,
% 7.47/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 7.47/1.49      | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top ),
% 7.47/1.49      inference(renaming,[status(thm)],[c_4666]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_4675,plain,
% 7.47/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK6)))) = iProver_top ),
% 7.47/1.49      inference(superposition,[status(thm)],[c_3735,c_4667]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_31,plain,
% 7.47/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.47/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.47/1.49      | ~ r2_hidden(X3,X1)
% 7.47/1.49      | r2_hidden(k1_funct_1(X0,X3),X2)
% 7.47/1.49      | ~ v1_funct_1(X0)
% 7.47/1.49      | k1_xboole_0 = X2 ),
% 7.47/1.49      inference(cnf_transformation,[],[f97]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_1708,plain,
% 7.47/1.49      ( k1_xboole_0 = X0
% 7.47/1.49      | v1_funct_2(X1,X2,X0) != iProver_top
% 7.47/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 7.47/1.49      | r2_hidden(X3,X2) != iProver_top
% 7.47/1.49      | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
% 7.47/1.49      | v1_funct_1(X1) != iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_5441,plain,
% 7.47/1.49      ( k1_relat_1(sK6) = k1_xboole_0
% 7.47/1.49      | v1_funct_2(sK5,sK3,k1_relat_1(sK6)) != iProver_top
% 7.47/1.49      | r2_hidden(X0,sK3) != iProver_top
% 7.47/1.49      | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top
% 7.47/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.47/1.49      inference(superposition,[status(thm)],[c_4675,c_1708]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_35,plain,
% 7.47/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.47/1.49      | v1_funct_2(X0,X1,X3)
% 7.47/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.47/1.49      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 7.47/1.49      | ~ v1_funct_1(X0)
% 7.47/1.49      | k1_xboole_0 = X2 ),
% 7.47/1.49      inference(cnf_transformation,[],[f100]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_1704,plain,
% 7.47/1.49      ( k1_xboole_0 = X0
% 7.47/1.49      | v1_funct_2(X1,X2,X0) != iProver_top
% 7.47/1.49      | v1_funct_2(X1,X2,X3) = iProver_top
% 7.47/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 7.47/1.49      | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
% 7.47/1.49      | v1_funct_1(X1) != iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_3312,plain,
% 7.47/1.49      ( sK4 = k1_xboole_0
% 7.47/1.49      | v1_funct_2(sK5,sK3,X0) = iProver_top
% 7.47/1.49      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 7.47/1.49      | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
% 7.47/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.47/1.49      inference(superposition,[status(thm)],[c_1699,c_1704]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_3891,plain,
% 7.47/1.49      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
% 7.47/1.49      | v1_funct_2(sK5,sK3,X0) = iProver_top ),
% 7.47/1.49      inference(global_propositional_subsumption,
% 7.47/1.49                [status(thm)],
% 7.47/1.49                [c_3312,c_47,c_49,c_50,c_5,c_2038]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_3892,plain,
% 7.47/1.49      ( v1_funct_2(sK5,sK3,X0) = iProver_top
% 7.47/1.49      | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top ),
% 7.47/1.49      inference(renaming,[status(thm)],[c_3891]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_3900,plain,
% 7.47/1.49      ( v1_funct_2(sK5,sK3,k1_relat_1(sK6)) = iProver_top ),
% 7.47/1.49      inference(superposition,[status(thm)],[c_3735,c_3892]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_30458,plain,
% 7.47/1.49      ( r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top
% 7.47/1.49      | r2_hidden(X0,sK3) != iProver_top
% 7.47/1.49      | k1_relat_1(sK6) = k1_xboole_0 ),
% 7.47/1.49      inference(global_propositional_subsumption,
% 7.47/1.49                [status(thm)],
% 7.47/1.49                [c_5441,c_49,c_3900]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_30459,plain,
% 7.47/1.49      ( k1_relat_1(sK6) = k1_xboole_0
% 7.47/1.49      | r2_hidden(X0,sK3) != iProver_top
% 7.47/1.49      | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top ),
% 7.47/1.49      inference(renaming,[status(thm)],[c_30458]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_22,plain,
% 7.47/1.49      ( v5_relat_1(X0,X1)
% 7.47/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.47/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_29,plain,
% 7.47/1.49      ( ~ v5_relat_1(X0,X1)
% 7.47/1.49      | ~ r2_hidden(X2,k1_relat_1(X0))
% 7.47/1.49      | ~ v1_funct_1(X0)
% 7.47/1.49      | ~ v1_relat_1(X0)
% 7.47/1.49      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 7.47/1.49      inference(cnf_transformation,[],[f95]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_536,plain,
% 7.47/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.47/1.49      | ~ r2_hidden(X3,k1_relat_1(X0))
% 7.47/1.49      | ~ v1_funct_1(X0)
% 7.47/1.49      | ~ v1_relat_1(X0)
% 7.47/1.49      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 7.47/1.49      inference(resolution,[status(thm)],[c_22,c_29]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_21,plain,
% 7.47/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.47/1.49      | v1_relat_1(X0) ),
% 7.47/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_540,plain,
% 7.47/1.49      ( ~ v1_funct_1(X0)
% 7.47/1.49      | ~ r2_hidden(X3,k1_relat_1(X0))
% 7.47/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.47/1.49      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 7.47/1.49      inference(global_propositional_subsumption,
% 7.47/1.49                [status(thm)],
% 7.47/1.49                [c_536,c_21]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_541,plain,
% 7.47/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.47/1.49      | ~ r2_hidden(X3,k1_relat_1(X0))
% 7.47/1.49      | ~ v1_funct_1(X0)
% 7.47/1.49      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 7.47/1.49      inference(renaming,[status(thm)],[c_540]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_1693,plain,
% 7.47/1.49      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 7.47/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
% 7.47/1.49      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 7.47/1.49      | v1_funct_1(X1) != iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_541]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2371,plain,
% 7.47/1.49      ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
% 7.47/1.49      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 7.47/1.49      | v1_funct_1(sK6) != iProver_top ),
% 7.47/1.49      inference(superposition,[status(thm)],[c_1701,c_1693]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_43,negated_conjecture,
% 7.47/1.49      ( v1_funct_1(sK6) ),
% 7.47/1.49      inference(cnf_transformation,[],[f108]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_52,plain,
% 7.47/1.49      ( v1_funct_1(sK6) = iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2570,plain,
% 7.47/1.49      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 7.47/1.49      | k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0) ),
% 7.47/1.49      inference(global_propositional_subsumption,
% 7.47/1.49                [status(thm)],
% 7.47/1.49                [c_2371,c_52]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2571,plain,
% 7.47/1.49      ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
% 7.47/1.49      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 7.47/1.49      inference(renaming,[status(thm)],[c_2570]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_30474,plain,
% 7.47/1.49      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 7.47/1.49      | k1_relat_1(sK6) = k1_xboole_0
% 7.47/1.49      | r2_hidden(X0,sK3) != iProver_top ),
% 7.47/1.49      inference(superposition,[status(thm)],[c_30459,c_2571]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_31215,plain,
% 7.47/1.49      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(sK6,k1_funct_1(sK5,sK7))
% 7.47/1.49      | k1_relat_1(sK6) = k1_xboole_0 ),
% 7.47/1.49      inference(superposition,[status(thm)],[c_4533,c_30474]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_30,plain,
% 7.47/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.47/1.49      | ~ m1_subset_1(X3,X1)
% 7.47/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 7.47/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.47/1.49      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
% 7.47/1.49      | ~ v1_funct_1(X4)
% 7.47/1.49      | ~ v1_funct_1(X0)
% 7.47/1.49      | v1_xboole_0(X2)
% 7.47/1.49      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 7.47/1.49      | k1_xboole_0 = X1 ),
% 7.47/1.49      inference(cnf_transformation,[],[f96]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_1709,plain,
% 7.47/1.49      ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
% 7.47/1.49      | k1_xboole_0 = X0
% 7.47/1.49      | v1_funct_2(X3,X0,X1) != iProver_top
% 7.47/1.49      | m1_subset_1(X5,X0) != iProver_top
% 7.47/1.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.47/1.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.47/1.49      | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
% 7.47/1.49      | v1_funct_1(X3) != iProver_top
% 7.47/1.49      | v1_funct_1(X4) != iProver_top
% 7.47/1.49      | v1_xboole_0(X1) = iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_5905,plain,
% 7.47/1.49      ( k1_funct_1(k8_funct_2(X0,sK4,sK2,X1,sK6),X2) = k1_funct_1(sK6,k1_funct_1(X1,X2))
% 7.47/1.49      | k1_xboole_0 = X0
% 7.47/1.49      | v1_funct_2(X1,X0,sK4) != iProver_top
% 7.47/1.49      | m1_subset_1(X2,X0) != iProver_top
% 7.47/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) != iProver_top
% 7.47/1.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 7.47/1.49      | r1_tarski(k2_relset_1(X0,sK4,X1),k1_relat_1(sK6)) != iProver_top
% 7.47/1.49      | v1_funct_1(X1) != iProver_top
% 7.47/1.49      | v1_funct_1(sK6) != iProver_top
% 7.47/1.49      | v1_xboole_0(sK4) = iProver_top ),
% 7.47/1.49      inference(superposition,[status(thm)],[c_3654,c_1709]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_48,plain,
% 7.47/1.49      ( v1_xboole_0(sK4) != iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_53,plain,
% 7.47/1.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_12197,plain,
% 7.47/1.49      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) != iProver_top
% 7.47/1.49      | m1_subset_1(X2,X0) != iProver_top
% 7.47/1.49      | v1_funct_2(X1,X0,sK4) != iProver_top
% 7.47/1.49      | k1_xboole_0 = X0
% 7.47/1.49      | k1_funct_1(k8_funct_2(X0,sK4,sK2,X1,sK6),X2) = k1_funct_1(sK6,k1_funct_1(X1,X2))
% 7.47/1.49      | r1_tarski(k2_relset_1(X0,sK4,X1),k1_relat_1(sK6)) != iProver_top
% 7.47/1.49      | v1_funct_1(X1) != iProver_top ),
% 7.47/1.49      inference(global_propositional_subsumption,
% 7.47/1.49                [status(thm)],
% 7.47/1.49                [c_5905,c_48,c_52,c_53]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_12198,plain,
% 7.47/1.49      ( k1_funct_1(k8_funct_2(X0,sK4,sK2,X1,sK6),X2) = k1_funct_1(sK6,k1_funct_1(X1,X2))
% 7.47/1.49      | k1_xboole_0 = X0
% 7.47/1.49      | v1_funct_2(X1,X0,sK4) != iProver_top
% 7.47/1.49      | m1_subset_1(X2,X0) != iProver_top
% 7.47/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) != iProver_top
% 7.47/1.49      | r1_tarski(k2_relset_1(X0,sK4,X1),k1_relat_1(sK6)) != iProver_top
% 7.47/1.49      | v1_funct_1(X1) != iProver_top ),
% 7.47/1.49      inference(renaming,[status(thm)],[c_12197]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_12209,plain,
% 7.47/1.49      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 7.47/1.49      | sK3 = k1_xboole_0
% 7.47/1.49      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 7.47/1.49      | m1_subset_1(X0,sK3) != iProver_top
% 7.47/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 7.47/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.47/1.49      inference(superposition,[status(thm)],[c_3735,c_12198]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_51,plain,
% 7.47/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_12,plain,
% 7.47/1.49      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 7.47/1.49      | k1_xboole_0 = X0
% 7.47/1.49      | k1_xboole_0 = X1 ),
% 7.47/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_107,plain,
% 7.47/1.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.47/1.49      | k1_xboole_0 = k1_xboole_0 ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_12]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_11,plain,
% 7.47/1.49      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.47/1.49      inference(cnf_transformation,[],[f117]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_108,plain,
% 7.47/1.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_11]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_875,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2076,plain,
% 7.47/1.49      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_875]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2077,plain,
% 7.47/1.49      ( sK3 != k1_xboole_0
% 7.47/1.49      | k1_xboole_0 = sK3
% 7.47/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_2076]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_12241,plain,
% 7.47/1.49      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 7.47/1.49      | m1_subset_1(X0,sK3) != iProver_top ),
% 7.47/1.49      inference(global_propositional_subsumption,
% 7.47/1.49                [status(thm)],
% 7.47/1.49                [c_12209,c_49,c_50,c_51,c_39,c_107,c_108,c_2077]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_12250,plain,
% 7.47/1.49      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 7.47/1.49      inference(superposition,[status(thm)],[c_1702,c_12241]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_38,negated_conjecture,
% 7.47/1.49      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) ),
% 7.47/1.49      inference(cnf_transformation,[],[f113]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_12379,plain,
% 7.47/1.49      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 7.47/1.49      inference(demodulation,[status(thm)],[c_12250,c_38]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_31415,plain,
% 7.47/1.49      ( k1_relat_1(sK6) = k1_xboole_0 ),
% 7.47/1.49      inference(global_propositional_subsumption,
% 7.47/1.49                [status(thm)],
% 7.47/1.49                [c_31215,c_12379]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_24,plain,
% 7.47/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.47/1.49      | ~ v1_xboole_0(X2)
% 7.47/1.49      | v1_xboole_0(X0) ),
% 7.47/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_1712,plain,
% 7.47/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.47/1.49      | v1_xboole_0(X2) != iProver_top
% 7.47/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_5440,plain,
% 7.47/1.49      ( v1_xboole_0(k1_relat_1(sK6)) != iProver_top
% 7.47/1.49      | v1_xboole_0(sK5) = iProver_top ),
% 7.47/1.49      inference(superposition,[status(thm)],[c_4675,c_1712]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_27,plain,
% 7.47/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.47/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.47/1.49      | ~ v1_funct_1(X0)
% 7.47/1.49      | ~ v1_xboole_0(X0)
% 7.47/1.49      | v1_xboole_0(X1)
% 7.47/1.49      | v1_xboole_0(X2) ),
% 7.47/1.49      inference(cnf_transformation,[],[f93]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2189,plain,
% 7.47/1.49      ( ~ v1_funct_2(X0,sK3,X1)
% 7.47/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
% 7.47/1.49      | ~ v1_funct_1(X0)
% 7.47/1.49      | ~ v1_xboole_0(X0)
% 7.47/1.49      | v1_xboole_0(X1)
% 7.47/1.49      | v1_xboole_0(sK3) ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_27]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2846,plain,
% 7.47/1.49      ( ~ v1_funct_2(X0,sK3,sK4)
% 7.47/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 7.47/1.49      | ~ v1_funct_1(X0)
% 7.47/1.49      | ~ v1_xboole_0(X0)
% 7.47/1.49      | v1_xboole_0(sK4)
% 7.47/1.49      | v1_xboole_0(sK3) ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_2189]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2930,plain,
% 7.47/1.49      ( ~ v1_funct_2(sK5,sK3,sK4)
% 7.47/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 7.47/1.49      | ~ v1_funct_1(sK5)
% 7.47/1.49      | v1_xboole_0(sK4)
% 7.47/1.49      | v1_xboole_0(sK3)
% 7.47/1.49      | ~ v1_xboole_0(sK5) ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_2846]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2931,plain,
% 7.47/1.49      ( v1_funct_2(sK5,sK3,sK4) != iProver_top
% 7.47/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 7.47/1.49      | v1_funct_1(sK5) != iProver_top
% 7.47/1.49      | v1_xboole_0(sK4) = iProver_top
% 7.47/1.49      | v1_xboole_0(sK3) = iProver_top
% 7.47/1.49      | v1_xboole_0(sK5) != iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_2930]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_10402,plain,
% 7.47/1.49      ( v1_xboole_0(k1_relat_1(sK6)) != iProver_top ),
% 7.47/1.49      inference(global_propositional_subsumption,
% 7.47/1.49                [status(thm)],
% 7.47/1.49                [c_5440,c_48,c_49,c_50,c_51,c_39,c_2021,c_2931]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_31442,plain,
% 7.47/1.49      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.47/1.49      inference(demodulation,[status(thm)],[c_31415,c_10402]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_119,plain,
% 7.47/1.49      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.47/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(contradiction,plain,
% 7.47/1.49      ( $false ),
% 7.47/1.49      inference(minisat,[status(thm)],[c_31442,c_119]) ).
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.47/1.49  
% 7.47/1.49  ------                               Statistics
% 7.47/1.49  
% 7.47/1.49  ------ General
% 7.47/1.49  
% 7.47/1.49  abstr_ref_over_cycles:                  0
% 7.47/1.49  abstr_ref_under_cycles:                 0
% 7.47/1.49  gc_basic_clause_elim:                   0
% 7.47/1.49  forced_gc_time:                         0
% 7.47/1.49  parsing_time:                           0.01
% 7.47/1.49  unif_index_cands_time:                  0.
% 7.47/1.49  unif_index_add_time:                    0.
% 7.47/1.49  orderings_time:                         0.
% 7.47/1.49  out_proof_time:                         0.014
% 7.47/1.49  total_time:                             0.951
% 7.47/1.49  num_of_symbols:                         56
% 7.47/1.49  num_of_terms:                           29948
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing
% 7.47/1.49  
% 7.47/1.49  num_of_splits:                          0
% 7.47/1.49  num_of_split_atoms:                     0
% 7.47/1.49  num_of_reused_defs:                     0
% 7.47/1.49  num_eq_ax_congr_red:                    15
% 7.47/1.49  num_of_sem_filtered_clauses:            1
% 7.47/1.49  num_of_subtypes:                        0
% 7.47/1.49  monotx_restored_types:                  0
% 7.47/1.49  sat_num_of_epr_types:                   0
% 7.47/1.49  sat_num_of_non_cyclic_types:            0
% 7.47/1.49  sat_guarded_non_collapsed_types:        0
% 7.47/1.49  num_pure_diseq_elim:                    0
% 7.47/1.49  simp_replaced_by:                       0
% 7.47/1.49  res_preprocessed:                       197
% 7.47/1.49  prep_upred:                             0
% 7.47/1.49  prep_unflattend:                        0
% 7.47/1.49  smt_new_axioms:                         0
% 7.47/1.49  pred_elim_cands:                        6
% 7.47/1.49  pred_elim:                              2
% 7.47/1.49  pred_elim_cl:                           2
% 7.47/1.49  pred_elim_cycles:                       5
% 7.47/1.49  merged_defs:                            8
% 7.47/1.49  merged_defs_ncl:                        0
% 7.47/1.49  bin_hyper_res:                          9
% 7.47/1.49  prep_cycles:                            4
% 7.47/1.49  pred_elim_time:                         0.002
% 7.47/1.49  splitting_time:                         0.
% 7.47/1.49  sem_filter_time:                        0.
% 7.47/1.49  monotx_time:                            0.
% 7.47/1.49  subtype_inf_time:                       0.
% 7.47/1.49  
% 7.47/1.49  ------ Problem properties
% 7.47/1.49  
% 7.47/1.49  clauses:                                41
% 7.47/1.49  conjectures:                            10
% 7.47/1.49  epr:                                    17
% 7.47/1.49  horn:                                   32
% 7.47/1.49  ground:                                 11
% 7.47/1.49  unary:                                  14
% 7.47/1.49  binary:                                 9
% 7.47/1.49  lits:                                   110
% 7.47/1.49  lits_eq:                                16
% 7.47/1.49  fd_pure:                                0
% 7.47/1.49  fd_pseudo:                              0
% 7.47/1.49  fd_cond:                                6
% 7.47/1.49  fd_pseudo_cond:                         1
% 7.47/1.49  ac_symbols:                             0
% 7.47/1.49  
% 7.47/1.49  ------ Propositional Solver
% 7.47/1.49  
% 7.47/1.49  prop_solver_calls:                      29
% 7.47/1.49  prop_fast_solver_calls:                 2119
% 7.47/1.49  smt_solver_calls:                       0
% 7.47/1.49  smt_fast_solver_calls:                  0
% 7.47/1.49  prop_num_of_clauses:                    10808
% 7.47/1.49  prop_preprocess_simplified:             20309
% 7.47/1.49  prop_fo_subsumed:                       64
% 7.47/1.49  prop_solver_time:                       0.
% 7.47/1.49  smt_solver_time:                        0.
% 7.47/1.49  smt_fast_solver_time:                   0.
% 7.47/1.49  prop_fast_solver_time:                  0.
% 7.47/1.49  prop_unsat_core_time:                   0.001
% 7.47/1.49  
% 7.47/1.49  ------ QBF
% 7.47/1.49  
% 7.47/1.49  qbf_q_res:                              0
% 7.47/1.49  qbf_num_tautologies:                    0
% 7.47/1.49  qbf_prep_cycles:                        0
% 7.47/1.49  
% 7.47/1.49  ------ BMC1
% 7.47/1.49  
% 7.47/1.49  bmc1_current_bound:                     -1
% 7.47/1.49  bmc1_last_solved_bound:                 -1
% 7.47/1.49  bmc1_unsat_core_size:                   -1
% 7.47/1.49  bmc1_unsat_core_parents_size:           -1
% 7.47/1.49  bmc1_merge_next_fun:                    0
% 7.47/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.47/1.49  
% 7.47/1.49  ------ Instantiation
% 7.47/1.49  
% 7.47/1.49  inst_num_of_clauses:                    2833
% 7.47/1.49  inst_num_in_passive:                    695
% 7.47/1.49  inst_num_in_active:                     1214
% 7.47/1.49  inst_num_in_unprocessed:                924
% 7.47/1.49  inst_num_of_loops:                      1500
% 7.47/1.49  inst_num_of_learning_restarts:          0
% 7.47/1.49  inst_num_moves_active_passive:          283
% 7.47/1.49  inst_lit_activity:                      0
% 7.47/1.49  inst_lit_activity_moves:                0
% 7.47/1.49  inst_num_tautologies:                   0
% 7.47/1.49  inst_num_prop_implied:                  0
% 7.47/1.49  inst_num_existing_simplified:           0
% 7.47/1.49  inst_num_eq_res_simplified:             0
% 7.47/1.49  inst_num_child_elim:                    0
% 7.47/1.49  inst_num_of_dismatching_blockings:      1306
% 7.47/1.49  inst_num_of_non_proper_insts:           2935
% 7.47/1.49  inst_num_of_duplicates:                 0
% 7.47/1.49  inst_inst_num_from_inst_to_res:         0
% 7.47/1.49  inst_dismatching_checking_time:         0.
% 7.47/1.49  
% 7.47/1.49  ------ Resolution
% 7.47/1.49  
% 7.47/1.49  res_num_of_clauses:                     0
% 7.47/1.49  res_num_in_passive:                     0
% 7.47/1.49  res_num_in_active:                      0
% 7.47/1.49  res_num_of_loops:                       201
% 7.47/1.49  res_forward_subset_subsumed:            341
% 7.47/1.49  res_backward_subset_subsumed:           0
% 7.47/1.49  res_forward_subsumed:                   0
% 7.47/1.49  res_backward_subsumed:                  0
% 7.47/1.49  res_forward_subsumption_resolution:     0
% 7.47/1.49  res_backward_subsumption_resolution:    0
% 7.47/1.49  res_clause_to_clause_subsumption:       5641
% 7.47/1.49  res_orphan_elimination:                 0
% 7.47/1.49  res_tautology_del:                      132
% 7.47/1.49  res_num_eq_res_simplified:              0
% 7.47/1.49  res_num_sel_changes:                    0
% 7.47/1.49  res_moves_from_active_to_pass:          0
% 7.47/1.49  
% 7.47/1.49  ------ Superposition
% 7.47/1.49  
% 7.47/1.49  sup_time_total:                         0.
% 7.47/1.49  sup_time_generating:                    0.
% 7.47/1.49  sup_time_sim_full:                      0.
% 7.47/1.49  sup_time_sim_immed:                     0.
% 7.47/1.49  
% 7.47/1.49  sup_num_of_clauses:                     879
% 7.47/1.49  sup_num_in_active:                      256
% 7.47/1.49  sup_num_in_passive:                     623
% 7.47/1.49  sup_num_of_loops:                       298
% 7.47/1.49  sup_fw_superposition:                   681
% 7.47/1.49  sup_bw_superposition:                   544
% 7.47/1.49  sup_immediate_simplified:               168
% 7.47/1.49  sup_given_eliminated:                   1
% 7.47/1.49  comparisons_done:                       0
% 7.47/1.49  comparisons_avoided:                    55
% 7.47/1.49  
% 7.47/1.49  ------ Simplifications
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  sim_fw_subset_subsumed:                 116
% 7.47/1.49  sim_bw_subset_subsumed:                 30
% 7.47/1.49  sim_fw_subsumed:                        39
% 7.47/1.49  sim_bw_subsumed:                        3
% 7.47/1.49  sim_fw_subsumption_res:                 1
% 7.47/1.49  sim_bw_subsumption_res:                 0
% 7.47/1.49  sim_tautology_del:                      31
% 7.47/1.49  sim_eq_tautology_del:                   18
% 7.47/1.49  sim_eq_res_simp:                        0
% 7.47/1.49  sim_fw_demodulated:                     13
% 7.47/1.49  sim_bw_demodulated:                     37
% 7.47/1.49  sim_light_normalised:                   4
% 7.47/1.49  sim_joinable_taut:                      0
% 7.47/1.49  sim_joinable_simp:                      0
% 7.47/1.49  sim_ac_normalised:                      0
% 7.47/1.49  sim_smt_subsumption:                    0
% 7.47/1.49  
%------------------------------------------------------------------------------
