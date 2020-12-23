%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:51 EST 2020

% Result     : Theorem 6.97s
% Output     : CNFRefutation 6.97s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 502 expanded)
%              Number of clauses        :  105 ( 144 expanded)
%              Number of leaves         :   25 ( 164 expanded)
%              Depth                    :   19
%              Number of atoms          :  599 (3577 expanded)
%              Number of equality atoms :  250 ( 990 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
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
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
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
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f36])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK7) != k7_partfun1(X0,X4,k1_funct_1(X3,sK7))
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK7,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
              & k1_xboole_0 != X1
              & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK6),X5) != k7_partfun1(X0,sK6,k1_funct_1(X3,X5))
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK6))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
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
                ( k1_funct_1(k8_funct_2(X1,X2,X0,sK5,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK5,X5))
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK5),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK5,X1,X2)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
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
                  ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,X3,X4),X5) != k7_partfun1(sK2,X4,k1_funct_1(X3,X5))
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

fof(f54,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7))
    & k1_xboole_0 != sK3
    & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))
    & m1_subset_1(sK7,sK3)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f37,f53,f52,f51,f50])).

fof(f88,plain,(
    m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f21])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f90,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f54])).

fof(f87,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f54])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f85,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f54])).

fof(f89,plain,(
    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f14,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f56,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f82,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f84,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f83,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f86,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f54])).

fof(f16,axiom,(
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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f91,plain,(
    k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3317,plain,
    ( m1_subset_1(sK7,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3333,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3331,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5100,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | r1_tarski(k1_tarski(X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3333,c_3331])).

cnf(c_6,plain,
    ( ~ r1_tarski(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3335,plain,
    ( r1_tarski(k1_tarski(X0),X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_19545,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | r2_hidden(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5100,c_3335])).

cnf(c_21998,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK7,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3317,c_19545])).

cnf(c_43,plain,
    ( m1_subset_1(sK7,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3660,plain,
    ( ~ m1_subset_1(X0,sK3)
    | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3863,plain,
    ( m1_subset_1(k1_tarski(sK7),k1_zfmisc_1(sK3))
    | ~ m1_subset_1(sK7,sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_3660])).

cnf(c_3864,plain,
    ( k1_xboole_0 = sK3
    | m1_subset_1(k1_tarski(sK7),k1_zfmisc_1(sK3)) = iProver_top
    | m1_subset_1(sK7,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3863])).

cnf(c_3610,plain,
    ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
    | r1_tarski(k1_tarski(X0),X1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_4027,plain,
    ( ~ m1_subset_1(k1_tarski(sK7),k1_zfmisc_1(sK3))
    | r1_tarski(k1_tarski(sK7),sK3) ),
    inference(instantiation,[status(thm)],[c_3610])).

cnf(c_4028,plain,
    ( m1_subset_1(k1_tarski(sK7),k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(k1_tarski(sK7),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4027])).

cnf(c_4339,plain,
    ( ~ r1_tarski(k1_tarski(sK7),sK3)
    | r2_hidden(sK7,sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4340,plain,
    ( r1_tarski(k1_tarski(sK7),sK3) != iProver_top
    | r2_hidden(sK7,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4339])).

cnf(c_22057,plain,
    ( r2_hidden(sK7,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21998,c_43,c_28,c_3864,c_4028,c_4340])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_3316,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3326,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5014,plain,
    ( k2_relset_1(sK4,sK2,sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_3316,c_3326])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3328,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5836,plain,
    ( m1_subset_1(k2_relat_1(sK6),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5014,c_3328])).

cnf(c_42,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6438,plain,
    ( m1_subset_1(k2_relat_1(sK6),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5836,c_42])).

cnf(c_6443,plain,
    ( r1_tarski(k2_relat_1(sK6),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6438,c_3331])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3330,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3314,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_5015,plain,
    ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_3314,c_3326])).

cnf(c_29,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3318,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5234,plain,
    ( r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5015,c_3318])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3327,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5083,plain,
    ( k1_relset_1(sK4,sK2,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_3316,c_3327])).

cnf(c_5437,plain,
    ( r1_tarski(k2_relat_1(sK5),k1_relat_1(sK6)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5234,c_5083])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3337,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5990,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5437,c_3337])).

cnf(c_7794,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3330,c_5990])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3320,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4911,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | sK4 = k1_xboole_0
    | v1_funct_2(sK5,sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3314,c_3320])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_36,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_556,plain,
    ( r2_hidden(sK0(X0),X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_36])).

cnf(c_557,plain,
    ( r2_hidden(sK0(sK4),sK4) ),
    inference(unflattening,[status(thm)],[c_556])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_800,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_34])).

cnf(c_801,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_800])).

cnf(c_803,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_801,c_33])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | k2_xboole_0(k1_tarski(X0),X1) = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3776,plain,
    ( ~ r2_hidden(sK0(sK4),sK4)
    | k2_xboole_0(k1_tarski(sK0(sK4)),sK4) = sK4 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2476,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3675,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) != X2
    | k2_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    | k1_xboole_0 != X2 ),
    inference(instantiation,[status(thm)],[c_2476])).

cnf(c_4255,plain,
    ( k2_xboole_0(k1_tarski(sK0(sK4)),sK4) != sK4
    | k2_xboole_0(k1_tarski(sK0(sK4)),sK4) = k1_xboole_0
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_3675])).

cnf(c_8,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_4460,plain,
    ( k2_xboole_0(k1_tarski(sK0(sK4)),sK4) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_5669,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4911,c_557,c_803,c_3776,c_4255,c_4460])).

cnf(c_5084,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_3314,c_3327])).

cnf(c_5672,plain,
    ( k1_relat_1(sK5) = sK3 ),
    inference(demodulation,[status(thm)],[c_5669,c_5084])).

cnf(c_7799,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7794,c_5672])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_38,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_40,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3621,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3622,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3621])).

cnf(c_9127,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7799,c_38,c_40,c_3622])).

cnf(c_12,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_25,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_470,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(resolution,[status(thm)],[c_12,c_25])).

cnf(c_3310,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | r1_tarski(k2_relat_1(X1),X0) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_470])).

cnf(c_9137,plain,
    ( k7_partfun1(X0,sK6,k1_funct_1(sK5,X1)) = k1_funct_1(sK6,k1_funct_1(sK5,X1))
    | r1_tarski(k2_relat_1(sK6),X0) != iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_9127,c_3310])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_41,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3618,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3619,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3618])).

cnf(c_13815,plain,
    ( k7_partfun1(X0,sK6,k1_funct_1(sK5,X1)) = k1_funct_1(sK6,k1_funct_1(sK5,X1))
    | r1_tarski(k2_relat_1(sK6),X0) != iProver_top
    | r2_hidden(X1,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9137,c_41,c_42,c_3619])).

cnf(c_13827,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6443,c_13815])).

cnf(c_22064,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_22057,c_13827])).

cnf(c_26,plain,
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
    inference(cnf_transformation,[],[f81])).

cnf(c_3319,plain,
    ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
    | k1_xboole_0 = X0
    | v1_funct_2(X3,X0,X1) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4187,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | sK3 = k1_xboole_0
    | v1_funct_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(X0,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3318,c_3319])).

cnf(c_37,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_39,plain,
    ( v1_funct_2(sK5,sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2475,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2506,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2475])).

cnf(c_3679,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_2476])).

cnf(c_3680,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3679])).

cnf(c_4627,plain,
    ( m1_subset_1(X0,sK3) != iProver_top
    | k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4187,c_37,c_38,c_39,c_40,c_41,c_42,c_28,c_2506,c_3680])).

cnf(c_4628,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_4627])).

cnf(c_4635,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_3317,c_4628])).

cnf(c_27,negated_conjecture,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_4637,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(demodulation,[status(thm)],[c_4635,c_27])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22064,c_4637])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:18:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 6.97/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.97/1.51  
% 6.97/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.97/1.51  
% 6.97/1.51  ------  iProver source info
% 6.97/1.51  
% 6.97/1.51  git: date: 2020-06-30 10:37:57 +0100
% 6.97/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.97/1.51  git: non_committed_changes: false
% 6.97/1.51  git: last_make_outside_of_git: false
% 6.97/1.51  
% 6.97/1.51  ------ 
% 6.97/1.51  ------ Parsing...
% 6.97/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.97/1.51  
% 6.97/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 6.97/1.51  
% 6.97/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.97/1.51  
% 6.97/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.97/1.51  ------ Proving...
% 6.97/1.51  ------ Problem Properties 
% 6.97/1.51  
% 6.97/1.51  
% 6.97/1.51  clauses                                 35
% 6.97/1.51  conjectures                             10
% 6.97/1.51  EPR                                     8
% 6.97/1.51  Horn                                    27
% 6.97/1.51  unary                                   11
% 6.97/1.51  binary                                  13
% 6.97/1.51  lits                                    83
% 6.97/1.51  lits eq                                 19
% 6.97/1.51  fd_pure                                 0
% 6.97/1.51  fd_pseudo                               0
% 6.97/1.51  fd_cond                                 5
% 6.97/1.51  fd_pseudo_cond                          0
% 6.97/1.51  AC symbols                              0
% 6.97/1.51  
% 6.97/1.51  ------ Input Options Time Limit: Unbounded
% 6.97/1.51  
% 6.97/1.51  
% 6.97/1.51  ------ 
% 6.97/1.51  Current options:
% 6.97/1.51  ------ 
% 6.97/1.51  
% 6.97/1.51  
% 6.97/1.51  
% 6.97/1.51  
% 6.97/1.51  ------ Proving...
% 6.97/1.51  
% 6.97/1.51  
% 6.97/1.51  % SZS status Theorem for theBenchmark.p
% 6.97/1.51  
% 6.97/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 6.97/1.51  
% 6.97/1.51  fof(f17,conjecture,(
% 6.97/1.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 6.97/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.97/1.51  
% 6.97/1.51  fof(f18,negated_conjecture,(
% 6.97/1.51    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 6.97/1.51    inference(negated_conjecture,[],[f17])).
% 6.97/1.51  
% 6.97/1.51  fof(f36,plain,(
% 6.97/1.51    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 6.97/1.51    inference(ennf_transformation,[],[f18])).
% 6.97/1.51  
% 6.97/1.51  fof(f37,plain,(
% 6.97/1.51    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 6.97/1.51    inference(flattening,[],[f36])).
% 6.97/1.51  
% 6.97/1.51  fof(f53,plain,(
% 6.97/1.51    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK7) != k7_partfun1(X0,X4,k1_funct_1(X3,sK7)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK7,X1))) )),
% 6.97/1.51    introduced(choice_axiom,[])).
% 6.97/1.51  
% 6.97/1.51  fof(f52,plain,(
% 6.97/1.51    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK6),X5) != k7_partfun1(X0,sK6,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK6)) & m1_subset_1(X5,X1)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK6))) )),
% 6.97/1.51    introduced(choice_axiom,[])).
% 6.97/1.51  
% 6.97/1.51  fof(f51,plain,(
% 6.97/1.51    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,sK5,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK5,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK5),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK5,X1,X2) & v1_funct_1(sK5))) )),
% 6.97/1.51    introduced(choice_axiom,[])).
% 6.97/1.51  
% 6.97/1.51  fof(f50,plain,(
% 6.97/1.51    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK3,sK4,sK2,X3,X4),X5) != k7_partfun1(sK2,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,X3),k1_relset_1(sK4,sK2,X4)) & m1_subset_1(X5,sK3)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & ~v1_xboole_0(sK4))),
% 6.97/1.51    introduced(choice_axiom,[])).
% 6.97/1.51  
% 6.97/1.51  fof(f54,plain,(
% 6.97/1.51    (((k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) & m1_subset_1(sK7,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)) & ~v1_xboole_0(sK4)),
% 6.97/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f37,f53,f52,f51,f50])).
% 6.97/1.51  
% 6.97/1.51  fof(f88,plain,(
% 6.97/1.51    m1_subset_1(sK7,sK3)),
% 6.97/1.51    inference(cnf_transformation,[],[f54])).
% 6.97/1.51  
% 6.97/1.51  fof(f6,axiom,(
% 6.97/1.51    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 6.97/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.97/1.51  
% 6.97/1.51  fof(f21,plain,(
% 6.97/1.51    ! [X0,X1] : ((m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X1,X0))),
% 6.97/1.51    inference(ennf_transformation,[],[f6])).
% 6.97/1.51  
% 6.97/1.51  fof(f22,plain,(
% 6.97/1.51    ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 6.97/1.51    inference(flattening,[],[f21])).
% 6.97/1.51  
% 6.97/1.51  fof(f64,plain,(
% 6.97/1.51    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) )),
% 6.97/1.51    inference(cnf_transformation,[],[f22])).
% 6.97/1.51  
% 6.97/1.51  fof(f7,axiom,(
% 6.97/1.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 6.97/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.97/1.51  
% 6.97/1.51  fof(f47,plain,(
% 6.97/1.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 6.97/1.51    inference(nnf_transformation,[],[f7])).
% 6.97/1.51  
% 6.97/1.51  fof(f65,plain,(
% 6.97/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 6.97/1.51    inference(cnf_transformation,[],[f47])).
% 6.97/1.51  
% 6.97/1.51  fof(f3,axiom,(
% 6.97/1.51    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 6.97/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.97/1.51  
% 6.97/1.51  fof(f46,plain,(
% 6.97/1.51    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 6.97/1.51    inference(nnf_transformation,[],[f3])).
% 6.97/1.51  
% 6.97/1.51  fof(f60,plain,(
% 6.97/1.51    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 6.97/1.51    inference(cnf_transformation,[],[f46])).
% 6.97/1.51  
% 6.97/1.51  fof(f90,plain,(
% 6.97/1.51    k1_xboole_0 != sK3),
% 6.97/1.51    inference(cnf_transformation,[],[f54])).
% 6.97/1.51  
% 6.97/1.51  fof(f87,plain,(
% 6.97/1.51    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))),
% 6.97/1.51    inference(cnf_transformation,[],[f54])).
% 6.97/1.51  
% 6.97/1.51  fof(f13,axiom,(
% 6.97/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 6.97/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.97/1.51  
% 6.97/1.51  fof(f29,plain,(
% 6.97/1.51    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.97/1.51    inference(ennf_transformation,[],[f13])).
% 6.97/1.51  
% 6.97/1.51  fof(f73,plain,(
% 6.97/1.51    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.97/1.51    inference(cnf_transformation,[],[f29])).
% 6.97/1.51  
% 6.97/1.51  fof(f11,axiom,(
% 6.97/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 6.97/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.97/1.51  
% 6.97/1.51  fof(f27,plain,(
% 6.97/1.51    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.97/1.51    inference(ennf_transformation,[],[f11])).
% 6.97/1.51  
% 6.97/1.51  fof(f71,plain,(
% 6.97/1.51    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.97/1.51    inference(cnf_transformation,[],[f27])).
% 6.97/1.51  
% 6.97/1.51  fof(f9,axiom,(
% 6.97/1.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 6.97/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.97/1.51  
% 6.97/1.51  fof(f24,plain,(
% 6.97/1.51    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 6.97/1.51    inference(ennf_transformation,[],[f9])).
% 6.97/1.51  
% 6.97/1.51  fof(f25,plain,(
% 6.97/1.51    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 6.97/1.51    inference(flattening,[],[f24])).
% 6.97/1.51  
% 6.97/1.51  fof(f69,plain,(
% 6.97/1.51    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 6.97/1.51    inference(cnf_transformation,[],[f25])).
% 6.97/1.51  
% 6.97/1.51  fof(f85,plain,(
% 6.97/1.51    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 6.97/1.51    inference(cnf_transformation,[],[f54])).
% 6.97/1.51  
% 6.97/1.51  fof(f89,plain,(
% 6.97/1.51    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))),
% 6.97/1.51    inference(cnf_transformation,[],[f54])).
% 6.97/1.51  
% 6.97/1.51  fof(f12,axiom,(
% 6.97/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 6.97/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.97/1.51  
% 6.97/1.51  fof(f28,plain,(
% 6.97/1.51    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.97/1.51    inference(ennf_transformation,[],[f12])).
% 6.97/1.51  
% 6.97/1.51  fof(f72,plain,(
% 6.97/1.51    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.97/1.51    inference(cnf_transformation,[],[f28])).
% 6.97/1.51  
% 6.97/1.51  fof(f2,axiom,(
% 6.97/1.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 6.97/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.97/1.51  
% 6.97/1.51  fof(f19,plain,(
% 6.97/1.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 6.97/1.51    inference(ennf_transformation,[],[f2])).
% 6.97/1.51  
% 6.97/1.51  fof(f42,plain,(
% 6.97/1.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 6.97/1.51    inference(nnf_transformation,[],[f19])).
% 6.97/1.51  
% 6.97/1.51  fof(f43,plain,(
% 6.97/1.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.97/1.51    inference(rectify,[],[f42])).
% 6.97/1.51  
% 6.97/1.51  fof(f44,plain,(
% 6.97/1.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 6.97/1.51    introduced(choice_axiom,[])).
% 6.97/1.51  
% 6.97/1.51  fof(f45,plain,(
% 6.97/1.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.97/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).
% 6.97/1.51  
% 6.97/1.51  fof(f57,plain,(
% 6.97/1.51    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 6.97/1.51    inference(cnf_transformation,[],[f45])).
% 6.97/1.51  
% 6.97/1.51  fof(f14,axiom,(
% 6.97/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 6.97/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.97/1.51  
% 6.97/1.51  fof(f30,plain,(
% 6.97/1.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.97/1.51    inference(ennf_transformation,[],[f14])).
% 6.97/1.51  
% 6.97/1.51  fof(f31,plain,(
% 6.97/1.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.97/1.51    inference(flattening,[],[f30])).
% 6.97/1.51  
% 6.97/1.51  fof(f49,plain,(
% 6.97/1.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.97/1.51    inference(nnf_transformation,[],[f31])).
% 6.97/1.51  
% 6.97/1.51  fof(f74,plain,(
% 6.97/1.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.97/1.51    inference(cnf_transformation,[],[f49])).
% 6.97/1.51  
% 6.97/1.51  fof(f1,axiom,(
% 6.97/1.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 6.97/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.97/1.51  
% 6.97/1.51  fof(f38,plain,(
% 6.97/1.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 6.97/1.51    inference(nnf_transformation,[],[f1])).
% 6.97/1.51  
% 6.97/1.51  fof(f39,plain,(
% 6.97/1.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 6.97/1.51    inference(rectify,[],[f38])).
% 6.97/1.51  
% 6.97/1.51  fof(f40,plain,(
% 6.97/1.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 6.97/1.51    introduced(choice_axiom,[])).
% 6.97/1.51  
% 6.97/1.51  fof(f41,plain,(
% 6.97/1.51    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 6.97/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 6.97/1.51  
% 6.97/1.51  fof(f56,plain,(
% 6.97/1.51    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 6.97/1.51    inference(cnf_transformation,[],[f41])).
% 6.97/1.51  
% 6.97/1.51  fof(f82,plain,(
% 6.97/1.51    ~v1_xboole_0(sK4)),
% 6.97/1.51    inference(cnf_transformation,[],[f54])).
% 6.97/1.51  
% 6.97/1.51  fof(f84,plain,(
% 6.97/1.51    v1_funct_2(sK5,sK3,sK4)),
% 6.97/1.51    inference(cnf_transformation,[],[f54])).
% 6.97/1.51  
% 6.97/1.51  fof(f4,axiom,(
% 6.97/1.51    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 6.97/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.97/1.51  
% 6.97/1.51  fof(f20,plain,(
% 6.97/1.51    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 6.97/1.51    inference(ennf_transformation,[],[f4])).
% 6.97/1.51  
% 6.97/1.51  fof(f62,plain,(
% 6.97/1.51    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 6.97/1.51    inference(cnf_transformation,[],[f20])).
% 6.97/1.51  
% 6.97/1.51  fof(f5,axiom,(
% 6.97/1.51    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 6.97/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.97/1.51  
% 6.97/1.51  fof(f63,plain,(
% 6.97/1.51    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 6.97/1.51    inference(cnf_transformation,[],[f5])).
% 6.97/1.51  
% 6.97/1.51  fof(f83,plain,(
% 6.97/1.51    v1_funct_1(sK5)),
% 6.97/1.51    inference(cnf_transformation,[],[f54])).
% 6.97/1.51  
% 6.97/1.51  fof(f10,axiom,(
% 6.97/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 6.97/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.97/1.51  
% 6.97/1.51  fof(f26,plain,(
% 6.97/1.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.97/1.51    inference(ennf_transformation,[],[f10])).
% 6.97/1.51  
% 6.97/1.51  fof(f70,plain,(
% 6.97/1.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.97/1.51    inference(cnf_transformation,[],[f26])).
% 6.97/1.51  
% 6.97/1.51  fof(f8,axiom,(
% 6.97/1.51    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 6.97/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.97/1.51  
% 6.97/1.51  fof(f23,plain,(
% 6.97/1.51    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 6.97/1.51    inference(ennf_transformation,[],[f8])).
% 6.97/1.51  
% 6.97/1.51  fof(f48,plain,(
% 6.97/1.51    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 6.97/1.51    inference(nnf_transformation,[],[f23])).
% 6.97/1.51  
% 6.97/1.51  fof(f68,plain,(
% 6.97/1.51    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 6.97/1.51    inference(cnf_transformation,[],[f48])).
% 6.97/1.51  
% 6.97/1.51  fof(f15,axiom,(
% 6.97/1.51    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)))),
% 6.97/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.97/1.51  
% 6.97/1.51  fof(f32,plain,(
% 6.97/1.51    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 6.97/1.51    inference(ennf_transformation,[],[f15])).
% 6.97/1.51  
% 6.97/1.51  fof(f33,plain,(
% 6.97/1.51    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 6.97/1.51    inference(flattening,[],[f32])).
% 6.97/1.51  
% 6.97/1.51  fof(f80,plain,(
% 6.97/1.51    ( ! [X2,X0,X1] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 6.97/1.51    inference(cnf_transformation,[],[f33])).
% 6.97/1.51  
% 6.97/1.51  fof(f86,plain,(
% 6.97/1.51    v1_funct_1(sK6)),
% 6.97/1.51    inference(cnf_transformation,[],[f54])).
% 6.97/1.51  
% 6.97/1.51  fof(f16,axiom,(
% 6.97/1.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 6.97/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.97/1.51  
% 6.97/1.51  fof(f34,plain,(
% 6.97/1.51    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 6.97/1.51    inference(ennf_transformation,[],[f16])).
% 6.97/1.51  
% 6.97/1.51  fof(f35,plain,(
% 6.97/1.51    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 6.97/1.51    inference(flattening,[],[f34])).
% 6.97/1.51  
% 6.97/1.51  fof(f81,plain,(
% 6.97/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 6.97/1.51    inference(cnf_transformation,[],[f35])).
% 6.97/1.51  
% 6.97/1.51  fof(f91,plain,(
% 6.97/1.51    k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7))),
% 6.97/1.51    inference(cnf_transformation,[],[f54])).
% 6.97/1.51  
% 6.97/1.51  cnf(c_30,negated_conjecture,
% 6.97/1.51      ( m1_subset_1(sK7,sK3) ),
% 6.97/1.51      inference(cnf_transformation,[],[f88]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_3317,plain,
% 6.97/1.51      ( m1_subset_1(sK7,sK3) = iProver_top ),
% 6.97/1.51      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_9,plain,
% 6.97/1.51      ( ~ m1_subset_1(X0,X1)
% 6.97/1.51      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
% 6.97/1.51      | k1_xboole_0 = X1 ),
% 6.97/1.51      inference(cnf_transformation,[],[f64]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_3333,plain,
% 6.97/1.51      ( k1_xboole_0 = X0
% 6.97/1.51      | m1_subset_1(X1,X0) != iProver_top
% 6.97/1.51      | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) = iProver_top ),
% 6.97/1.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_11,plain,
% 6.97/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 6.97/1.51      inference(cnf_transformation,[],[f65]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_3331,plain,
% 6.97/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 6.97/1.51      | r1_tarski(X0,X1) = iProver_top ),
% 6.97/1.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_5100,plain,
% 6.97/1.51      ( k1_xboole_0 = X0
% 6.97/1.51      | m1_subset_1(X1,X0) != iProver_top
% 6.97/1.51      | r1_tarski(k1_tarski(X1),X0) = iProver_top ),
% 6.97/1.51      inference(superposition,[status(thm)],[c_3333,c_3331]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_6,plain,
% 6.97/1.51      ( ~ r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1) ),
% 6.97/1.51      inference(cnf_transformation,[],[f60]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_3335,plain,
% 6.97/1.51      ( r1_tarski(k1_tarski(X0),X1) != iProver_top
% 6.97/1.51      | r2_hidden(X0,X1) = iProver_top ),
% 6.97/1.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_19545,plain,
% 6.97/1.51      ( k1_xboole_0 = X0
% 6.97/1.51      | m1_subset_1(X1,X0) != iProver_top
% 6.97/1.51      | r2_hidden(X1,X0) = iProver_top ),
% 6.97/1.51      inference(superposition,[status(thm)],[c_5100,c_3335]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_21998,plain,
% 6.97/1.51      ( sK3 = k1_xboole_0 | r2_hidden(sK7,sK3) = iProver_top ),
% 6.97/1.51      inference(superposition,[status(thm)],[c_3317,c_19545]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_43,plain,
% 6.97/1.51      ( m1_subset_1(sK7,sK3) = iProver_top ),
% 6.97/1.51      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_28,negated_conjecture,
% 6.97/1.51      ( k1_xboole_0 != sK3 ),
% 6.97/1.51      inference(cnf_transformation,[],[f90]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_3660,plain,
% 6.97/1.51      ( ~ m1_subset_1(X0,sK3)
% 6.97/1.51      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
% 6.97/1.51      | k1_xboole_0 = sK3 ),
% 6.97/1.51      inference(instantiation,[status(thm)],[c_9]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_3863,plain,
% 6.97/1.51      ( m1_subset_1(k1_tarski(sK7),k1_zfmisc_1(sK3))
% 6.97/1.51      | ~ m1_subset_1(sK7,sK3)
% 6.97/1.51      | k1_xboole_0 = sK3 ),
% 6.97/1.51      inference(instantiation,[status(thm)],[c_3660]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_3864,plain,
% 6.97/1.51      ( k1_xboole_0 = sK3
% 6.97/1.51      | m1_subset_1(k1_tarski(sK7),k1_zfmisc_1(sK3)) = iProver_top
% 6.97/1.51      | m1_subset_1(sK7,sK3) != iProver_top ),
% 6.97/1.51      inference(predicate_to_equality,[status(thm)],[c_3863]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_3610,plain,
% 6.97/1.51      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
% 6.97/1.51      | r1_tarski(k1_tarski(X0),X1) ),
% 6.97/1.51      inference(instantiation,[status(thm)],[c_11]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_4027,plain,
% 6.97/1.51      ( ~ m1_subset_1(k1_tarski(sK7),k1_zfmisc_1(sK3))
% 6.97/1.51      | r1_tarski(k1_tarski(sK7),sK3) ),
% 6.97/1.51      inference(instantiation,[status(thm)],[c_3610]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_4028,plain,
% 6.97/1.51      ( m1_subset_1(k1_tarski(sK7),k1_zfmisc_1(sK3)) != iProver_top
% 6.97/1.51      | r1_tarski(k1_tarski(sK7),sK3) = iProver_top ),
% 6.97/1.51      inference(predicate_to_equality,[status(thm)],[c_4027]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_4339,plain,
% 6.97/1.51      ( ~ r1_tarski(k1_tarski(sK7),sK3) | r2_hidden(sK7,sK3) ),
% 6.97/1.51      inference(instantiation,[status(thm)],[c_6]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_4340,plain,
% 6.97/1.51      ( r1_tarski(k1_tarski(sK7),sK3) != iProver_top
% 6.97/1.51      | r2_hidden(sK7,sK3) = iProver_top ),
% 6.97/1.51      inference(predicate_to_equality,[status(thm)],[c_4339]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_22057,plain,
% 6.97/1.51      ( r2_hidden(sK7,sK3) = iProver_top ),
% 6.97/1.51      inference(global_propositional_subsumption,
% 6.97/1.51                [status(thm)],
% 6.97/1.51                [c_21998,c_43,c_28,c_3864,c_4028,c_4340]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_31,negated_conjecture,
% 6.97/1.51      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
% 6.97/1.51      inference(cnf_transformation,[],[f87]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_3316,plain,
% 6.97/1.51      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 6.97/1.51      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_18,plain,
% 6.97/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.97/1.51      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 6.97/1.51      inference(cnf_transformation,[],[f73]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_3326,plain,
% 6.97/1.51      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 6.97/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.97/1.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_5014,plain,
% 6.97/1.51      ( k2_relset_1(sK4,sK2,sK6) = k2_relat_1(sK6) ),
% 6.97/1.51      inference(superposition,[status(thm)],[c_3316,c_3326]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_16,plain,
% 6.97/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.97/1.51      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 6.97/1.51      inference(cnf_transformation,[],[f71]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_3328,plain,
% 6.97/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.97/1.51      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 6.97/1.51      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_5836,plain,
% 6.97/1.51      ( m1_subset_1(k2_relat_1(sK6),k1_zfmisc_1(sK2)) = iProver_top
% 6.97/1.51      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top ),
% 6.97/1.51      inference(superposition,[status(thm)],[c_5014,c_3328]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_42,plain,
% 6.97/1.51      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 6.97/1.51      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_6438,plain,
% 6.97/1.51      ( m1_subset_1(k2_relat_1(sK6),k1_zfmisc_1(sK2)) = iProver_top ),
% 6.97/1.51      inference(global_propositional_subsumption,
% 6.97/1.51                [status(thm)],
% 6.97/1.51                [c_5836,c_42]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_6443,plain,
% 6.97/1.51      ( r1_tarski(k2_relat_1(sK6),sK2) = iProver_top ),
% 6.97/1.51      inference(superposition,[status(thm)],[c_6438,c_3331]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_14,plain,
% 6.97/1.51      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 6.97/1.51      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 6.97/1.51      | ~ v1_funct_1(X1)
% 6.97/1.51      | ~ v1_relat_1(X1) ),
% 6.97/1.51      inference(cnf_transformation,[],[f69]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_3330,plain,
% 6.97/1.51      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 6.97/1.51      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 6.97/1.51      | v1_funct_1(X1) != iProver_top
% 6.97/1.51      | v1_relat_1(X1) != iProver_top ),
% 6.97/1.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_33,negated_conjecture,
% 6.97/1.51      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 6.97/1.51      inference(cnf_transformation,[],[f85]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_3314,plain,
% 6.97/1.51      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 6.97/1.51      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_5015,plain,
% 6.97/1.51      ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
% 6.97/1.51      inference(superposition,[status(thm)],[c_3314,c_3326]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_29,negated_conjecture,
% 6.97/1.51      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
% 6.97/1.51      inference(cnf_transformation,[],[f89]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_3318,plain,
% 6.97/1.51      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
% 6.97/1.51      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_5234,plain,
% 6.97/1.51      ( r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
% 6.97/1.51      inference(demodulation,[status(thm)],[c_5015,c_3318]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_17,plain,
% 6.97/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.97/1.51      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 6.97/1.51      inference(cnf_transformation,[],[f72]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_3327,plain,
% 6.97/1.51      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 6.97/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.97/1.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_5083,plain,
% 6.97/1.51      ( k1_relset_1(sK4,sK2,sK6) = k1_relat_1(sK6) ),
% 6.97/1.51      inference(superposition,[status(thm)],[c_3316,c_3327]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_5437,plain,
% 6.97/1.51      ( r1_tarski(k2_relat_1(sK5),k1_relat_1(sK6)) = iProver_top ),
% 6.97/1.51      inference(light_normalisation,[status(thm)],[c_5234,c_5083]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_4,plain,
% 6.97/1.51      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 6.97/1.51      inference(cnf_transformation,[],[f57]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_3337,plain,
% 6.97/1.51      ( r1_tarski(X0,X1) != iProver_top
% 6.97/1.51      | r2_hidden(X2,X0) != iProver_top
% 6.97/1.51      | r2_hidden(X2,X1) = iProver_top ),
% 6.97/1.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_5990,plain,
% 6.97/1.51      ( r2_hidden(X0,k1_relat_1(sK6)) = iProver_top
% 6.97/1.51      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 6.97/1.51      inference(superposition,[status(thm)],[c_5437,c_3337]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_7794,plain,
% 6.97/1.51      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 6.97/1.51      | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top
% 6.97/1.51      | v1_funct_1(sK5) != iProver_top
% 6.97/1.51      | v1_relat_1(sK5) != iProver_top ),
% 6.97/1.51      inference(superposition,[status(thm)],[c_3330,c_5990]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_24,plain,
% 6.97/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 6.97/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.97/1.51      | k1_relset_1(X1,X2,X0) = X1
% 6.97/1.51      | k1_xboole_0 = X2 ),
% 6.97/1.51      inference(cnf_transformation,[],[f74]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_3320,plain,
% 6.97/1.51      ( k1_relset_1(X0,X1,X2) = X0
% 6.97/1.51      | k1_xboole_0 = X1
% 6.97/1.51      | v1_funct_2(X2,X0,X1) != iProver_top
% 6.97/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.97/1.51      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_4911,plain,
% 6.97/1.51      ( k1_relset_1(sK3,sK4,sK5) = sK3
% 6.97/1.51      | sK4 = k1_xboole_0
% 6.97/1.51      | v1_funct_2(sK5,sK3,sK4) != iProver_top ),
% 6.97/1.51      inference(superposition,[status(thm)],[c_3314,c_3320]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_0,plain,
% 6.97/1.51      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 6.97/1.51      inference(cnf_transformation,[],[f56]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_36,negated_conjecture,
% 6.97/1.51      ( ~ v1_xboole_0(sK4) ),
% 6.97/1.51      inference(cnf_transformation,[],[f82]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_556,plain,
% 6.97/1.51      ( r2_hidden(sK0(X0),X0) | sK4 != X0 ),
% 6.97/1.51      inference(resolution_lifted,[status(thm)],[c_0,c_36]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_557,plain,
% 6.97/1.51      ( r2_hidden(sK0(sK4),sK4) ),
% 6.97/1.51      inference(unflattening,[status(thm)],[c_556]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_34,negated_conjecture,
% 6.97/1.51      ( v1_funct_2(sK5,sK3,sK4) ),
% 6.97/1.51      inference(cnf_transformation,[],[f84]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_800,plain,
% 6.97/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.97/1.51      | k1_relset_1(X1,X2,X0) = X1
% 6.97/1.51      | sK5 != X0
% 6.97/1.51      | sK4 != X2
% 6.97/1.51      | sK3 != X1
% 6.97/1.51      | k1_xboole_0 = X2 ),
% 6.97/1.51      inference(resolution_lifted,[status(thm)],[c_24,c_34]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_801,plain,
% 6.97/1.51      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 6.97/1.51      | k1_relset_1(sK3,sK4,sK5) = sK3
% 6.97/1.51      | k1_xboole_0 = sK4 ),
% 6.97/1.51      inference(unflattening,[status(thm)],[c_800]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_803,plain,
% 6.97/1.51      ( k1_relset_1(sK3,sK4,sK5) = sK3 | k1_xboole_0 = sK4 ),
% 6.97/1.51      inference(global_propositional_subsumption,
% 6.97/1.51                [status(thm)],
% 6.97/1.51                [c_801,c_33]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_7,plain,
% 6.97/1.51      ( ~ r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1 ),
% 6.97/1.51      inference(cnf_transformation,[],[f62]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_3776,plain,
% 6.97/1.51      ( ~ r2_hidden(sK0(sK4),sK4)
% 6.97/1.51      | k2_xboole_0(k1_tarski(sK0(sK4)),sK4) = sK4 ),
% 6.97/1.51      inference(instantiation,[status(thm)],[c_7]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_2476,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_3675,plain,
% 6.97/1.51      ( k2_xboole_0(k1_tarski(X0),X1) != X2
% 6.97/1.51      | k2_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
% 6.97/1.51      | k1_xboole_0 != X2 ),
% 6.97/1.51      inference(instantiation,[status(thm)],[c_2476]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_4255,plain,
% 6.97/1.51      ( k2_xboole_0(k1_tarski(sK0(sK4)),sK4) != sK4
% 6.97/1.51      | k2_xboole_0(k1_tarski(sK0(sK4)),sK4) = k1_xboole_0
% 6.97/1.51      | k1_xboole_0 != sK4 ),
% 6.97/1.51      inference(instantiation,[status(thm)],[c_3675]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_8,plain,
% 6.97/1.51      ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
% 6.97/1.51      inference(cnf_transformation,[],[f63]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_4460,plain,
% 6.97/1.51      ( k2_xboole_0(k1_tarski(sK0(sK4)),sK4) != k1_xboole_0 ),
% 6.97/1.51      inference(instantiation,[status(thm)],[c_8]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_5669,plain,
% 6.97/1.51      ( k1_relset_1(sK3,sK4,sK5) = sK3 ),
% 6.97/1.51      inference(global_propositional_subsumption,
% 6.97/1.51                [status(thm)],
% 6.97/1.51                [c_4911,c_557,c_803,c_3776,c_4255,c_4460]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_5084,plain,
% 6.97/1.51      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 6.97/1.51      inference(superposition,[status(thm)],[c_3314,c_3327]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_5672,plain,
% 6.97/1.51      ( k1_relat_1(sK5) = sK3 ),
% 6.97/1.51      inference(demodulation,[status(thm)],[c_5669,c_5084]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_7799,plain,
% 6.97/1.51      ( r2_hidden(X0,sK3) != iProver_top
% 6.97/1.51      | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top
% 6.97/1.51      | v1_funct_1(sK5) != iProver_top
% 6.97/1.51      | v1_relat_1(sK5) != iProver_top ),
% 6.97/1.51      inference(light_normalisation,[status(thm)],[c_7794,c_5672]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_35,negated_conjecture,
% 6.97/1.51      ( v1_funct_1(sK5) ),
% 6.97/1.51      inference(cnf_transformation,[],[f83]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_38,plain,
% 6.97/1.51      ( v1_funct_1(sK5) = iProver_top ),
% 6.97/1.51      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_40,plain,
% 6.97/1.51      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 6.97/1.51      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_15,plain,
% 6.97/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.97/1.51      | v1_relat_1(X0) ),
% 6.97/1.51      inference(cnf_transformation,[],[f70]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_3621,plain,
% 6.97/1.51      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 6.97/1.51      | v1_relat_1(sK5) ),
% 6.97/1.51      inference(instantiation,[status(thm)],[c_15]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_3622,plain,
% 6.97/1.51      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 6.97/1.51      | v1_relat_1(sK5) = iProver_top ),
% 6.97/1.51      inference(predicate_to_equality,[status(thm)],[c_3621]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_9127,plain,
% 6.97/1.51      ( r2_hidden(X0,sK3) != iProver_top
% 6.97/1.51      | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top ),
% 6.97/1.51      inference(global_propositional_subsumption,
% 6.97/1.51                [status(thm)],
% 6.97/1.51                [c_7799,c_38,c_40,c_3622]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_12,plain,
% 6.97/1.51      ( v5_relat_1(X0,X1)
% 6.97/1.51      | ~ r1_tarski(k2_relat_1(X0),X1)
% 6.97/1.51      | ~ v1_relat_1(X0) ),
% 6.97/1.51      inference(cnf_transformation,[],[f68]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_25,plain,
% 6.97/1.51      ( ~ v5_relat_1(X0,X1)
% 6.97/1.51      | ~ r2_hidden(X2,k1_relat_1(X0))
% 6.97/1.51      | ~ v1_funct_1(X0)
% 6.97/1.51      | ~ v1_relat_1(X0)
% 6.97/1.51      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 6.97/1.51      inference(cnf_transformation,[],[f80]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_470,plain,
% 6.97/1.51      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 6.97/1.51      | ~ r2_hidden(X2,k1_relat_1(X0))
% 6.97/1.51      | ~ v1_funct_1(X0)
% 6.97/1.51      | ~ v1_relat_1(X0)
% 6.97/1.51      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 6.97/1.51      inference(resolution,[status(thm)],[c_12,c_25]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_3310,plain,
% 6.97/1.51      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 6.97/1.51      | r1_tarski(k2_relat_1(X1),X0) != iProver_top
% 6.97/1.51      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 6.97/1.51      | v1_funct_1(X1) != iProver_top
% 6.97/1.51      | v1_relat_1(X1) != iProver_top ),
% 6.97/1.51      inference(predicate_to_equality,[status(thm)],[c_470]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_9137,plain,
% 6.97/1.51      ( k7_partfun1(X0,sK6,k1_funct_1(sK5,X1)) = k1_funct_1(sK6,k1_funct_1(sK5,X1))
% 6.97/1.51      | r1_tarski(k2_relat_1(sK6),X0) != iProver_top
% 6.97/1.51      | r2_hidden(X1,sK3) != iProver_top
% 6.97/1.51      | v1_funct_1(sK6) != iProver_top
% 6.97/1.51      | v1_relat_1(sK6) != iProver_top ),
% 6.97/1.51      inference(superposition,[status(thm)],[c_9127,c_3310]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_32,negated_conjecture,
% 6.97/1.51      ( v1_funct_1(sK6) ),
% 6.97/1.51      inference(cnf_transformation,[],[f86]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_41,plain,
% 6.97/1.51      ( v1_funct_1(sK6) = iProver_top ),
% 6.97/1.51      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_3618,plain,
% 6.97/1.51      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 6.97/1.51      | v1_relat_1(sK6) ),
% 6.97/1.51      inference(instantiation,[status(thm)],[c_15]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_3619,plain,
% 6.97/1.51      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 6.97/1.51      | v1_relat_1(sK6) = iProver_top ),
% 6.97/1.51      inference(predicate_to_equality,[status(thm)],[c_3618]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_13815,plain,
% 6.97/1.51      ( k7_partfun1(X0,sK6,k1_funct_1(sK5,X1)) = k1_funct_1(sK6,k1_funct_1(sK5,X1))
% 6.97/1.51      | r1_tarski(k2_relat_1(sK6),X0) != iProver_top
% 6.97/1.51      | r2_hidden(X1,sK3) != iProver_top ),
% 6.97/1.51      inference(global_propositional_subsumption,
% 6.97/1.51                [status(thm)],
% 6.97/1.51                [c_9137,c_41,c_42,c_3619]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_13827,plain,
% 6.97/1.51      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 6.97/1.51      | r2_hidden(X0,sK3) != iProver_top ),
% 6.97/1.51      inference(superposition,[status(thm)],[c_6443,c_13815]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_22064,plain,
% 6.97/1.51      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 6.97/1.51      inference(superposition,[status(thm)],[c_22057,c_13827]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_26,plain,
% 6.97/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 6.97/1.51      | ~ m1_subset_1(X3,X1)
% 6.97/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 6.97/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.97/1.51      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
% 6.97/1.51      | ~ v1_funct_1(X4)
% 6.97/1.51      | ~ v1_funct_1(X0)
% 6.97/1.51      | v1_xboole_0(X2)
% 6.97/1.51      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 6.97/1.51      | k1_xboole_0 = X1 ),
% 6.97/1.51      inference(cnf_transformation,[],[f81]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_3319,plain,
% 6.97/1.51      ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
% 6.97/1.51      | k1_xboole_0 = X0
% 6.97/1.51      | v1_funct_2(X3,X0,X1) != iProver_top
% 6.97/1.51      | m1_subset_1(X5,X0) != iProver_top
% 6.97/1.51      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.97/1.51      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.97/1.51      | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
% 6.97/1.51      | v1_funct_1(X4) != iProver_top
% 6.97/1.51      | v1_funct_1(X3) != iProver_top
% 6.97/1.51      | v1_xboole_0(X1) = iProver_top ),
% 6.97/1.51      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_4187,plain,
% 6.97/1.51      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 6.97/1.51      | sK3 = k1_xboole_0
% 6.97/1.51      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 6.97/1.51      | m1_subset_1(X0,sK3) != iProver_top
% 6.97/1.51      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 6.97/1.51      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 6.97/1.51      | v1_funct_1(sK6) != iProver_top
% 6.97/1.51      | v1_funct_1(sK5) != iProver_top
% 6.97/1.51      | v1_xboole_0(sK4) = iProver_top ),
% 6.97/1.51      inference(superposition,[status(thm)],[c_3318,c_3319]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_37,plain,
% 6.97/1.51      ( v1_xboole_0(sK4) != iProver_top ),
% 6.97/1.51      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_39,plain,
% 6.97/1.51      ( v1_funct_2(sK5,sK3,sK4) = iProver_top ),
% 6.97/1.51      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_2475,plain,( X0 = X0 ),theory(equality) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_2506,plain,
% 6.97/1.51      ( k1_xboole_0 = k1_xboole_0 ),
% 6.97/1.51      inference(instantiation,[status(thm)],[c_2475]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_3679,plain,
% 6.97/1.51      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 6.97/1.51      inference(instantiation,[status(thm)],[c_2476]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_3680,plain,
% 6.97/1.51      ( sK3 != k1_xboole_0
% 6.97/1.51      | k1_xboole_0 = sK3
% 6.97/1.51      | k1_xboole_0 != k1_xboole_0 ),
% 6.97/1.51      inference(instantiation,[status(thm)],[c_3679]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_4627,plain,
% 6.97/1.51      ( m1_subset_1(X0,sK3) != iProver_top
% 6.97/1.51      | k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0)) ),
% 6.97/1.51      inference(global_propositional_subsumption,
% 6.97/1.51                [status(thm)],
% 6.97/1.51                [c_4187,c_37,c_38,c_39,c_40,c_41,c_42,c_28,c_2506,c_3680]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_4628,plain,
% 6.97/1.51      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 6.97/1.51      | m1_subset_1(X0,sK3) != iProver_top ),
% 6.97/1.51      inference(renaming,[status(thm)],[c_4627]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_4635,plain,
% 6.97/1.51      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 6.97/1.51      inference(superposition,[status(thm)],[c_3317,c_4628]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_27,negated_conjecture,
% 6.97/1.51      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) ),
% 6.97/1.51      inference(cnf_transformation,[],[f91]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(c_4637,plain,
% 6.97/1.51      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 6.97/1.51      inference(demodulation,[status(thm)],[c_4635,c_27]) ).
% 6.97/1.51  
% 6.97/1.51  cnf(contradiction,plain,
% 6.97/1.51      ( $false ),
% 6.97/1.51      inference(minisat,[status(thm)],[c_22064,c_4637]) ).
% 6.97/1.51  
% 6.97/1.51  
% 6.97/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 6.97/1.51  
% 6.97/1.51  ------                               Statistics
% 6.97/1.51  
% 6.97/1.51  ------ Selected
% 6.97/1.51  
% 6.97/1.51  total_time:                             0.596
% 6.97/1.51  
%------------------------------------------------------------------------------
