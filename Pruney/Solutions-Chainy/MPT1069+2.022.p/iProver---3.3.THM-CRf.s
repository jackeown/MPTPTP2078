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
% DateTime   : Thu Dec  3 12:09:46 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 466 expanded)
%              Number of clauses        :  100 ( 132 expanded)
%              Number of leaves         :   25 ( 152 expanded)
%              Depth                    :   17
%              Number of atoms          :  604 (3307 expanded)
%              Number of equality atoms :  221 ( 870 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f61,plain,(
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

fof(f60,plain,(
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

fof(f59,plain,(
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

fof(f58,plain,
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

fof(f62,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f44,f61,f60,f59,f58])).

fof(f103,plain,(
    m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f105,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f62])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f100,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f62])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f104,plain,(
    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
    inference(cnf_transformation,[],[f62])).

fof(f102,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f62])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f50,f51])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

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

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f53])).

fof(f71,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f97,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f99,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f47])).

fof(f64,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f17,axiom,(
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

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f98,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f101,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f62])).

fof(f19,axiom,(
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

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

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
    inference(cnf_transformation,[],[f42])).

fof(f106,plain,(
    k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2295,plain,
    ( m1_subset_1(sK7,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2313,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4737,plain,
    ( r2_hidden(sK7,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2295,c_2313])).

cnf(c_50,plain,
    ( m1_subset_1(sK7,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_35,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2589,plain,
    ( ~ v1_xboole_0(sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2590,plain,
    ( k1_xboole_0 = sK3
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2589])).

cnf(c_2760,plain,
    ( ~ m1_subset_1(X0,sK3)
    | r2_hidden(X0,sK3)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3215,plain,
    ( ~ m1_subset_1(sK7,sK3)
    | r2_hidden(sK7,sK3)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2760])).

cnf(c_3216,plain,
    ( m1_subset_1(sK7,sK3) != iProver_top
    | r2_hidden(sK7,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3215])).

cnf(c_5409,plain,
    ( r2_hidden(sK7,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4737,c_50,c_35,c_2590,c_3216])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2310,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2292,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2305,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4061,plain,
    ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2292,c_2305])).

cnf(c_36,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_2296,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_4359,plain,
    ( r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4061,c_2296])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2294,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2306,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4182,plain,
    ( k1_relset_1(sK4,sK2,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_2294,c_2306])).

cnf(c_4516,plain,
    ( r1_tarski(k2_relat_1(sK5),k1_relat_1(sK6)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4359,c_4182])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2318,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5233,plain,
    ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4516,c_2318])).

cnf(c_9333,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2310,c_5233])).

cnf(c_19,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_14,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_551,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_19,c_14])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_555,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_551,c_17])).

cnf(c_556,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_555])).

cnf(c_2287,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_556])).

cnf(c_2730,plain,
    ( r1_tarski(k1_relat_1(sK5),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2292,c_2287])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2316,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4773,plain,
    ( k1_relat_1(sK5) = sK3
    | r1_tarski(sK3,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2730,c_2316])).

cnf(c_43,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_46,plain,
    ( v1_funct_2(sK5,sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_134,plain,
    ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1458,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2613,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1458])).

cnf(c_2615,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2613])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_3473,plain,
    ( ~ r1_tarski(X0,sK0(X0))
    | ~ r2_hidden(sK0(X0),X0) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_3475,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0(k1_xboole_0))
    | ~ r2_hidden(sK0(k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3473])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2298,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_4617,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | sK4 = k1_xboole_0
    | v1_funct_2(sK5,sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2292,c_2298])).

cnf(c_4183,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2292,c_2306])).

cnf(c_4621,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0
    | v1_funct_2(sK5,sK3,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4617,c_4183])).

cnf(c_9,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_5833,plain,
    ( r1_tarski(k1_xboole_0,sK0(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_5934,plain,
    ( k1_relat_1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4773,c_43,c_46,c_134,c_2615,c_3475,c_4621,c_5833])).

cnf(c_9338,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9333,c_5934])).

cnf(c_42,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_45,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_47,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_2610,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2611,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2610])).

cnf(c_10129,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9338,c_45,c_47,c_2611])).

cnf(c_18,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_32,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_523,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(resolution,[status(thm)],[c_18,c_32])).

cnf(c_527,plain,
    ( ~ v1_funct_1(X0)
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_523,c_17])).

cnf(c_528,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(renaming,[status(thm)],[c_527])).

cnf(c_2288,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_528])).

cnf(c_3328,plain,
    ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2294,c_2288])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_48,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_3562,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3328,c_48])).

cnf(c_3563,plain,
    ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3562])).

cnf(c_10140,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10129,c_3563])).

cnf(c_10174,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_5409,c_10140])).

cnf(c_33,plain,
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

cnf(c_2297,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3940,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | sK3 = k1_xboole_0
    | v1_funct_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(X0,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2296,c_2297])).

cnf(c_44,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_49,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_117,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_122,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1457,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2661,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1457])).

cnf(c_2662,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2661])).

cnf(c_4601,plain,
    ( m1_subset_1(X0,sK3) != iProver_top
    | k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3940,c_44,c_45,c_46,c_47,c_48,c_49,c_35,c_117,c_122,c_2662])).

cnf(c_4602,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_4601])).

cnf(c_4609,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_2295,c_4602])).

cnf(c_34,negated_conjecture,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_5318,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(demodulation,[status(thm)],[c_4609,c_34])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10174,c_5318])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:20:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.34/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.00  
% 3.34/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.34/1.00  
% 3.34/1.00  ------  iProver source info
% 3.34/1.00  
% 3.34/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.34/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.34/1.00  git: non_committed_changes: false
% 3.34/1.00  git: last_make_outside_of_git: false
% 3.34/1.00  
% 3.34/1.00  ------ 
% 3.34/1.00  
% 3.34/1.00  ------ Input Options
% 3.34/1.00  
% 3.34/1.00  --out_options                           all
% 3.34/1.00  --tptp_safe_out                         true
% 3.34/1.00  --problem_path                          ""
% 3.34/1.00  --include_path                          ""
% 3.34/1.00  --clausifier                            res/vclausify_rel
% 3.34/1.00  --clausifier_options                    --mode clausify
% 3.34/1.00  --stdin                                 false
% 3.34/1.00  --stats_out                             all
% 3.34/1.00  
% 3.34/1.00  ------ General Options
% 3.34/1.00  
% 3.34/1.00  --fof                                   false
% 3.34/1.00  --time_out_real                         305.
% 3.34/1.00  --time_out_virtual                      -1.
% 3.34/1.00  --symbol_type_check                     false
% 3.34/1.00  --clausify_out                          false
% 3.34/1.00  --sig_cnt_out                           false
% 3.34/1.00  --trig_cnt_out                          false
% 3.34/1.00  --trig_cnt_out_tolerance                1.
% 3.34/1.00  --trig_cnt_out_sk_spl                   false
% 3.34/1.00  --abstr_cl_out                          false
% 3.34/1.00  
% 3.34/1.00  ------ Global Options
% 3.34/1.00  
% 3.34/1.00  --schedule                              default
% 3.34/1.00  --add_important_lit                     false
% 3.34/1.00  --prop_solver_per_cl                    1000
% 3.34/1.00  --min_unsat_core                        false
% 3.34/1.00  --soft_assumptions                      false
% 3.34/1.00  --soft_lemma_size                       3
% 3.34/1.00  --prop_impl_unit_size                   0
% 3.34/1.00  --prop_impl_unit                        []
% 3.34/1.00  --share_sel_clauses                     true
% 3.34/1.00  --reset_solvers                         false
% 3.34/1.00  --bc_imp_inh                            [conj_cone]
% 3.34/1.00  --conj_cone_tolerance                   3.
% 3.34/1.00  --extra_neg_conj                        none
% 3.34/1.00  --large_theory_mode                     true
% 3.34/1.00  --prolific_symb_bound                   200
% 3.34/1.00  --lt_threshold                          2000
% 3.34/1.00  --clause_weak_htbl                      true
% 3.34/1.00  --gc_record_bc_elim                     false
% 3.34/1.00  
% 3.34/1.00  ------ Preprocessing Options
% 3.34/1.00  
% 3.34/1.00  --preprocessing_flag                    true
% 3.34/1.00  --time_out_prep_mult                    0.1
% 3.34/1.00  --splitting_mode                        input
% 3.34/1.00  --splitting_grd                         true
% 3.34/1.00  --splitting_cvd                         false
% 3.34/1.00  --splitting_cvd_svl                     false
% 3.34/1.00  --splitting_nvd                         32
% 3.34/1.00  --sub_typing                            true
% 3.34/1.00  --prep_gs_sim                           true
% 3.34/1.00  --prep_unflatten                        true
% 3.34/1.00  --prep_res_sim                          true
% 3.34/1.00  --prep_upred                            true
% 3.34/1.00  --prep_sem_filter                       exhaustive
% 3.34/1.00  --prep_sem_filter_out                   false
% 3.34/1.00  --pred_elim                             true
% 3.34/1.00  --res_sim_input                         true
% 3.34/1.00  --eq_ax_congr_red                       true
% 3.34/1.00  --pure_diseq_elim                       true
% 3.34/1.00  --brand_transform                       false
% 3.34/1.00  --non_eq_to_eq                          false
% 3.34/1.00  --prep_def_merge                        true
% 3.34/1.00  --prep_def_merge_prop_impl              false
% 3.34/1.00  --prep_def_merge_mbd                    true
% 3.34/1.00  --prep_def_merge_tr_red                 false
% 3.34/1.00  --prep_def_merge_tr_cl                  false
% 3.34/1.00  --smt_preprocessing                     true
% 3.34/1.00  --smt_ac_axioms                         fast
% 3.34/1.00  --preprocessed_out                      false
% 3.34/1.00  --preprocessed_stats                    false
% 3.34/1.00  
% 3.34/1.00  ------ Abstraction refinement Options
% 3.34/1.00  
% 3.34/1.00  --abstr_ref                             []
% 3.34/1.00  --abstr_ref_prep                        false
% 3.34/1.00  --abstr_ref_until_sat                   false
% 3.34/1.00  --abstr_ref_sig_restrict                funpre
% 3.34/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/1.00  --abstr_ref_under                       []
% 3.34/1.00  
% 3.34/1.00  ------ SAT Options
% 3.34/1.00  
% 3.34/1.00  --sat_mode                              false
% 3.34/1.00  --sat_fm_restart_options                ""
% 3.34/1.00  --sat_gr_def                            false
% 3.34/1.00  --sat_epr_types                         true
% 3.34/1.00  --sat_non_cyclic_types                  false
% 3.34/1.00  --sat_finite_models                     false
% 3.34/1.00  --sat_fm_lemmas                         false
% 3.34/1.00  --sat_fm_prep                           false
% 3.34/1.00  --sat_fm_uc_incr                        true
% 3.34/1.00  --sat_out_model                         small
% 3.34/1.00  --sat_out_clauses                       false
% 3.34/1.00  
% 3.34/1.00  ------ QBF Options
% 3.34/1.00  
% 3.34/1.00  --qbf_mode                              false
% 3.34/1.00  --qbf_elim_univ                         false
% 3.34/1.00  --qbf_dom_inst                          none
% 3.34/1.00  --qbf_dom_pre_inst                      false
% 3.34/1.00  --qbf_sk_in                             false
% 3.34/1.00  --qbf_pred_elim                         true
% 3.34/1.00  --qbf_split                             512
% 3.34/1.00  
% 3.34/1.00  ------ BMC1 Options
% 3.34/1.00  
% 3.34/1.00  --bmc1_incremental                      false
% 3.34/1.00  --bmc1_axioms                           reachable_all
% 3.34/1.00  --bmc1_min_bound                        0
% 3.34/1.00  --bmc1_max_bound                        -1
% 3.34/1.00  --bmc1_max_bound_default                -1
% 3.34/1.00  --bmc1_symbol_reachability              true
% 3.34/1.00  --bmc1_property_lemmas                  false
% 3.34/1.00  --bmc1_k_induction                      false
% 3.34/1.00  --bmc1_non_equiv_states                 false
% 3.34/1.00  --bmc1_deadlock                         false
% 3.34/1.00  --bmc1_ucm                              false
% 3.34/1.00  --bmc1_add_unsat_core                   none
% 3.34/1.00  --bmc1_unsat_core_children              false
% 3.34/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/1.00  --bmc1_out_stat                         full
% 3.34/1.00  --bmc1_ground_init                      false
% 3.34/1.00  --bmc1_pre_inst_next_state              false
% 3.34/1.00  --bmc1_pre_inst_state                   false
% 3.34/1.00  --bmc1_pre_inst_reach_state             false
% 3.34/1.00  --bmc1_out_unsat_core                   false
% 3.34/1.00  --bmc1_aig_witness_out                  false
% 3.34/1.00  --bmc1_verbose                          false
% 3.34/1.00  --bmc1_dump_clauses_tptp                false
% 3.34/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.34/1.00  --bmc1_dump_file                        -
% 3.34/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.34/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.34/1.00  --bmc1_ucm_extend_mode                  1
% 3.34/1.00  --bmc1_ucm_init_mode                    2
% 3.34/1.00  --bmc1_ucm_cone_mode                    none
% 3.34/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.34/1.00  --bmc1_ucm_relax_model                  4
% 3.34/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.34/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/1.00  --bmc1_ucm_layered_model                none
% 3.34/1.00  --bmc1_ucm_max_lemma_size               10
% 3.34/1.00  
% 3.34/1.00  ------ AIG Options
% 3.34/1.00  
% 3.34/1.00  --aig_mode                              false
% 3.34/1.00  
% 3.34/1.00  ------ Instantiation Options
% 3.34/1.00  
% 3.34/1.00  --instantiation_flag                    true
% 3.34/1.00  --inst_sos_flag                         false
% 3.34/1.00  --inst_sos_phase                        true
% 3.34/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/1.00  --inst_lit_sel_side                     num_symb
% 3.34/1.00  --inst_solver_per_active                1400
% 3.34/1.00  --inst_solver_calls_frac                1.
% 3.34/1.00  --inst_passive_queue_type               priority_queues
% 3.34/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/1.00  --inst_passive_queues_freq              [25;2]
% 3.34/1.00  --inst_dismatching                      true
% 3.34/1.00  --inst_eager_unprocessed_to_passive     true
% 3.34/1.00  --inst_prop_sim_given                   true
% 3.34/1.00  --inst_prop_sim_new                     false
% 3.34/1.00  --inst_subs_new                         false
% 3.34/1.00  --inst_eq_res_simp                      false
% 3.34/1.00  --inst_subs_given                       false
% 3.34/1.00  --inst_orphan_elimination               true
% 3.34/1.00  --inst_learning_loop_flag               true
% 3.34/1.00  --inst_learning_start                   3000
% 3.34/1.00  --inst_learning_factor                  2
% 3.34/1.00  --inst_start_prop_sim_after_learn       3
% 3.34/1.00  --inst_sel_renew                        solver
% 3.34/1.00  --inst_lit_activity_flag                true
% 3.34/1.00  --inst_restr_to_given                   false
% 3.34/1.00  --inst_activity_threshold               500
% 3.34/1.00  --inst_out_proof                        true
% 3.34/1.00  
% 3.34/1.00  ------ Resolution Options
% 3.34/1.00  
% 3.34/1.00  --resolution_flag                       true
% 3.34/1.00  --res_lit_sel                           adaptive
% 3.34/1.00  --res_lit_sel_side                      none
% 3.34/1.00  --res_ordering                          kbo
% 3.34/1.00  --res_to_prop_solver                    active
% 3.34/1.00  --res_prop_simpl_new                    false
% 3.34/1.00  --res_prop_simpl_given                  true
% 3.34/1.00  --res_passive_queue_type                priority_queues
% 3.34/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/1.00  --res_passive_queues_freq               [15;5]
% 3.34/1.00  --res_forward_subs                      full
% 3.34/1.00  --res_backward_subs                     full
% 3.34/1.00  --res_forward_subs_resolution           true
% 3.34/1.00  --res_backward_subs_resolution          true
% 3.34/1.00  --res_orphan_elimination                true
% 3.34/1.00  --res_time_limit                        2.
% 3.34/1.00  --res_out_proof                         true
% 3.34/1.00  
% 3.34/1.00  ------ Superposition Options
% 3.34/1.00  
% 3.34/1.00  --superposition_flag                    true
% 3.34/1.00  --sup_passive_queue_type                priority_queues
% 3.34/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.34/1.00  --demod_completeness_check              fast
% 3.34/1.00  --demod_use_ground                      true
% 3.34/1.00  --sup_to_prop_solver                    passive
% 3.34/1.00  --sup_prop_simpl_new                    true
% 3.34/1.00  --sup_prop_simpl_given                  true
% 3.34/1.00  --sup_fun_splitting                     false
% 3.34/1.00  --sup_smt_interval                      50000
% 3.34/1.00  
% 3.34/1.00  ------ Superposition Simplification Setup
% 3.34/1.00  
% 3.34/1.00  --sup_indices_passive                   []
% 3.34/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/1.00  --sup_full_bw                           [BwDemod]
% 3.34/1.00  --sup_immed_triv                        [TrivRules]
% 3.34/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/1.00  --sup_immed_bw_main                     []
% 3.34/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/1.00  
% 3.34/1.00  ------ Combination Options
% 3.34/1.00  
% 3.34/1.00  --comb_res_mult                         3
% 3.34/1.00  --comb_sup_mult                         2
% 3.34/1.00  --comb_inst_mult                        10
% 3.34/1.00  
% 3.34/1.00  ------ Debug Options
% 3.34/1.00  
% 3.34/1.00  --dbg_backtrace                         false
% 3.34/1.00  --dbg_dump_prop_clauses                 false
% 3.34/1.00  --dbg_dump_prop_clauses_file            -
% 3.34/1.00  --dbg_out_stat                          false
% 3.34/1.00  ------ Parsing...
% 3.34/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.34/1.00  
% 3.34/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.34/1.00  
% 3.34/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.34/1.00  
% 3.34/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.34/1.00  ------ Proving...
% 3.34/1.00  ------ Problem Properties 
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  clauses                                 38
% 3.34/1.00  conjectures                             10
% 3.34/1.00  EPR                                     14
% 3.34/1.00  Horn                                    29
% 3.34/1.00  unary                                   12
% 3.34/1.00  binary                                  12
% 3.34/1.00  lits                                    93
% 3.34/1.00  lits eq                                 18
% 3.34/1.00  fd_pure                                 0
% 3.34/1.00  fd_pseudo                               0
% 3.34/1.00  fd_cond                                 5
% 3.34/1.00  fd_pseudo_cond                          1
% 3.34/1.00  AC symbols                              0
% 3.34/1.00  
% 3.34/1.00  ------ Schedule dynamic 5 is on 
% 3.34/1.00  
% 3.34/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  ------ 
% 3.34/1.00  Current options:
% 3.34/1.00  ------ 
% 3.34/1.00  
% 3.34/1.00  ------ Input Options
% 3.34/1.00  
% 3.34/1.00  --out_options                           all
% 3.34/1.00  --tptp_safe_out                         true
% 3.34/1.00  --problem_path                          ""
% 3.34/1.00  --include_path                          ""
% 3.34/1.00  --clausifier                            res/vclausify_rel
% 3.34/1.00  --clausifier_options                    --mode clausify
% 3.34/1.00  --stdin                                 false
% 3.34/1.00  --stats_out                             all
% 3.34/1.00  
% 3.34/1.00  ------ General Options
% 3.34/1.00  
% 3.34/1.00  --fof                                   false
% 3.34/1.00  --time_out_real                         305.
% 3.34/1.00  --time_out_virtual                      -1.
% 3.34/1.00  --symbol_type_check                     false
% 3.34/1.00  --clausify_out                          false
% 3.34/1.00  --sig_cnt_out                           false
% 3.34/1.00  --trig_cnt_out                          false
% 3.34/1.00  --trig_cnt_out_tolerance                1.
% 3.34/1.00  --trig_cnt_out_sk_spl                   false
% 3.34/1.00  --abstr_cl_out                          false
% 3.34/1.00  
% 3.34/1.00  ------ Global Options
% 3.34/1.00  
% 3.34/1.00  --schedule                              default
% 3.34/1.00  --add_important_lit                     false
% 3.34/1.00  --prop_solver_per_cl                    1000
% 3.34/1.00  --min_unsat_core                        false
% 3.34/1.00  --soft_assumptions                      false
% 3.34/1.00  --soft_lemma_size                       3
% 3.34/1.00  --prop_impl_unit_size                   0
% 3.34/1.00  --prop_impl_unit                        []
% 3.34/1.00  --share_sel_clauses                     true
% 3.34/1.00  --reset_solvers                         false
% 3.34/1.00  --bc_imp_inh                            [conj_cone]
% 3.34/1.00  --conj_cone_tolerance                   3.
% 3.34/1.00  --extra_neg_conj                        none
% 3.34/1.00  --large_theory_mode                     true
% 3.34/1.00  --prolific_symb_bound                   200
% 3.34/1.00  --lt_threshold                          2000
% 3.34/1.00  --clause_weak_htbl                      true
% 3.34/1.00  --gc_record_bc_elim                     false
% 3.34/1.00  
% 3.34/1.00  ------ Preprocessing Options
% 3.34/1.00  
% 3.34/1.00  --preprocessing_flag                    true
% 3.34/1.00  --time_out_prep_mult                    0.1
% 3.34/1.00  --splitting_mode                        input
% 3.34/1.00  --splitting_grd                         true
% 3.34/1.00  --splitting_cvd                         false
% 3.34/1.00  --splitting_cvd_svl                     false
% 3.34/1.00  --splitting_nvd                         32
% 3.34/1.00  --sub_typing                            true
% 3.34/1.00  --prep_gs_sim                           true
% 3.34/1.00  --prep_unflatten                        true
% 3.34/1.00  --prep_res_sim                          true
% 3.34/1.00  --prep_upred                            true
% 3.34/1.00  --prep_sem_filter                       exhaustive
% 3.34/1.00  --prep_sem_filter_out                   false
% 3.34/1.00  --pred_elim                             true
% 3.34/1.00  --res_sim_input                         true
% 3.34/1.00  --eq_ax_congr_red                       true
% 3.34/1.00  --pure_diseq_elim                       true
% 3.34/1.00  --brand_transform                       false
% 3.34/1.00  --non_eq_to_eq                          false
% 3.34/1.00  --prep_def_merge                        true
% 3.34/1.00  --prep_def_merge_prop_impl              false
% 3.34/1.00  --prep_def_merge_mbd                    true
% 3.34/1.00  --prep_def_merge_tr_red                 false
% 3.34/1.00  --prep_def_merge_tr_cl                  false
% 3.34/1.00  --smt_preprocessing                     true
% 3.34/1.00  --smt_ac_axioms                         fast
% 3.34/1.00  --preprocessed_out                      false
% 3.34/1.00  --preprocessed_stats                    false
% 3.34/1.00  
% 3.34/1.00  ------ Abstraction refinement Options
% 3.34/1.00  
% 3.34/1.00  --abstr_ref                             []
% 3.34/1.00  --abstr_ref_prep                        false
% 3.34/1.00  --abstr_ref_until_sat                   false
% 3.34/1.00  --abstr_ref_sig_restrict                funpre
% 3.34/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/1.00  --abstr_ref_under                       []
% 3.34/1.00  
% 3.34/1.00  ------ SAT Options
% 3.34/1.00  
% 3.34/1.00  --sat_mode                              false
% 3.34/1.00  --sat_fm_restart_options                ""
% 3.34/1.00  --sat_gr_def                            false
% 3.34/1.00  --sat_epr_types                         true
% 3.34/1.00  --sat_non_cyclic_types                  false
% 3.34/1.00  --sat_finite_models                     false
% 3.34/1.00  --sat_fm_lemmas                         false
% 3.34/1.00  --sat_fm_prep                           false
% 3.34/1.00  --sat_fm_uc_incr                        true
% 3.34/1.00  --sat_out_model                         small
% 3.34/1.00  --sat_out_clauses                       false
% 3.34/1.00  
% 3.34/1.00  ------ QBF Options
% 3.34/1.00  
% 3.34/1.00  --qbf_mode                              false
% 3.34/1.00  --qbf_elim_univ                         false
% 3.34/1.00  --qbf_dom_inst                          none
% 3.34/1.00  --qbf_dom_pre_inst                      false
% 3.34/1.00  --qbf_sk_in                             false
% 3.34/1.00  --qbf_pred_elim                         true
% 3.34/1.00  --qbf_split                             512
% 3.34/1.00  
% 3.34/1.00  ------ BMC1 Options
% 3.34/1.00  
% 3.34/1.00  --bmc1_incremental                      false
% 3.34/1.00  --bmc1_axioms                           reachable_all
% 3.34/1.00  --bmc1_min_bound                        0
% 3.34/1.00  --bmc1_max_bound                        -1
% 3.34/1.00  --bmc1_max_bound_default                -1
% 3.34/1.00  --bmc1_symbol_reachability              true
% 3.34/1.00  --bmc1_property_lemmas                  false
% 3.34/1.00  --bmc1_k_induction                      false
% 3.34/1.00  --bmc1_non_equiv_states                 false
% 3.34/1.00  --bmc1_deadlock                         false
% 3.34/1.00  --bmc1_ucm                              false
% 3.34/1.00  --bmc1_add_unsat_core                   none
% 3.34/1.00  --bmc1_unsat_core_children              false
% 3.34/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/1.00  --bmc1_out_stat                         full
% 3.34/1.00  --bmc1_ground_init                      false
% 3.34/1.00  --bmc1_pre_inst_next_state              false
% 3.34/1.00  --bmc1_pre_inst_state                   false
% 3.34/1.00  --bmc1_pre_inst_reach_state             false
% 3.34/1.00  --bmc1_out_unsat_core                   false
% 3.34/1.00  --bmc1_aig_witness_out                  false
% 3.34/1.00  --bmc1_verbose                          false
% 3.34/1.00  --bmc1_dump_clauses_tptp                false
% 3.34/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.34/1.00  --bmc1_dump_file                        -
% 3.34/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.34/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.34/1.00  --bmc1_ucm_extend_mode                  1
% 3.34/1.00  --bmc1_ucm_init_mode                    2
% 3.34/1.00  --bmc1_ucm_cone_mode                    none
% 3.34/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.34/1.00  --bmc1_ucm_relax_model                  4
% 3.34/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.34/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/1.00  --bmc1_ucm_layered_model                none
% 3.34/1.00  --bmc1_ucm_max_lemma_size               10
% 3.34/1.00  
% 3.34/1.00  ------ AIG Options
% 3.34/1.00  
% 3.34/1.00  --aig_mode                              false
% 3.34/1.00  
% 3.34/1.00  ------ Instantiation Options
% 3.34/1.00  
% 3.34/1.00  --instantiation_flag                    true
% 3.34/1.00  --inst_sos_flag                         false
% 3.34/1.00  --inst_sos_phase                        true
% 3.34/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/1.00  --inst_lit_sel_side                     none
% 3.34/1.00  --inst_solver_per_active                1400
% 3.34/1.00  --inst_solver_calls_frac                1.
% 3.34/1.00  --inst_passive_queue_type               priority_queues
% 3.34/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/1.00  --inst_passive_queues_freq              [25;2]
% 3.34/1.00  --inst_dismatching                      true
% 3.34/1.00  --inst_eager_unprocessed_to_passive     true
% 3.34/1.00  --inst_prop_sim_given                   true
% 3.34/1.00  --inst_prop_sim_new                     false
% 3.34/1.00  --inst_subs_new                         false
% 3.34/1.00  --inst_eq_res_simp                      false
% 3.34/1.00  --inst_subs_given                       false
% 3.34/1.00  --inst_orphan_elimination               true
% 3.34/1.00  --inst_learning_loop_flag               true
% 3.34/1.00  --inst_learning_start                   3000
% 3.34/1.00  --inst_learning_factor                  2
% 3.34/1.00  --inst_start_prop_sim_after_learn       3
% 3.34/1.00  --inst_sel_renew                        solver
% 3.34/1.00  --inst_lit_activity_flag                true
% 3.34/1.00  --inst_restr_to_given                   false
% 3.34/1.00  --inst_activity_threshold               500
% 3.34/1.00  --inst_out_proof                        true
% 3.34/1.00  
% 3.34/1.00  ------ Resolution Options
% 3.34/1.00  
% 3.34/1.00  --resolution_flag                       false
% 3.34/1.00  --res_lit_sel                           adaptive
% 3.34/1.00  --res_lit_sel_side                      none
% 3.34/1.00  --res_ordering                          kbo
% 3.34/1.00  --res_to_prop_solver                    active
% 3.34/1.00  --res_prop_simpl_new                    false
% 3.34/1.00  --res_prop_simpl_given                  true
% 3.34/1.00  --res_passive_queue_type                priority_queues
% 3.34/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/1.00  --res_passive_queues_freq               [15;5]
% 3.34/1.00  --res_forward_subs                      full
% 3.34/1.00  --res_backward_subs                     full
% 3.34/1.00  --res_forward_subs_resolution           true
% 3.34/1.00  --res_backward_subs_resolution          true
% 3.34/1.00  --res_orphan_elimination                true
% 3.34/1.00  --res_time_limit                        2.
% 3.34/1.00  --res_out_proof                         true
% 3.34/1.00  
% 3.34/1.00  ------ Superposition Options
% 3.34/1.00  
% 3.34/1.00  --superposition_flag                    true
% 3.34/1.00  --sup_passive_queue_type                priority_queues
% 3.34/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.34/1.00  --demod_completeness_check              fast
% 3.34/1.00  --demod_use_ground                      true
% 3.34/1.00  --sup_to_prop_solver                    passive
% 3.34/1.00  --sup_prop_simpl_new                    true
% 3.34/1.00  --sup_prop_simpl_given                  true
% 3.34/1.00  --sup_fun_splitting                     false
% 3.34/1.00  --sup_smt_interval                      50000
% 3.34/1.00  
% 3.34/1.00  ------ Superposition Simplification Setup
% 3.34/1.00  
% 3.34/1.00  --sup_indices_passive                   []
% 3.34/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/1.00  --sup_full_bw                           [BwDemod]
% 3.34/1.00  --sup_immed_triv                        [TrivRules]
% 3.34/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/1.00  --sup_immed_bw_main                     []
% 3.34/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/1.00  
% 3.34/1.00  ------ Combination Options
% 3.34/1.00  
% 3.34/1.00  --comb_res_mult                         3
% 3.34/1.00  --comb_sup_mult                         2
% 3.34/1.00  --comb_inst_mult                        10
% 3.34/1.00  
% 3.34/1.00  ------ Debug Options
% 3.34/1.00  
% 3.34/1.00  --dbg_backtrace                         false
% 3.34/1.00  --dbg_dump_prop_clauses                 false
% 3.34/1.00  --dbg_dump_prop_clauses_file            -
% 3.34/1.00  --dbg_out_stat                          false
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  ------ Proving...
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  % SZS status Theorem for theBenchmark.p
% 3.34/1.00  
% 3.34/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.34/1.00  
% 3.34/1.00  fof(f20,conjecture,(
% 3.34/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f21,negated_conjecture,(
% 3.34/1.01    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 3.34/1.01    inference(negated_conjecture,[],[f20])).
% 3.34/1.01  
% 3.34/1.01  fof(f43,plain,(
% 3.34/1.01    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 3.34/1.01    inference(ennf_transformation,[],[f21])).
% 3.34/1.01  
% 3.34/1.01  fof(f44,plain,(
% 3.34/1.01    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 3.34/1.01    inference(flattening,[],[f43])).
% 3.34/1.01  
% 3.34/1.01  fof(f61,plain,(
% 3.34/1.01    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK7) != k7_partfun1(X0,X4,k1_funct_1(X3,sK7)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK7,X1))) )),
% 3.34/1.01    introduced(choice_axiom,[])).
% 3.34/1.01  
% 3.34/1.01  fof(f60,plain,(
% 3.34/1.01    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK6),X5) != k7_partfun1(X0,sK6,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK6)) & m1_subset_1(X5,X1)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK6))) )),
% 3.34/1.01    introduced(choice_axiom,[])).
% 3.34/1.01  
% 3.34/1.01  fof(f59,plain,(
% 3.34/1.01    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,sK5,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK5,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK5),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK5,X1,X2) & v1_funct_1(sK5))) )),
% 3.34/1.01    introduced(choice_axiom,[])).
% 3.34/1.01  
% 3.34/1.01  fof(f58,plain,(
% 3.34/1.01    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK3,sK4,sK2,X3,X4),X5) != k7_partfun1(sK2,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,X3),k1_relset_1(sK4,sK2,X4)) & m1_subset_1(X5,sK3)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & ~v1_xboole_0(sK4))),
% 3.34/1.01    introduced(choice_axiom,[])).
% 3.34/1.01  
% 3.34/1.01  fof(f62,plain,(
% 3.34/1.01    (((k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) & m1_subset_1(sK7,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)) & ~v1_xboole_0(sK4)),
% 3.34/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f44,f61,f60,f59,f58])).
% 3.34/1.01  
% 3.34/1.01  fof(f103,plain,(
% 3.34/1.01    m1_subset_1(sK7,sK3)),
% 3.34/1.01    inference(cnf_transformation,[],[f62])).
% 3.34/1.01  
% 3.34/1.01  fof(f6,axiom,(
% 3.34/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f24,plain,(
% 3.34/1.01    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.34/1.01    inference(ennf_transformation,[],[f6])).
% 3.34/1.01  
% 3.34/1.01  fof(f25,plain,(
% 3.34/1.01    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.34/1.01    inference(flattening,[],[f24])).
% 3.34/1.01  
% 3.34/1.01  fof(f73,plain,(
% 3.34/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.34/1.01    inference(cnf_transformation,[],[f25])).
% 3.34/1.01  
% 3.34/1.01  fof(f105,plain,(
% 3.34/1.01    k1_xboole_0 != sK3),
% 3.34/1.01    inference(cnf_transformation,[],[f62])).
% 3.34/1.01  
% 3.34/1.01  fof(f3,axiom,(
% 3.34/1.01    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f23,plain,(
% 3.34/1.01    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.34/1.01    inference(ennf_transformation,[],[f3])).
% 3.34/1.01  
% 3.34/1.01  fof(f68,plain,(
% 3.34/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.34/1.01    inference(cnf_transformation,[],[f23])).
% 3.34/1.01  
% 3.34/1.01  fof(f9,axiom,(
% 3.34/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f27,plain,(
% 3.34/1.01    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.34/1.01    inference(ennf_transformation,[],[f9])).
% 3.34/1.01  
% 3.34/1.01  fof(f28,plain,(
% 3.34/1.01    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.34/1.01    inference(flattening,[],[f27])).
% 3.34/1.01  
% 3.34/1.01  fof(f78,plain,(
% 3.34/1.01    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.34/1.01    inference(cnf_transformation,[],[f28])).
% 3.34/1.01  
% 3.34/1.01  fof(f100,plain,(
% 3.34/1.01    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.34/1.01    inference(cnf_transformation,[],[f62])).
% 3.34/1.01  
% 3.34/1.01  fof(f15,axiom,(
% 3.34/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f34,plain,(
% 3.34/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/1.01    inference(ennf_transformation,[],[f15])).
% 3.34/1.01  
% 3.34/1.01  fof(f85,plain,(
% 3.34/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/1.01    inference(cnf_transformation,[],[f34])).
% 3.34/1.01  
% 3.34/1.01  fof(f104,plain,(
% 3.34/1.01    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))),
% 3.34/1.01    inference(cnf_transformation,[],[f62])).
% 3.34/1.01  
% 3.34/1.01  fof(f102,plain,(
% 3.34/1.01    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))),
% 3.34/1.01    inference(cnf_transformation,[],[f62])).
% 3.34/1.01  
% 3.34/1.01  fof(f14,axiom,(
% 3.34/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f33,plain,(
% 3.34/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/1.01    inference(ennf_transformation,[],[f14])).
% 3.34/1.01  
% 3.34/1.01  fof(f84,plain,(
% 3.34/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/1.01    inference(cnf_transformation,[],[f33])).
% 3.34/1.01  
% 3.34/1.01  fof(f2,axiom,(
% 3.34/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f22,plain,(
% 3.34/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.34/1.01    inference(ennf_transformation,[],[f2])).
% 3.34/1.01  
% 3.34/1.01  fof(f49,plain,(
% 3.34/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.34/1.01    inference(nnf_transformation,[],[f22])).
% 3.34/1.01  
% 3.34/1.01  fof(f50,plain,(
% 3.34/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.34/1.01    inference(rectify,[],[f49])).
% 3.34/1.01  
% 3.34/1.01  fof(f51,plain,(
% 3.34/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.34/1.01    introduced(choice_axiom,[])).
% 3.34/1.01  
% 3.34/1.01  fof(f52,plain,(
% 3.34/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.34/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f50,f51])).
% 3.34/1.01  
% 3.34/1.01  fof(f65,plain,(
% 3.34/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.34/1.01    inference(cnf_transformation,[],[f52])).
% 3.34/1.01  
% 3.34/1.01  fof(f12,axiom,(
% 3.34/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f31,plain,(
% 3.34/1.01    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/1.01    inference(ennf_transformation,[],[f12])).
% 3.34/1.01  
% 3.34/1.01  fof(f81,plain,(
% 3.34/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/1.01    inference(cnf_transformation,[],[f31])).
% 3.34/1.01  
% 3.34/1.01  fof(f8,axiom,(
% 3.34/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f26,plain,(
% 3.34/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.34/1.01    inference(ennf_transformation,[],[f8])).
% 3.34/1.01  
% 3.34/1.01  fof(f56,plain,(
% 3.34/1.01    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.34/1.01    inference(nnf_transformation,[],[f26])).
% 3.34/1.01  
% 3.34/1.01  fof(f76,plain,(
% 3.34/1.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.34/1.01    inference(cnf_transformation,[],[f56])).
% 3.34/1.01  
% 3.34/1.01  fof(f11,axiom,(
% 3.34/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f30,plain,(
% 3.34/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/1.01    inference(ennf_transformation,[],[f11])).
% 3.34/1.01  
% 3.34/1.01  fof(f80,plain,(
% 3.34/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/1.01    inference(cnf_transformation,[],[f30])).
% 3.34/1.01  
% 3.34/1.01  fof(f4,axiom,(
% 3.34/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f53,plain,(
% 3.34/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.34/1.01    inference(nnf_transformation,[],[f4])).
% 3.34/1.01  
% 3.34/1.01  fof(f54,plain,(
% 3.34/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.34/1.01    inference(flattening,[],[f53])).
% 3.34/1.01  
% 3.34/1.01  fof(f71,plain,(
% 3.34/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.34/1.01    inference(cnf_transformation,[],[f54])).
% 3.34/1.01  
% 3.34/1.01  fof(f97,plain,(
% 3.34/1.01    ~v1_xboole_0(sK4)),
% 3.34/1.01    inference(cnf_transformation,[],[f62])).
% 3.34/1.01  
% 3.34/1.01  fof(f99,plain,(
% 3.34/1.01    v1_funct_2(sK5,sK3,sK4)),
% 3.34/1.01    inference(cnf_transformation,[],[f62])).
% 3.34/1.01  
% 3.34/1.01  fof(f1,axiom,(
% 3.34/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f45,plain,(
% 3.34/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.34/1.01    inference(nnf_transformation,[],[f1])).
% 3.34/1.01  
% 3.34/1.01  fof(f46,plain,(
% 3.34/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.34/1.01    inference(rectify,[],[f45])).
% 3.34/1.01  
% 3.34/1.01  fof(f47,plain,(
% 3.34/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.34/1.01    introduced(choice_axiom,[])).
% 3.34/1.01  
% 3.34/1.01  fof(f48,plain,(
% 3.34/1.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.34/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f47])).
% 3.34/1.01  
% 3.34/1.01  fof(f64,plain,(
% 3.34/1.01    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.34/1.01    inference(cnf_transformation,[],[f48])).
% 3.34/1.01  
% 3.34/1.01  fof(f10,axiom,(
% 3.34/1.01    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f29,plain,(
% 3.34/1.01    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.34/1.01    inference(ennf_transformation,[],[f10])).
% 3.34/1.01  
% 3.34/1.01  fof(f79,plain,(
% 3.34/1.01    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.34/1.01    inference(cnf_transformation,[],[f29])).
% 3.34/1.01  
% 3.34/1.01  fof(f17,axiom,(
% 3.34/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f37,plain,(
% 3.34/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/1.01    inference(ennf_transformation,[],[f17])).
% 3.34/1.01  
% 3.34/1.01  fof(f38,plain,(
% 3.34/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/1.01    inference(flattening,[],[f37])).
% 3.34/1.01  
% 3.34/1.01  fof(f57,plain,(
% 3.34/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/1.01    inference(nnf_transformation,[],[f38])).
% 3.34/1.01  
% 3.34/1.01  fof(f89,plain,(
% 3.34/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/1.01    inference(cnf_transformation,[],[f57])).
% 3.34/1.01  
% 3.34/1.01  fof(f5,axiom,(
% 3.34/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f72,plain,(
% 3.34/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.34/1.01    inference(cnf_transformation,[],[f5])).
% 3.34/1.01  
% 3.34/1.01  fof(f98,plain,(
% 3.34/1.01    v1_funct_1(sK5)),
% 3.34/1.01    inference(cnf_transformation,[],[f62])).
% 3.34/1.01  
% 3.34/1.01  fof(f82,plain,(
% 3.34/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/1.01    inference(cnf_transformation,[],[f31])).
% 3.34/1.01  
% 3.34/1.01  fof(f18,axiom,(
% 3.34/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)))),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f39,plain,(
% 3.34/1.01    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.34/1.01    inference(ennf_transformation,[],[f18])).
% 3.34/1.01  
% 3.34/1.01  fof(f40,plain,(
% 3.34/1.01    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.34/1.01    inference(flattening,[],[f39])).
% 3.34/1.01  
% 3.34/1.01  fof(f95,plain,(
% 3.34/1.01    ( ! [X2,X0,X1] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.34/1.01    inference(cnf_transformation,[],[f40])).
% 3.34/1.01  
% 3.34/1.01  fof(f101,plain,(
% 3.34/1.01    v1_funct_1(sK6)),
% 3.34/1.01    inference(cnf_transformation,[],[f62])).
% 3.34/1.01  
% 3.34/1.01  fof(f19,axiom,(
% 3.34/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f41,plain,(
% 3.34/1.01    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 3.34/1.01    inference(ennf_transformation,[],[f19])).
% 3.34/1.01  
% 3.34/1.01  fof(f42,plain,(
% 3.34/1.01    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 3.34/1.01    inference(flattening,[],[f41])).
% 3.34/1.01  
% 3.34/1.01  fof(f96,plain,(
% 3.34/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 3.34/1.01    inference(cnf_transformation,[],[f42])).
% 3.34/1.01  
% 3.34/1.01  fof(f106,plain,(
% 3.34/1.01    k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7))),
% 3.34/1.01    inference(cnf_transformation,[],[f62])).
% 3.34/1.01  
% 3.34/1.01  cnf(c_37,negated_conjecture,
% 3.34/1.01      ( m1_subset_1(sK7,sK3) ),
% 3.34/1.01      inference(cnf_transformation,[],[f103]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2295,plain,
% 3.34/1.01      ( m1_subset_1(sK7,sK3) = iProver_top ),
% 3.34/1.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_10,plain,
% 3.34/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.34/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2313,plain,
% 3.34/1.01      ( m1_subset_1(X0,X1) != iProver_top
% 3.34/1.01      | r2_hidden(X0,X1) = iProver_top
% 3.34/1.01      | v1_xboole_0(X1) = iProver_top ),
% 3.34/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_4737,plain,
% 3.34/1.01      ( r2_hidden(sK7,sK3) = iProver_top
% 3.34/1.01      | v1_xboole_0(sK3) = iProver_top ),
% 3.34/1.01      inference(superposition,[status(thm)],[c_2295,c_2313]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_50,plain,
% 3.34/1.01      ( m1_subset_1(sK7,sK3) = iProver_top ),
% 3.34/1.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_35,negated_conjecture,
% 3.34/1.01      ( k1_xboole_0 != sK3 ),
% 3.34/1.01      inference(cnf_transformation,[],[f105]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_5,plain,
% 3.34/1.01      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.34/1.01      inference(cnf_transformation,[],[f68]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2589,plain,
% 3.34/1.01      ( ~ v1_xboole_0(sK3) | k1_xboole_0 = sK3 ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2590,plain,
% 3.34/1.01      ( k1_xboole_0 = sK3 | v1_xboole_0(sK3) != iProver_top ),
% 3.34/1.01      inference(predicate_to_equality,[status(thm)],[c_2589]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2760,plain,
% 3.34/1.01      ( ~ m1_subset_1(X0,sK3) | r2_hidden(X0,sK3) | v1_xboole_0(sK3) ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_3215,plain,
% 3.34/1.01      ( ~ m1_subset_1(sK7,sK3) | r2_hidden(sK7,sK3) | v1_xboole_0(sK3) ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_2760]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_3216,plain,
% 3.34/1.01      ( m1_subset_1(sK7,sK3) != iProver_top
% 3.34/1.01      | r2_hidden(sK7,sK3) = iProver_top
% 3.34/1.01      | v1_xboole_0(sK3) = iProver_top ),
% 3.34/1.01      inference(predicate_to_equality,[status(thm)],[c_3215]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_5409,plain,
% 3.34/1.01      ( r2_hidden(sK7,sK3) = iProver_top ),
% 3.34/1.01      inference(global_propositional_subsumption,
% 3.34/1.01                [status(thm)],
% 3.34/1.01                [c_4737,c_50,c_35,c_2590,c_3216]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_15,plain,
% 3.34/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.34/1.01      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.34/1.01      | ~ v1_funct_1(X1)
% 3.34/1.01      | ~ v1_relat_1(X1) ),
% 3.34/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2310,plain,
% 3.34/1.01      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 3.34/1.01      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 3.34/1.01      | v1_funct_1(X1) != iProver_top
% 3.34/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.34/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_40,negated_conjecture,
% 3.34/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.34/1.01      inference(cnf_transformation,[],[f100]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2292,plain,
% 3.34/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.34/1.01      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_22,plain,
% 3.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.34/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2305,plain,
% 3.34/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.34/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.34/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_4061,plain,
% 3.34/1.01      ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
% 3.34/1.01      inference(superposition,[status(thm)],[c_2292,c_2305]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_36,negated_conjecture,
% 3.34/1.01      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
% 3.34/1.01      inference(cnf_transformation,[],[f104]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2296,plain,
% 3.34/1.01      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
% 3.34/1.01      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_4359,plain,
% 3.34/1.01      ( r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
% 3.34/1.01      inference(demodulation,[status(thm)],[c_4061,c_2296]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_38,negated_conjecture,
% 3.34/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
% 3.34/1.01      inference(cnf_transformation,[],[f102]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2294,plain,
% 3.34/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 3.34/1.01      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_21,plain,
% 3.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.34/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2306,plain,
% 3.34/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.34/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.34/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_4182,plain,
% 3.34/1.01      ( k1_relset_1(sK4,sK2,sK6) = k1_relat_1(sK6) ),
% 3.34/1.01      inference(superposition,[status(thm)],[c_2294,c_2306]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_4516,plain,
% 3.34/1.01      ( r1_tarski(k2_relat_1(sK5),k1_relat_1(sK6)) = iProver_top ),
% 3.34/1.01      inference(light_normalisation,[status(thm)],[c_4359,c_4182]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_4,plain,
% 3.34/1.01      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.34/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2318,plain,
% 3.34/1.01      ( r1_tarski(X0,X1) != iProver_top
% 3.34/1.01      | r2_hidden(X2,X0) != iProver_top
% 3.34/1.01      | r2_hidden(X2,X1) = iProver_top ),
% 3.34/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_5233,plain,
% 3.34/1.01      ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
% 3.34/1.01      | r2_hidden(X0,k1_relat_1(sK6)) = iProver_top ),
% 3.34/1.01      inference(superposition,[status(thm)],[c_4516,c_2318]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_9333,plain,
% 3.34/1.01      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 3.34/1.01      | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top
% 3.34/1.01      | v1_funct_1(sK5) != iProver_top
% 3.34/1.01      | v1_relat_1(sK5) != iProver_top ),
% 3.34/1.01      inference(superposition,[status(thm)],[c_2310,c_5233]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_19,plain,
% 3.34/1.01      ( v4_relat_1(X0,X1)
% 3.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.34/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_14,plain,
% 3.34/1.01      ( ~ v4_relat_1(X0,X1)
% 3.34/1.01      | r1_tarski(k1_relat_1(X0),X1)
% 3.34/1.01      | ~ v1_relat_1(X0) ),
% 3.34/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_551,plain,
% 3.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/1.01      | r1_tarski(k1_relat_1(X0),X1)
% 3.34/1.01      | ~ v1_relat_1(X0) ),
% 3.34/1.01      inference(resolution,[status(thm)],[c_19,c_14]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_17,plain,
% 3.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/1.01      | v1_relat_1(X0) ),
% 3.34/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_555,plain,
% 3.34/1.01      ( r1_tarski(k1_relat_1(X0),X1)
% 3.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.34/1.01      inference(global_propositional_subsumption,
% 3.34/1.01                [status(thm)],
% 3.34/1.01                [c_551,c_17]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_556,plain,
% 3.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/1.01      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.34/1.01      inference(renaming,[status(thm)],[c_555]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2287,plain,
% 3.34/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.34/1.01      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.34/1.01      inference(predicate_to_equality,[status(thm)],[c_556]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2730,plain,
% 3.34/1.01      ( r1_tarski(k1_relat_1(sK5),sK3) = iProver_top ),
% 3.34/1.01      inference(superposition,[status(thm)],[c_2292,c_2287]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_6,plain,
% 3.34/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.34/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2316,plain,
% 3.34/1.01      ( X0 = X1
% 3.34/1.01      | r1_tarski(X1,X0) != iProver_top
% 3.34/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.34/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_4773,plain,
% 3.34/1.01      ( k1_relat_1(sK5) = sK3
% 3.34/1.01      | r1_tarski(sK3,k1_relat_1(sK5)) != iProver_top ),
% 3.34/1.01      inference(superposition,[status(thm)],[c_2730,c_2316]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_43,negated_conjecture,
% 3.34/1.01      ( ~ v1_xboole_0(sK4) ),
% 3.34/1.01      inference(cnf_transformation,[],[f97]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_41,negated_conjecture,
% 3.34/1.01      ( v1_funct_2(sK5,sK3,sK4) ),
% 3.34/1.01      inference(cnf_transformation,[],[f99]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_46,plain,
% 3.34/1.01      ( v1_funct_2(sK5,sK3,sK4) = iProver_top ),
% 3.34/1.01      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_0,plain,
% 3.34/1.01      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.34/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_134,plain,
% 3.34/1.01      ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
% 3.34/1.01      | v1_xboole_0(k1_xboole_0) ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_1458,plain,
% 3.34/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.34/1.01      theory(equality) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2613,plain,
% 3.34/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK4) | sK4 != X0 ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_1458]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2615,plain,
% 3.34/1.01      ( v1_xboole_0(sK4)
% 3.34/1.01      | ~ v1_xboole_0(k1_xboole_0)
% 3.34/1.01      | sK4 != k1_xboole_0 ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_2613]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_16,plain,
% 3.34/1.01      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.34/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_3473,plain,
% 3.34/1.01      ( ~ r1_tarski(X0,sK0(X0)) | ~ r2_hidden(sK0(X0),X0) ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_16]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_3475,plain,
% 3.34/1.01      ( ~ r1_tarski(k1_xboole_0,sK0(k1_xboole_0))
% 3.34/1.01      | ~ r2_hidden(sK0(k1_xboole_0),k1_xboole_0) ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_3473]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_31,plain,
% 3.34/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.34/1.01      | k1_xboole_0 = X2 ),
% 3.34/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2298,plain,
% 3.34/1.01      ( k1_relset_1(X0,X1,X2) = X0
% 3.34/1.01      | k1_xboole_0 = X1
% 3.34/1.01      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.34/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.34/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_4617,plain,
% 3.34/1.01      ( k1_relset_1(sK3,sK4,sK5) = sK3
% 3.34/1.01      | sK4 = k1_xboole_0
% 3.34/1.01      | v1_funct_2(sK5,sK3,sK4) != iProver_top ),
% 3.34/1.01      inference(superposition,[status(thm)],[c_2292,c_2298]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_4183,plain,
% 3.34/1.01      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 3.34/1.01      inference(superposition,[status(thm)],[c_2292,c_2306]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_4621,plain,
% 3.34/1.01      ( k1_relat_1(sK5) = sK3
% 3.34/1.01      | sK4 = k1_xboole_0
% 3.34/1.01      | v1_funct_2(sK5,sK3,sK4) != iProver_top ),
% 3.34/1.01      inference(demodulation,[status(thm)],[c_4617,c_4183]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_9,plain,
% 3.34/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 3.34/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_5833,plain,
% 3.34/1.01      ( r1_tarski(k1_xboole_0,sK0(k1_xboole_0)) ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_5934,plain,
% 3.34/1.01      ( k1_relat_1(sK5) = sK3 ),
% 3.34/1.01      inference(global_propositional_subsumption,
% 3.34/1.01                [status(thm)],
% 3.34/1.01                [c_4773,c_43,c_46,c_134,c_2615,c_3475,c_4621,c_5833]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_9338,plain,
% 3.34/1.01      ( r2_hidden(X0,sK3) != iProver_top
% 3.34/1.01      | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top
% 3.34/1.01      | v1_funct_1(sK5) != iProver_top
% 3.34/1.01      | v1_relat_1(sK5) != iProver_top ),
% 3.34/1.01      inference(light_normalisation,[status(thm)],[c_9333,c_5934]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_42,negated_conjecture,
% 3.34/1.01      ( v1_funct_1(sK5) ),
% 3.34/1.01      inference(cnf_transformation,[],[f98]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_45,plain,
% 3.34/1.01      ( v1_funct_1(sK5) = iProver_top ),
% 3.34/1.01      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_47,plain,
% 3.34/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.34/1.01      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2610,plain,
% 3.34/1.01      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.34/1.01      | v1_relat_1(sK5) ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_17]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2611,plain,
% 3.34/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.34/1.01      | v1_relat_1(sK5) = iProver_top ),
% 3.34/1.01      inference(predicate_to_equality,[status(thm)],[c_2610]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_10129,plain,
% 3.34/1.01      ( r2_hidden(X0,sK3) != iProver_top
% 3.34/1.01      | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top ),
% 3.34/1.01      inference(global_propositional_subsumption,
% 3.34/1.01                [status(thm)],
% 3.34/1.01                [c_9338,c_45,c_47,c_2611]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_18,plain,
% 3.34/1.01      ( v5_relat_1(X0,X1)
% 3.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.34/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_32,plain,
% 3.34/1.01      ( ~ v5_relat_1(X0,X1)
% 3.34/1.01      | ~ r2_hidden(X2,k1_relat_1(X0))
% 3.34/1.01      | ~ v1_funct_1(X0)
% 3.34/1.01      | ~ v1_relat_1(X0)
% 3.34/1.01      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 3.34/1.01      inference(cnf_transformation,[],[f95]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_523,plain,
% 3.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/1.01      | ~ r2_hidden(X3,k1_relat_1(X0))
% 3.34/1.01      | ~ v1_funct_1(X0)
% 3.34/1.01      | ~ v1_relat_1(X0)
% 3.34/1.01      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.34/1.01      inference(resolution,[status(thm)],[c_18,c_32]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_527,plain,
% 3.34/1.01      ( ~ v1_funct_1(X0)
% 3.34/1.01      | ~ r2_hidden(X3,k1_relat_1(X0))
% 3.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/1.01      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.34/1.01      inference(global_propositional_subsumption,
% 3.34/1.01                [status(thm)],
% 3.34/1.01                [c_523,c_17]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_528,plain,
% 3.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/1.01      | ~ r2_hidden(X3,k1_relat_1(X0))
% 3.34/1.01      | ~ v1_funct_1(X0)
% 3.34/1.01      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.34/1.01      inference(renaming,[status(thm)],[c_527]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2288,plain,
% 3.34/1.01      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 3.34/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
% 3.34/1.01      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 3.34/1.01      | v1_funct_1(X1) != iProver_top ),
% 3.34/1.01      inference(predicate_to_equality,[status(thm)],[c_528]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_3328,plain,
% 3.34/1.01      ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
% 3.34/1.01      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.34/1.01      | v1_funct_1(sK6) != iProver_top ),
% 3.34/1.01      inference(superposition,[status(thm)],[c_2294,c_2288]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_39,negated_conjecture,
% 3.34/1.01      ( v1_funct_1(sK6) ),
% 3.34/1.01      inference(cnf_transformation,[],[f101]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_48,plain,
% 3.34/1.01      ( v1_funct_1(sK6) = iProver_top ),
% 3.34/1.01      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_3562,plain,
% 3.34/1.01      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.34/1.01      | k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0) ),
% 3.34/1.01      inference(global_propositional_subsumption,
% 3.34/1.01                [status(thm)],
% 3.34/1.01                [c_3328,c_48]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_3563,plain,
% 3.34/1.01      ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
% 3.34/1.01      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 3.34/1.01      inference(renaming,[status(thm)],[c_3562]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_10140,plain,
% 3.34/1.01      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 3.34/1.01      | r2_hidden(X0,sK3) != iProver_top ),
% 3.34/1.01      inference(superposition,[status(thm)],[c_10129,c_3563]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_10174,plain,
% 3.34/1.01      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 3.34/1.01      inference(superposition,[status(thm)],[c_5409,c_10140]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_33,plain,
% 3.34/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.34/1.01      | ~ m1_subset_1(X3,X1)
% 3.34/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 3.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/1.01      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
% 3.34/1.01      | ~ v1_funct_1(X4)
% 3.34/1.01      | ~ v1_funct_1(X0)
% 3.34/1.01      | v1_xboole_0(X2)
% 3.34/1.01      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 3.34/1.01      | k1_xboole_0 = X1 ),
% 3.34/1.01      inference(cnf_transformation,[],[f96]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2297,plain,
% 3.34/1.01      ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
% 3.34/1.01      | k1_xboole_0 = X0
% 3.34/1.01      | v1_funct_2(X3,X0,X1) != iProver_top
% 3.34/1.01      | m1_subset_1(X5,X0) != iProver_top
% 3.34/1.01      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.34/1.01      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.34/1.01      | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
% 3.34/1.01      | v1_funct_1(X4) != iProver_top
% 3.34/1.01      | v1_funct_1(X3) != iProver_top
% 3.34/1.01      | v1_xboole_0(X1) = iProver_top ),
% 3.34/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_3940,plain,
% 3.34/1.01      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 3.34/1.01      | sK3 = k1_xboole_0
% 3.34/1.01      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 3.34/1.01      | m1_subset_1(X0,sK3) != iProver_top
% 3.34/1.01      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 3.34/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.34/1.01      | v1_funct_1(sK6) != iProver_top
% 3.34/1.01      | v1_funct_1(sK5) != iProver_top
% 3.34/1.01      | v1_xboole_0(sK4) = iProver_top ),
% 3.34/1.01      inference(superposition,[status(thm)],[c_2296,c_2297]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_44,plain,
% 3.34/1.01      ( v1_xboole_0(sK4) != iProver_top ),
% 3.34/1.01      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_49,plain,
% 3.34/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 3.34/1.01      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_117,plain,
% 3.34/1.01      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_122,plain,
% 3.34/1.01      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.34/1.01      | k1_xboole_0 = k1_xboole_0 ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_1457,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2661,plain,
% 3.34/1.01      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_1457]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2662,plain,
% 3.34/1.01      ( sK3 != k1_xboole_0
% 3.34/1.01      | k1_xboole_0 = sK3
% 3.34/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_2661]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_4601,plain,
% 3.34/1.01      ( m1_subset_1(X0,sK3) != iProver_top
% 3.34/1.01      | k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0)) ),
% 3.34/1.01      inference(global_propositional_subsumption,
% 3.34/1.01                [status(thm)],
% 3.34/1.01                [c_3940,c_44,c_45,c_46,c_47,c_48,c_49,c_35,c_117,c_122,
% 3.34/1.01                 c_2662]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_4602,plain,
% 3.34/1.01      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 3.34/1.01      | m1_subset_1(X0,sK3) != iProver_top ),
% 3.34/1.01      inference(renaming,[status(thm)],[c_4601]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_4609,plain,
% 3.34/1.01      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 3.34/1.01      inference(superposition,[status(thm)],[c_2295,c_4602]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_34,negated_conjecture,
% 3.34/1.01      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) ),
% 3.34/1.01      inference(cnf_transformation,[],[f106]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_5318,plain,
% 3.34/1.01      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 3.34/1.01      inference(demodulation,[status(thm)],[c_4609,c_34]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(contradiction,plain,
% 3.34/1.01      ( $false ),
% 3.34/1.01      inference(minisat,[status(thm)],[c_10174,c_5318]) ).
% 3.34/1.01  
% 3.34/1.01  
% 3.34/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.34/1.01  
% 3.34/1.01  ------                               Statistics
% 3.34/1.01  
% 3.34/1.01  ------ General
% 3.34/1.01  
% 3.34/1.01  abstr_ref_over_cycles:                  0
% 3.34/1.01  abstr_ref_under_cycles:                 0
% 3.34/1.01  gc_basic_clause_elim:                   0
% 3.34/1.01  forced_gc_time:                         0
% 3.34/1.01  parsing_time:                           0.012
% 3.34/1.01  unif_index_cands_time:                  0.
% 3.34/1.01  unif_index_add_time:                    0.
% 3.34/1.01  orderings_time:                         0.
% 3.34/1.01  out_proof_time:                         0.014
% 3.34/1.01  total_time:                             0.299
% 3.34/1.01  num_of_symbols:                         58
% 3.34/1.01  num_of_terms:                           10320
% 3.34/1.01  
% 3.34/1.01  ------ Preprocessing
% 3.34/1.01  
% 3.34/1.01  num_of_splits:                          0
% 3.34/1.01  num_of_split_atoms:                     0
% 3.34/1.01  num_of_reused_defs:                     0
% 3.34/1.01  num_eq_ax_congr_red:                    22
% 3.34/1.01  num_of_sem_filtered_clauses:            1
% 3.34/1.01  num_of_subtypes:                        0
% 3.34/1.01  monotx_restored_types:                  0
% 3.34/1.01  sat_num_of_epr_types:                   0
% 3.34/1.01  sat_num_of_non_cyclic_types:            0
% 3.34/1.01  sat_guarded_non_collapsed_types:        0
% 3.34/1.01  num_pure_diseq_elim:                    0
% 3.34/1.01  simp_replaced_by:                       0
% 3.34/1.01  res_preprocessed:                       186
% 3.34/1.01  prep_upred:                             0
% 3.34/1.01  prep_unflattend:                        92
% 3.34/1.01  smt_new_axioms:                         0
% 3.34/1.01  pred_elim_cands:                        7
% 3.34/1.01  pred_elim:                              2
% 3.34/1.01  pred_elim_cl:                           3
% 3.34/1.01  pred_elim_cycles:                       6
% 3.34/1.01  merged_defs:                            8
% 3.34/1.01  merged_defs_ncl:                        0
% 3.34/1.01  bin_hyper_res:                          8
% 3.34/1.01  prep_cycles:                            4
% 3.34/1.01  pred_elim_time:                         0.015
% 3.34/1.01  splitting_time:                         0.
% 3.34/1.01  sem_filter_time:                        0.
% 3.34/1.01  monotx_time:                            0.002
% 3.34/1.01  subtype_inf_time:                       0.
% 3.34/1.01  
% 3.34/1.01  ------ Problem properties
% 3.34/1.01  
% 3.34/1.01  clauses:                                38
% 3.34/1.01  conjectures:                            10
% 3.34/1.01  epr:                                    14
% 3.34/1.01  horn:                                   29
% 3.34/1.01  ground:                                 10
% 3.34/1.01  unary:                                  12
% 3.34/1.01  binary:                                 12
% 3.34/1.01  lits:                                   93
% 3.34/1.01  lits_eq:                                18
% 3.34/1.01  fd_pure:                                0
% 3.34/1.01  fd_pseudo:                              0
% 3.34/1.01  fd_cond:                                5
% 3.34/1.01  fd_pseudo_cond:                         1
% 3.34/1.01  ac_symbols:                             0
% 3.34/1.01  
% 3.34/1.01  ------ Propositional Solver
% 3.34/1.01  
% 3.34/1.01  prop_solver_calls:                      28
% 3.34/1.01  prop_fast_solver_calls:                 1476
% 3.34/1.01  smt_solver_calls:                       0
% 3.34/1.01  smt_fast_solver_calls:                  0
% 3.34/1.01  prop_num_of_clauses:                    3491
% 3.34/1.01  prop_preprocess_simplified:             11056
% 3.34/1.01  prop_fo_subsumed:                       56
% 3.34/1.01  prop_solver_time:                       0.
% 3.34/1.01  smt_solver_time:                        0.
% 3.34/1.01  smt_fast_solver_time:                   0.
% 3.34/1.01  prop_fast_solver_time:                  0.
% 3.34/1.01  prop_unsat_core_time:                   0.
% 3.34/1.01  
% 3.34/1.01  ------ QBF
% 3.34/1.01  
% 3.34/1.01  qbf_q_res:                              0
% 3.34/1.01  qbf_num_tautologies:                    0
% 3.34/1.01  qbf_prep_cycles:                        0
% 3.34/1.01  
% 3.34/1.01  ------ BMC1
% 3.34/1.01  
% 3.34/1.01  bmc1_current_bound:                     -1
% 3.34/1.01  bmc1_last_solved_bound:                 -1
% 3.34/1.01  bmc1_unsat_core_size:                   -1
% 3.34/1.01  bmc1_unsat_core_parents_size:           -1
% 3.34/1.01  bmc1_merge_next_fun:                    0
% 3.34/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.34/1.01  
% 3.34/1.01  ------ Instantiation
% 3.34/1.01  
% 3.34/1.01  inst_num_of_clauses:                    1097
% 3.34/1.01  inst_num_in_passive:                    480
% 3.34/1.01  inst_num_in_active:                     438
% 3.34/1.01  inst_num_in_unprocessed:                181
% 3.34/1.01  inst_num_of_loops:                      560
% 3.34/1.01  inst_num_of_learning_restarts:          0
% 3.34/1.01  inst_num_moves_active_passive:          120
% 3.34/1.01  inst_lit_activity:                      0
% 3.34/1.01  inst_lit_activity_moves:                0
% 3.34/1.01  inst_num_tautologies:                   0
% 3.34/1.01  inst_num_prop_implied:                  0
% 3.34/1.01  inst_num_existing_simplified:           0
% 3.34/1.01  inst_num_eq_res_simplified:             0
% 3.34/1.01  inst_num_child_elim:                    0
% 3.34/1.01  inst_num_of_dismatching_blockings:      246
% 3.34/1.01  inst_num_of_non_proper_insts:           931
% 3.34/1.01  inst_num_of_duplicates:                 0
% 3.34/1.01  inst_inst_num_from_inst_to_res:         0
% 3.34/1.01  inst_dismatching_checking_time:         0.
% 3.34/1.01  
% 3.34/1.01  ------ Resolution
% 3.34/1.01  
% 3.34/1.01  res_num_of_clauses:                     0
% 3.34/1.01  res_num_in_passive:                     0
% 3.34/1.01  res_num_in_active:                      0
% 3.34/1.01  res_num_of_loops:                       190
% 3.34/1.01  res_forward_subset_subsumed:            107
% 3.34/1.01  res_backward_subset_subsumed:           8
% 3.34/1.01  res_forward_subsumed:                   0
% 3.34/1.01  res_backward_subsumed:                  0
% 3.34/1.01  res_forward_subsumption_resolution:     2
% 3.34/1.01  res_backward_subsumption_resolution:    0
% 3.34/1.01  res_clause_to_clause_subsumption:       511
% 3.34/1.01  res_orphan_elimination:                 0
% 3.34/1.01  res_tautology_del:                      96
% 3.34/1.01  res_num_eq_res_simplified:              0
% 3.34/1.01  res_num_sel_changes:                    0
% 3.34/1.01  res_moves_from_active_to_pass:          0
% 3.34/1.01  
% 3.34/1.01  ------ Superposition
% 3.34/1.01  
% 3.34/1.01  sup_time_total:                         0.
% 3.34/1.01  sup_time_generating:                    0.
% 3.34/1.01  sup_time_sim_full:                      0.
% 3.34/1.01  sup_time_sim_immed:                     0.
% 3.34/1.01  
% 3.34/1.01  sup_num_of_clauses:                     169
% 3.34/1.01  sup_num_in_active:                      103
% 3.34/1.01  sup_num_in_passive:                     66
% 3.34/1.01  sup_num_of_loops:                       111
% 3.34/1.01  sup_fw_superposition:                   115
% 3.34/1.01  sup_bw_superposition:                   54
% 3.34/1.01  sup_immediate_simplified:               15
% 3.34/1.01  sup_given_eliminated:                   1
% 3.34/1.01  comparisons_done:                       0
% 3.34/1.01  comparisons_avoided:                    3
% 3.34/1.01  
% 3.34/1.01  ------ Simplifications
% 3.34/1.01  
% 3.34/1.01  
% 3.34/1.01  sim_fw_subset_subsumed:                 8
% 3.34/1.01  sim_bw_subset_subsumed:                 1
% 3.34/1.01  sim_fw_subsumed:                        5
% 3.34/1.01  sim_bw_subsumed:                        0
% 3.34/1.01  sim_fw_subsumption_res:                 0
% 3.34/1.01  sim_bw_subsumption_res:                 0
% 3.34/1.01  sim_tautology_del:                      6
% 3.34/1.01  sim_eq_tautology_del:                   3
% 3.34/1.01  sim_eq_res_simp:                        0
% 3.34/1.01  sim_fw_demodulated:                     2
% 3.34/1.01  sim_bw_demodulated:                     9
% 3.34/1.01  sim_light_normalised:                   6
% 3.34/1.01  sim_joinable_taut:                      0
% 3.34/1.01  sim_joinable_simp:                      0
% 3.34/1.01  sim_ac_normalised:                      0
% 3.34/1.01  sim_smt_subsumption:                    0
% 3.34/1.01  
%------------------------------------------------------------------------------
