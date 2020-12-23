%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:55 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :  154 (1135 expanded)
%              Number of clauses        :   86 ( 374 expanded)
%              Number of leaves         :   18 ( 246 expanded)
%              Depth                    :   24
%              Number of atoms          :  572 (5053 expanded)
%              Number of equality atoms :  183 (1012 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f18,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f35,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f36,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f35])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK8
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X5,X0) )
        & r2_hidden(sK8,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK7,X5) != X4
              | ~ r2_hidden(X5,sK6)
              | ~ r2_hidden(X5,sK4) )
          & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6)) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ! [X5] :
        ( k1_funct_1(sK7,X5) != sK8
        | ~ r2_hidden(X5,sK6)
        | ~ r2_hidden(X5,sK4) )
    & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f36,f54,f53])).

fof(f81,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f55])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                          | ! [X5] :
                              ( ~ r2_hidden(X5,X1)
                              | ~ r2_hidden(k4_tarski(X5,X4),X3)
                              | ~ m1_subset_1(X5,X2) ) )
                        & ( ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X5,X4),X3)
                              & m1_subset_1(X5,X2) )
                          | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                          | ! [X5] :
                              ( ~ r2_hidden(X5,X1)
                              | ~ r2_hidden(k4_tarski(X5,X4),X3)
                              | ~ m1_subset_1(X5,X2) ) )
                        & ( ? [X6] :
                              ( r2_hidden(X6,X1)
                              & r2_hidden(k4_tarski(X6,X4),X3)
                              & m1_subset_1(X6,X2) )
                          | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X4,X3,X2,X1] :
      ( ? [X6] :
          ( r2_hidden(X6,X1)
          & r2_hidden(k4_tarski(X6,X4),X3)
          & m1_subset_1(X6,X2) )
     => ( r2_hidden(sK3(X1,X2,X3,X4),X1)
        & r2_hidden(k4_tarski(sK3(X1,X2,X3,X4),X4),X3)
        & m1_subset_1(sK3(X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                          | ! [X5] :
                              ( ~ r2_hidden(X5,X1)
                              | ~ r2_hidden(k4_tarski(X5,X4),X3)
                              | ~ m1_subset_1(X5,X2) ) )
                        & ( ( r2_hidden(sK3(X1,X2,X3,X4),X1)
                            & r2_hidden(k4_tarski(sK3(X1,X2,X3,X4),X4),X3)
                            & m1_subset_1(sK3(X1,X2,X3,X4),X2) )
                          | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f50,f51])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK3(X1,X2,X3,X4),X1)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
        & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
            & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f44,f45])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f84,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f70])).

fof(f80,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f55])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).

fof(f56,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f82,plain,(
    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f55])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK3(X1,X2,X3,X4),X2)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK3(X1,X2,X3,X4),X4),X3)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f83,plain,(
    ! [X5] :
      ( k1_funct_1(sK7,X5) != sK8
      | ~ r2_hidden(X5,sK6)
      | ~ r2_hidden(X5,sK4) ) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1068,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1076,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2265,plain,
    ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
    inference(superposition,[status(thm)],[c_1068,c_1076])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | r2_hidden(sK3(X4,X3,X2,X0),X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1073,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | r2_hidden(sK3(X4,X3,X2,X0),X4) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2664,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(X1,sK4,sK7,X0),X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2265,c_1073])).

cnf(c_29,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1334,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1515,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_relat_1(k2_zfmisc_1(sK4,sK5))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1334])).

cnf(c_1516,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1515])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1543,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1544,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1543])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1078,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2350,plain,
    ( v1_xboole_0(sK5) != iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1068,c_1078])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1079,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2741,plain,
    ( v1_xboole_0(sK4) != iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1068,c_1079])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1077,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2374,plain,
    ( m1_subset_1(k9_relat_1(sK7,X0),k1_zfmisc_1(sK5)) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2265,c_1077])).

cnf(c_2600,plain,
    ( m1_subset_1(k9_relat_1(sK7,X0),k1_zfmisc_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2374,c_29])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1086,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2760,plain,
    ( m1_subset_1(X0,sK5) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2600,c_1086])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1080,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK2(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_359,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_360,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK7))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_1066,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_360])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1090,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1452,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1066,c_1090])).

cnf(c_1838,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1452,c_29,c_1516,c_1544])).

cnf(c_2901,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1080,c_1838])).

cnf(c_3338,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(X1,sK4,sK7,X0),X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2664,c_29,c_1516,c_1544,c_2350,c_2741,c_2760,c_2901])).

cnf(c_25,negated_conjecture,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1069,plain,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | m1_subset_1(sK3(X4,X3,X2,X0),X3)
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1071,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(sK3(X4,X3,X2,X0),X3) = iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1572,plain,
    ( m1_subset_1(sK3(sK6,sK4,sK7,sK8),sK4) = iProver_top
    | m1_subset_1(sK8,sK5) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1069,c_1071])).

cnf(c_30,plain,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1344,plain,
    ( ~ m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(X0))
    | m1_subset_1(sK8,X0)
    | ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1470,plain,
    ( ~ m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5))
    | m1_subset_1(sK8,sK5)
    | ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_1344])).

cnf(c_1472,plain,
    ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5)) != iProver_top
    | m1_subset_1(sK8,sK5) = iProver_top
    | r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1470])).

cnf(c_1367,plain,
    ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,X0),k1_zfmisc_1(sK5))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1471,plain,
    ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_1367])).

cnf(c_1474,plain,
    ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5)) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1471])).

cnf(c_1784,plain,
    ( m1_subset_1(sK3(sK6,sK4,sK7,sK8),sK4) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1572,c_29,c_30,c_1472,c_1474])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1087,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1792,plain,
    ( r2_hidden(sK3(sK6,sK4,sK7,sK8),sK4) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1784,c_1087])).

cnf(c_2367,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2265,c_1069])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | r2_hidden(k4_tarski(sK3(X4,X3,X2,X0),X0),X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1072,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | r2_hidden(k4_tarski(sK3(X4,X3,X2,X0),X0),X2) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2375,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK3(X1,sK4,sK7,X0),X0),sK7) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2265,c_1072])).

cnf(c_7283,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK3(X1,sK4,sK7,X0),X0),sK7) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2375,c_29,c_1516,c_1544,c_2350,c_2741,c_2760,c_2901])).

cnf(c_13,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_374,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_27])).

cnf(c_375,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK7)
    | ~ v1_relat_1(sK7)
    | k1_funct_1(sK7,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_1065,plain,
    ( k1_funct_1(sK7,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_7297,plain,
    ( k1_funct_1(sK7,sK3(X0,sK4,sK7,X1)) = X1
    | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7283,c_1065])).

cnf(c_7373,plain,
    ( r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
    | k1_funct_1(sK7,sK3(X0,sK4,sK7,X1)) = X1
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7297,c_29,c_1516,c_1544])).

cnf(c_7374,plain,
    ( k1_funct_1(sK7,sK3(X0,sK4,sK7,X1)) = X1
    | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7373])).

cnf(c_7386,plain,
    ( k1_funct_1(sK7,sK3(sK6,sK4,sK7,sK8)) = sK8
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2367,c_7374])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1082,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK2(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2816,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1082,c_1090])).

cnf(c_7043,plain,
    ( v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2367,c_2816])).

cnf(c_7503,plain,
    ( k1_funct_1(sK7,sK3(sK6,sK4,sK7,sK8)) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7386,c_29,c_1516,c_1544,c_7043])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | ~ r2_hidden(X0,sK6)
    | k1_funct_1(sK7,X0) != sK8 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1070,plain,
    ( k1_funct_1(sK7,X0) != sK8
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_7509,plain,
    ( r2_hidden(sK3(sK6,sK4,sK7,sK8),sK4) != iProver_top
    | r2_hidden(sK3(sK6,sK4,sK7,sK8),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_7503,c_1070])).

cnf(c_7539,plain,
    ( r2_hidden(sK3(sK6,sK4,sK7,sK8),sK6) != iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1792,c_7509])).

cnf(c_7293,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_7283,c_1090])).

cnf(c_7731,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7293,c_29,c_1516,c_1544,c_2901])).

cnf(c_7743,plain,
    ( v1_xboole_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2367,c_7731])).

cnf(c_7915,plain,
    ( r2_hidden(sK3(sK6,sK4,sK7,sK8),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7539,c_29,c_1516,c_1544,c_2350,c_2741,c_7043,c_7743])).

cnf(c_7920,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3338,c_7915])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7920,c_7043,c_2367,c_1544,c_1516,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:11:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.57/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.00  
% 2.57/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.57/1.00  
% 2.57/1.00  ------  iProver source info
% 2.57/1.00  
% 2.57/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.57/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.57/1.00  git: non_committed_changes: false
% 2.57/1.00  git: last_make_outside_of_git: false
% 2.57/1.00  
% 2.57/1.00  ------ 
% 2.57/1.00  
% 2.57/1.00  ------ Input Options
% 2.57/1.00  
% 2.57/1.00  --out_options                           all
% 2.57/1.00  --tptp_safe_out                         true
% 2.57/1.00  --problem_path                          ""
% 2.57/1.00  --include_path                          ""
% 2.57/1.00  --clausifier                            res/vclausify_rel
% 2.57/1.00  --clausifier_options                    --mode clausify
% 2.57/1.00  --stdin                                 false
% 2.57/1.00  --stats_out                             all
% 2.57/1.00  
% 2.57/1.00  ------ General Options
% 2.57/1.00  
% 2.57/1.00  --fof                                   false
% 2.57/1.00  --time_out_real                         305.
% 2.57/1.00  --time_out_virtual                      -1.
% 2.57/1.00  --symbol_type_check                     false
% 2.57/1.00  --clausify_out                          false
% 2.57/1.00  --sig_cnt_out                           false
% 2.57/1.00  --trig_cnt_out                          false
% 2.57/1.00  --trig_cnt_out_tolerance                1.
% 2.57/1.00  --trig_cnt_out_sk_spl                   false
% 2.57/1.00  --abstr_cl_out                          false
% 2.57/1.00  
% 2.57/1.00  ------ Global Options
% 2.57/1.00  
% 2.57/1.00  --schedule                              default
% 2.57/1.00  --add_important_lit                     false
% 2.57/1.00  --prop_solver_per_cl                    1000
% 2.57/1.00  --min_unsat_core                        false
% 2.57/1.00  --soft_assumptions                      false
% 2.57/1.00  --soft_lemma_size                       3
% 2.57/1.00  --prop_impl_unit_size                   0
% 2.57/1.00  --prop_impl_unit                        []
% 2.57/1.00  --share_sel_clauses                     true
% 2.57/1.00  --reset_solvers                         false
% 2.57/1.00  --bc_imp_inh                            [conj_cone]
% 2.57/1.00  --conj_cone_tolerance                   3.
% 2.57/1.00  --extra_neg_conj                        none
% 2.57/1.00  --large_theory_mode                     true
% 2.57/1.00  --prolific_symb_bound                   200
% 2.57/1.00  --lt_threshold                          2000
% 2.57/1.00  --clause_weak_htbl                      true
% 2.57/1.00  --gc_record_bc_elim                     false
% 2.57/1.00  
% 2.57/1.00  ------ Preprocessing Options
% 2.57/1.00  
% 2.57/1.00  --preprocessing_flag                    true
% 2.57/1.00  --time_out_prep_mult                    0.1
% 2.57/1.00  --splitting_mode                        input
% 2.57/1.00  --splitting_grd                         true
% 2.57/1.00  --splitting_cvd                         false
% 2.57/1.00  --splitting_cvd_svl                     false
% 2.57/1.00  --splitting_nvd                         32
% 2.57/1.00  --sub_typing                            true
% 2.57/1.00  --prep_gs_sim                           true
% 2.57/1.00  --prep_unflatten                        true
% 2.57/1.00  --prep_res_sim                          true
% 2.57/1.00  --prep_upred                            true
% 2.57/1.00  --prep_sem_filter                       exhaustive
% 2.57/1.00  --prep_sem_filter_out                   false
% 2.57/1.00  --pred_elim                             true
% 2.57/1.00  --res_sim_input                         true
% 2.57/1.00  --eq_ax_congr_red                       true
% 2.57/1.00  --pure_diseq_elim                       true
% 2.57/1.00  --brand_transform                       false
% 2.57/1.00  --non_eq_to_eq                          false
% 2.57/1.00  --prep_def_merge                        true
% 2.57/1.00  --prep_def_merge_prop_impl              false
% 2.57/1.00  --prep_def_merge_mbd                    true
% 2.57/1.00  --prep_def_merge_tr_red                 false
% 2.57/1.00  --prep_def_merge_tr_cl                  false
% 2.57/1.00  --smt_preprocessing                     true
% 2.57/1.00  --smt_ac_axioms                         fast
% 2.57/1.00  --preprocessed_out                      false
% 2.57/1.00  --preprocessed_stats                    false
% 2.57/1.00  
% 2.57/1.00  ------ Abstraction refinement Options
% 2.57/1.00  
% 2.57/1.00  --abstr_ref                             []
% 2.57/1.00  --abstr_ref_prep                        false
% 2.57/1.00  --abstr_ref_until_sat                   false
% 2.57/1.00  --abstr_ref_sig_restrict                funpre
% 2.57/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.57/1.00  --abstr_ref_under                       []
% 2.57/1.00  
% 2.57/1.00  ------ SAT Options
% 2.57/1.00  
% 2.57/1.00  --sat_mode                              false
% 2.57/1.00  --sat_fm_restart_options                ""
% 2.57/1.00  --sat_gr_def                            false
% 2.57/1.00  --sat_epr_types                         true
% 2.57/1.00  --sat_non_cyclic_types                  false
% 2.57/1.00  --sat_finite_models                     false
% 2.57/1.00  --sat_fm_lemmas                         false
% 2.57/1.00  --sat_fm_prep                           false
% 2.57/1.00  --sat_fm_uc_incr                        true
% 2.57/1.00  --sat_out_model                         small
% 2.57/1.00  --sat_out_clauses                       false
% 2.57/1.00  
% 2.57/1.00  ------ QBF Options
% 2.57/1.00  
% 2.57/1.00  --qbf_mode                              false
% 2.57/1.00  --qbf_elim_univ                         false
% 2.57/1.00  --qbf_dom_inst                          none
% 2.57/1.00  --qbf_dom_pre_inst                      false
% 2.57/1.00  --qbf_sk_in                             false
% 2.57/1.00  --qbf_pred_elim                         true
% 2.57/1.00  --qbf_split                             512
% 2.57/1.00  
% 2.57/1.00  ------ BMC1 Options
% 2.57/1.00  
% 2.57/1.00  --bmc1_incremental                      false
% 2.57/1.00  --bmc1_axioms                           reachable_all
% 2.57/1.00  --bmc1_min_bound                        0
% 2.57/1.00  --bmc1_max_bound                        -1
% 2.57/1.00  --bmc1_max_bound_default                -1
% 2.57/1.00  --bmc1_symbol_reachability              true
% 2.57/1.00  --bmc1_property_lemmas                  false
% 2.57/1.00  --bmc1_k_induction                      false
% 2.57/1.00  --bmc1_non_equiv_states                 false
% 2.57/1.00  --bmc1_deadlock                         false
% 2.57/1.00  --bmc1_ucm                              false
% 2.57/1.00  --bmc1_add_unsat_core                   none
% 2.57/1.00  --bmc1_unsat_core_children              false
% 2.57/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.57/1.00  --bmc1_out_stat                         full
% 2.57/1.00  --bmc1_ground_init                      false
% 2.57/1.00  --bmc1_pre_inst_next_state              false
% 2.57/1.00  --bmc1_pre_inst_state                   false
% 2.57/1.00  --bmc1_pre_inst_reach_state             false
% 2.57/1.00  --bmc1_out_unsat_core                   false
% 2.57/1.00  --bmc1_aig_witness_out                  false
% 2.57/1.00  --bmc1_verbose                          false
% 2.57/1.00  --bmc1_dump_clauses_tptp                false
% 2.57/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.57/1.00  --bmc1_dump_file                        -
% 2.57/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.57/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.57/1.00  --bmc1_ucm_extend_mode                  1
% 2.57/1.00  --bmc1_ucm_init_mode                    2
% 2.57/1.00  --bmc1_ucm_cone_mode                    none
% 2.57/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.57/1.00  --bmc1_ucm_relax_model                  4
% 2.57/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.57/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.57/1.00  --bmc1_ucm_layered_model                none
% 2.57/1.00  --bmc1_ucm_max_lemma_size               10
% 2.57/1.00  
% 2.57/1.00  ------ AIG Options
% 2.57/1.00  
% 2.57/1.00  --aig_mode                              false
% 2.57/1.00  
% 2.57/1.00  ------ Instantiation Options
% 2.57/1.00  
% 2.57/1.00  --instantiation_flag                    true
% 2.57/1.00  --inst_sos_flag                         false
% 2.57/1.00  --inst_sos_phase                        true
% 2.57/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.57/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.57/1.00  --inst_lit_sel_side                     num_symb
% 2.57/1.00  --inst_solver_per_active                1400
% 2.57/1.00  --inst_solver_calls_frac                1.
% 2.57/1.00  --inst_passive_queue_type               priority_queues
% 2.57/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.57/1.00  --inst_passive_queues_freq              [25;2]
% 2.57/1.00  --inst_dismatching                      true
% 2.57/1.00  --inst_eager_unprocessed_to_passive     true
% 2.57/1.00  --inst_prop_sim_given                   true
% 2.57/1.00  --inst_prop_sim_new                     false
% 2.57/1.00  --inst_subs_new                         false
% 2.57/1.00  --inst_eq_res_simp                      false
% 2.57/1.00  --inst_subs_given                       false
% 2.57/1.00  --inst_orphan_elimination               true
% 2.57/1.00  --inst_learning_loop_flag               true
% 2.57/1.00  --inst_learning_start                   3000
% 2.57/1.00  --inst_learning_factor                  2
% 2.57/1.00  --inst_start_prop_sim_after_learn       3
% 2.57/1.00  --inst_sel_renew                        solver
% 2.57/1.00  --inst_lit_activity_flag                true
% 2.57/1.00  --inst_restr_to_given                   false
% 2.57/1.00  --inst_activity_threshold               500
% 2.57/1.00  --inst_out_proof                        true
% 2.57/1.00  
% 2.57/1.00  ------ Resolution Options
% 2.57/1.00  
% 2.57/1.00  --resolution_flag                       true
% 2.57/1.00  --res_lit_sel                           adaptive
% 2.57/1.00  --res_lit_sel_side                      none
% 2.57/1.00  --res_ordering                          kbo
% 2.57/1.00  --res_to_prop_solver                    active
% 2.57/1.00  --res_prop_simpl_new                    false
% 2.57/1.00  --res_prop_simpl_given                  true
% 2.57/1.00  --res_passive_queue_type                priority_queues
% 2.57/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.57/1.00  --res_passive_queues_freq               [15;5]
% 2.57/1.00  --res_forward_subs                      full
% 2.57/1.00  --res_backward_subs                     full
% 2.57/1.00  --res_forward_subs_resolution           true
% 2.57/1.00  --res_backward_subs_resolution          true
% 2.57/1.00  --res_orphan_elimination                true
% 2.57/1.00  --res_time_limit                        2.
% 2.57/1.00  --res_out_proof                         true
% 2.57/1.00  
% 2.57/1.00  ------ Superposition Options
% 2.57/1.00  
% 2.57/1.00  --superposition_flag                    true
% 2.57/1.00  --sup_passive_queue_type                priority_queues
% 2.57/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.57/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.57/1.00  --demod_completeness_check              fast
% 2.57/1.00  --demod_use_ground                      true
% 2.57/1.00  --sup_to_prop_solver                    passive
% 2.57/1.00  --sup_prop_simpl_new                    true
% 2.57/1.00  --sup_prop_simpl_given                  true
% 2.57/1.00  --sup_fun_splitting                     false
% 2.57/1.00  --sup_smt_interval                      50000
% 2.57/1.00  
% 2.57/1.00  ------ Superposition Simplification Setup
% 2.57/1.00  
% 2.57/1.00  --sup_indices_passive                   []
% 2.57/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.57/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/1.00  --sup_full_bw                           [BwDemod]
% 2.57/1.00  --sup_immed_triv                        [TrivRules]
% 2.57/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.57/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/1.00  --sup_immed_bw_main                     []
% 2.57/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.57/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.57/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.57/1.00  
% 2.57/1.00  ------ Combination Options
% 2.57/1.00  
% 2.57/1.00  --comb_res_mult                         3
% 2.57/1.00  --comb_sup_mult                         2
% 2.57/1.00  --comb_inst_mult                        10
% 2.57/1.00  
% 2.57/1.00  ------ Debug Options
% 2.57/1.00  
% 2.57/1.00  --dbg_backtrace                         false
% 2.57/1.00  --dbg_dump_prop_clauses                 false
% 2.57/1.00  --dbg_dump_prop_clauses_file            -
% 2.57/1.00  --dbg_out_stat                          false
% 2.57/1.00  ------ Parsing...
% 2.57/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.57/1.00  
% 2.57/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.57/1.00  
% 2.57/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.57/1.00  
% 2.57/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.57/1.00  ------ Proving...
% 2.57/1.00  ------ Problem Properties 
% 2.57/1.00  
% 2.57/1.00  
% 2.57/1.00  clauses                                 27
% 2.57/1.00  conjectures                             3
% 2.57/1.00  EPR                                     2
% 2.57/1.00  Horn                                    20
% 2.57/1.00  unary                                   3
% 2.57/1.00  binary                                  6
% 2.57/1.00  lits                                    89
% 2.57/1.00  lits eq                                 3
% 2.57/1.00  fd_pure                                 0
% 2.57/1.00  fd_pseudo                               0
% 2.57/1.00  fd_cond                                 0
% 2.57/1.00  fd_pseudo_cond                          1
% 2.57/1.00  AC symbols                              0
% 2.57/1.00  
% 2.57/1.00  ------ Schedule dynamic 5 is on 
% 2.57/1.00  
% 2.57/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.57/1.00  
% 2.57/1.00  
% 2.57/1.00  ------ 
% 2.57/1.00  Current options:
% 2.57/1.00  ------ 
% 2.57/1.00  
% 2.57/1.00  ------ Input Options
% 2.57/1.00  
% 2.57/1.00  --out_options                           all
% 2.57/1.00  --tptp_safe_out                         true
% 2.57/1.00  --problem_path                          ""
% 2.57/1.00  --include_path                          ""
% 2.57/1.00  --clausifier                            res/vclausify_rel
% 2.57/1.00  --clausifier_options                    --mode clausify
% 2.57/1.00  --stdin                                 false
% 2.57/1.00  --stats_out                             all
% 2.57/1.00  
% 2.57/1.00  ------ General Options
% 2.57/1.00  
% 2.57/1.00  --fof                                   false
% 2.57/1.00  --time_out_real                         305.
% 2.57/1.00  --time_out_virtual                      -1.
% 2.57/1.00  --symbol_type_check                     false
% 2.57/1.00  --clausify_out                          false
% 2.57/1.00  --sig_cnt_out                           false
% 2.57/1.00  --trig_cnt_out                          false
% 2.57/1.00  --trig_cnt_out_tolerance                1.
% 2.57/1.00  --trig_cnt_out_sk_spl                   false
% 2.57/1.00  --abstr_cl_out                          false
% 2.57/1.00  
% 2.57/1.00  ------ Global Options
% 2.57/1.00  
% 2.57/1.00  --schedule                              default
% 2.57/1.00  --add_important_lit                     false
% 2.57/1.00  --prop_solver_per_cl                    1000
% 2.57/1.00  --min_unsat_core                        false
% 2.57/1.00  --soft_assumptions                      false
% 2.57/1.00  --soft_lemma_size                       3
% 2.57/1.00  --prop_impl_unit_size                   0
% 2.57/1.00  --prop_impl_unit                        []
% 2.57/1.00  --share_sel_clauses                     true
% 2.57/1.00  --reset_solvers                         false
% 2.57/1.00  --bc_imp_inh                            [conj_cone]
% 2.57/1.00  --conj_cone_tolerance                   3.
% 2.57/1.00  --extra_neg_conj                        none
% 2.57/1.00  --large_theory_mode                     true
% 2.57/1.00  --prolific_symb_bound                   200
% 2.57/1.00  --lt_threshold                          2000
% 2.57/1.00  --clause_weak_htbl                      true
% 2.57/1.00  --gc_record_bc_elim                     false
% 2.57/1.00  
% 2.57/1.00  ------ Preprocessing Options
% 2.57/1.00  
% 2.57/1.00  --preprocessing_flag                    true
% 2.57/1.00  --time_out_prep_mult                    0.1
% 2.57/1.00  --splitting_mode                        input
% 2.57/1.00  --splitting_grd                         true
% 2.57/1.00  --splitting_cvd                         false
% 2.57/1.00  --splitting_cvd_svl                     false
% 2.57/1.00  --splitting_nvd                         32
% 2.57/1.00  --sub_typing                            true
% 2.57/1.00  --prep_gs_sim                           true
% 2.57/1.00  --prep_unflatten                        true
% 2.57/1.00  --prep_res_sim                          true
% 2.57/1.00  --prep_upred                            true
% 2.57/1.00  --prep_sem_filter                       exhaustive
% 2.57/1.00  --prep_sem_filter_out                   false
% 2.57/1.00  --pred_elim                             true
% 2.57/1.00  --res_sim_input                         true
% 2.57/1.00  --eq_ax_congr_red                       true
% 2.57/1.00  --pure_diseq_elim                       true
% 2.57/1.00  --brand_transform                       false
% 2.57/1.00  --non_eq_to_eq                          false
% 2.57/1.00  --prep_def_merge                        true
% 2.57/1.00  --prep_def_merge_prop_impl              false
% 2.57/1.00  --prep_def_merge_mbd                    true
% 2.57/1.00  --prep_def_merge_tr_red                 false
% 2.57/1.00  --prep_def_merge_tr_cl                  false
% 2.57/1.00  --smt_preprocessing                     true
% 2.57/1.00  --smt_ac_axioms                         fast
% 2.57/1.00  --preprocessed_out                      false
% 2.57/1.00  --preprocessed_stats                    false
% 2.57/1.00  
% 2.57/1.00  ------ Abstraction refinement Options
% 2.57/1.00  
% 2.57/1.00  --abstr_ref                             []
% 2.57/1.00  --abstr_ref_prep                        false
% 2.57/1.00  --abstr_ref_until_sat                   false
% 2.57/1.00  --abstr_ref_sig_restrict                funpre
% 2.57/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.57/1.00  --abstr_ref_under                       []
% 2.57/1.00  
% 2.57/1.00  ------ SAT Options
% 2.57/1.00  
% 2.57/1.00  --sat_mode                              false
% 2.57/1.00  --sat_fm_restart_options                ""
% 2.57/1.01  --sat_gr_def                            false
% 2.57/1.01  --sat_epr_types                         true
% 2.57/1.01  --sat_non_cyclic_types                  false
% 2.57/1.01  --sat_finite_models                     false
% 2.57/1.01  --sat_fm_lemmas                         false
% 2.57/1.01  --sat_fm_prep                           false
% 2.57/1.01  --sat_fm_uc_incr                        true
% 2.57/1.01  --sat_out_model                         small
% 2.57/1.01  --sat_out_clauses                       false
% 2.57/1.01  
% 2.57/1.01  ------ QBF Options
% 2.57/1.01  
% 2.57/1.01  --qbf_mode                              false
% 2.57/1.01  --qbf_elim_univ                         false
% 2.57/1.01  --qbf_dom_inst                          none
% 2.57/1.01  --qbf_dom_pre_inst                      false
% 2.57/1.01  --qbf_sk_in                             false
% 2.57/1.01  --qbf_pred_elim                         true
% 2.57/1.01  --qbf_split                             512
% 2.57/1.01  
% 2.57/1.01  ------ BMC1 Options
% 2.57/1.01  
% 2.57/1.01  --bmc1_incremental                      false
% 2.57/1.01  --bmc1_axioms                           reachable_all
% 2.57/1.01  --bmc1_min_bound                        0
% 2.57/1.01  --bmc1_max_bound                        -1
% 2.57/1.01  --bmc1_max_bound_default                -1
% 2.57/1.01  --bmc1_symbol_reachability              true
% 2.57/1.01  --bmc1_property_lemmas                  false
% 2.57/1.01  --bmc1_k_induction                      false
% 2.57/1.01  --bmc1_non_equiv_states                 false
% 2.57/1.01  --bmc1_deadlock                         false
% 2.57/1.01  --bmc1_ucm                              false
% 2.57/1.01  --bmc1_add_unsat_core                   none
% 2.57/1.01  --bmc1_unsat_core_children              false
% 2.57/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.57/1.01  --bmc1_out_stat                         full
% 2.57/1.01  --bmc1_ground_init                      false
% 2.57/1.01  --bmc1_pre_inst_next_state              false
% 2.57/1.01  --bmc1_pre_inst_state                   false
% 2.57/1.01  --bmc1_pre_inst_reach_state             false
% 2.57/1.01  --bmc1_out_unsat_core                   false
% 2.57/1.01  --bmc1_aig_witness_out                  false
% 2.57/1.01  --bmc1_verbose                          false
% 2.57/1.01  --bmc1_dump_clauses_tptp                false
% 2.57/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.57/1.01  --bmc1_dump_file                        -
% 2.57/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.57/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.57/1.01  --bmc1_ucm_extend_mode                  1
% 2.57/1.01  --bmc1_ucm_init_mode                    2
% 2.57/1.01  --bmc1_ucm_cone_mode                    none
% 2.57/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.57/1.01  --bmc1_ucm_relax_model                  4
% 2.57/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.57/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.57/1.01  --bmc1_ucm_layered_model                none
% 2.57/1.01  --bmc1_ucm_max_lemma_size               10
% 2.57/1.01  
% 2.57/1.01  ------ AIG Options
% 2.57/1.01  
% 2.57/1.01  --aig_mode                              false
% 2.57/1.01  
% 2.57/1.01  ------ Instantiation Options
% 2.57/1.01  
% 2.57/1.01  --instantiation_flag                    true
% 2.57/1.01  --inst_sos_flag                         false
% 2.57/1.01  --inst_sos_phase                        true
% 2.57/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.57/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.57/1.01  --inst_lit_sel_side                     none
% 2.57/1.01  --inst_solver_per_active                1400
% 2.57/1.01  --inst_solver_calls_frac                1.
% 2.57/1.01  --inst_passive_queue_type               priority_queues
% 2.57/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.57/1.01  --inst_passive_queues_freq              [25;2]
% 2.57/1.01  --inst_dismatching                      true
% 2.57/1.01  --inst_eager_unprocessed_to_passive     true
% 2.57/1.01  --inst_prop_sim_given                   true
% 2.57/1.01  --inst_prop_sim_new                     false
% 2.57/1.01  --inst_subs_new                         false
% 2.57/1.01  --inst_eq_res_simp                      false
% 2.57/1.01  --inst_subs_given                       false
% 2.57/1.01  --inst_orphan_elimination               true
% 2.57/1.01  --inst_learning_loop_flag               true
% 2.57/1.01  --inst_learning_start                   3000
% 2.57/1.01  --inst_learning_factor                  2
% 2.57/1.01  --inst_start_prop_sim_after_learn       3
% 2.57/1.01  --inst_sel_renew                        solver
% 2.57/1.01  --inst_lit_activity_flag                true
% 2.57/1.01  --inst_restr_to_given                   false
% 2.57/1.01  --inst_activity_threshold               500
% 2.57/1.01  --inst_out_proof                        true
% 2.57/1.01  
% 2.57/1.01  ------ Resolution Options
% 2.57/1.01  
% 2.57/1.01  --resolution_flag                       false
% 2.57/1.01  --res_lit_sel                           adaptive
% 2.57/1.01  --res_lit_sel_side                      none
% 2.57/1.01  --res_ordering                          kbo
% 2.57/1.01  --res_to_prop_solver                    active
% 2.57/1.01  --res_prop_simpl_new                    false
% 2.57/1.01  --res_prop_simpl_given                  true
% 2.57/1.01  --res_passive_queue_type                priority_queues
% 2.57/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.57/1.01  --res_passive_queues_freq               [15;5]
% 2.57/1.01  --res_forward_subs                      full
% 2.57/1.01  --res_backward_subs                     full
% 2.57/1.01  --res_forward_subs_resolution           true
% 2.57/1.01  --res_backward_subs_resolution          true
% 2.57/1.01  --res_orphan_elimination                true
% 2.57/1.01  --res_time_limit                        2.
% 2.57/1.01  --res_out_proof                         true
% 2.57/1.01  
% 2.57/1.01  ------ Superposition Options
% 2.57/1.01  
% 2.57/1.01  --superposition_flag                    true
% 2.57/1.01  --sup_passive_queue_type                priority_queues
% 2.57/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.57/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.57/1.01  --demod_completeness_check              fast
% 2.57/1.01  --demod_use_ground                      true
% 2.57/1.01  --sup_to_prop_solver                    passive
% 2.57/1.01  --sup_prop_simpl_new                    true
% 2.57/1.01  --sup_prop_simpl_given                  true
% 2.57/1.01  --sup_fun_splitting                     false
% 2.57/1.01  --sup_smt_interval                      50000
% 2.57/1.01  
% 2.57/1.01  ------ Superposition Simplification Setup
% 2.57/1.01  
% 2.57/1.01  --sup_indices_passive                   []
% 2.57/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.57/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/1.01  --sup_full_bw                           [BwDemod]
% 2.57/1.01  --sup_immed_triv                        [TrivRules]
% 2.57/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.57/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/1.01  --sup_immed_bw_main                     []
% 2.57/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.57/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.57/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.57/1.01  
% 2.57/1.01  ------ Combination Options
% 2.57/1.01  
% 2.57/1.01  --comb_res_mult                         3
% 2.57/1.01  --comb_sup_mult                         2
% 2.57/1.01  --comb_inst_mult                        10
% 2.57/1.01  
% 2.57/1.01  ------ Debug Options
% 2.57/1.01  
% 2.57/1.01  --dbg_backtrace                         false
% 2.57/1.01  --dbg_dump_prop_clauses                 false
% 2.57/1.01  --dbg_dump_prop_clauses_file            -
% 2.57/1.01  --dbg_out_stat                          false
% 2.57/1.01  
% 2.57/1.01  
% 2.57/1.01  
% 2.57/1.01  
% 2.57/1.01  ------ Proving...
% 2.57/1.01  
% 2.57/1.01  
% 2.57/1.01  % SZS status Theorem for theBenchmark.p
% 2.57/1.01  
% 2.57/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.57/1.01  
% 2.57/1.01  fof(f15,conjecture,(
% 2.57/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.57/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f16,negated_conjecture,(
% 2.57/1.01    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.57/1.01    inference(negated_conjecture,[],[f15])).
% 2.57/1.01  
% 2.57/1.01  fof(f18,plain,(
% 2.57/1.01    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.57/1.01    inference(pure_predicate_removal,[],[f16])).
% 2.57/1.01  
% 2.57/1.01  fof(f35,plain,(
% 2.57/1.01    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 2.57/1.01    inference(ennf_transformation,[],[f18])).
% 2.57/1.01  
% 2.57/1.01  fof(f36,plain,(
% 2.57/1.01    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 2.57/1.01    inference(flattening,[],[f35])).
% 2.57/1.01  
% 2.57/1.01  fof(f54,plain,(
% 2.57/1.01    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK8 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(sK8,k7_relset_1(X0,X1,X3,X2)))) )),
% 2.57/1.01    introduced(choice_axiom,[])).
% 2.57/1.01  
% 2.57/1.01  fof(f53,plain,(
% 2.57/1.01    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK7,X5) != X4 | ~r2_hidden(X5,sK6) | ~r2_hidden(X5,sK4)) & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_1(sK7))),
% 2.57/1.01    introduced(choice_axiom,[])).
% 2.57/1.01  
% 2.57/1.01  fof(f55,plain,(
% 2.57/1.01    (! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~r2_hidden(X5,sK4)) & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_1(sK7)),
% 2.57/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f36,f54,f53])).
% 2.57/1.01  
% 2.57/1.01  fof(f81,plain,(
% 2.57/1.01    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 2.57/1.01    inference(cnf_transformation,[],[f55])).
% 2.57/1.01  
% 2.57/1.01  fof(f12,axiom,(
% 2.57/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.57/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f31,plain,(
% 2.57/1.01    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.57/1.01    inference(ennf_transformation,[],[f12])).
% 2.57/1.01  
% 2.57/1.01  fof(f74,plain,(
% 2.57/1.01    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.57/1.01    inference(cnf_transformation,[],[f31])).
% 2.57/1.01  
% 2.57/1.01  fof(f14,axiom,(
% 2.57/1.01    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 2.57/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f34,plain,(
% 2.57/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.57/1.01    inference(ennf_transformation,[],[f14])).
% 2.57/1.01  
% 2.57/1.01  fof(f49,plain,(
% 2.57/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.57/1.01    inference(nnf_transformation,[],[f34])).
% 2.57/1.01  
% 2.57/1.01  fof(f50,plain,(
% 2.57/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.57/1.01    inference(rectify,[],[f49])).
% 2.57/1.01  
% 2.57/1.01  fof(f51,plain,(
% 2.57/1.01    ! [X4,X3,X2,X1] : (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) => (r2_hidden(sK3(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK3(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK3(X1,X2,X3,X4),X2)))),
% 2.57/1.01    introduced(choice_axiom,[])).
% 2.57/1.01  
% 2.57/1.01  fof(f52,plain,(
% 2.57/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & ((r2_hidden(sK3(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK3(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK3(X1,X2,X3,X4),X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.57/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f50,f51])).
% 2.57/1.01  
% 2.57/1.01  fof(f78,plain,(
% 2.57/1.01    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK3(X1,X2,X3,X4),X1) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.57/1.01    inference(cnf_transformation,[],[f52])).
% 2.57/1.01  
% 2.57/1.01  fof(f5,axiom,(
% 2.57/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.57/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f24,plain,(
% 2.57/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.57/1.01    inference(ennf_transformation,[],[f5])).
% 2.57/1.01  
% 2.57/1.01  fof(f62,plain,(
% 2.57/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.57/1.01    inference(cnf_transformation,[],[f24])).
% 2.57/1.01  
% 2.57/1.01  fof(f6,axiom,(
% 2.57/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.57/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f63,plain,(
% 2.57/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.57/1.01    inference(cnf_transformation,[],[f6])).
% 2.57/1.01  
% 2.57/1.01  fof(f10,axiom,(
% 2.57/1.01    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.57/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f29,plain,(
% 2.57/1.01    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.57/1.01    inference(ennf_transformation,[],[f10])).
% 2.57/1.01  
% 2.57/1.01  fof(f72,plain,(
% 2.57/1.01    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 2.57/1.01    inference(cnf_transformation,[],[f29])).
% 2.57/1.01  
% 2.57/1.01  fof(f9,axiom,(
% 2.57/1.01    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 2.57/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f28,plain,(
% 2.57/1.01    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.57/1.01    inference(ennf_transformation,[],[f9])).
% 2.57/1.01  
% 2.57/1.01  fof(f71,plain,(
% 2.57/1.01    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.57/1.01    inference(cnf_transformation,[],[f28])).
% 2.57/1.01  
% 2.57/1.01  fof(f11,axiom,(
% 2.57/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 2.57/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f30,plain,(
% 2.57/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.57/1.01    inference(ennf_transformation,[],[f11])).
% 2.57/1.01  
% 2.57/1.01  fof(f73,plain,(
% 2.57/1.01    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.57/1.01    inference(cnf_transformation,[],[f30])).
% 2.57/1.01  
% 2.57/1.01  fof(f4,axiom,(
% 2.57/1.01    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.57/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f22,plain,(
% 2.57/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.57/1.01    inference(ennf_transformation,[],[f4])).
% 2.57/1.01  
% 2.57/1.01  fof(f23,plain,(
% 2.57/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.57/1.01    inference(flattening,[],[f22])).
% 2.57/1.01  
% 2.57/1.01  fof(f61,plain,(
% 2.57/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.57/1.01    inference(cnf_transformation,[],[f23])).
% 2.57/1.01  
% 2.57/1.01  fof(f7,axiom,(
% 2.57/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 2.57/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f25,plain,(
% 2.57/1.01    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 2.57/1.01    inference(ennf_transformation,[],[f7])).
% 2.57/1.01  
% 2.57/1.01  fof(f43,plain,(
% 2.57/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.57/1.01    inference(nnf_transformation,[],[f25])).
% 2.57/1.01  
% 2.57/1.01  fof(f44,plain,(
% 2.57/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.57/1.01    inference(rectify,[],[f43])).
% 2.57/1.01  
% 2.57/1.01  fof(f45,plain,(
% 2.57/1.01    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))))),
% 2.57/1.01    introduced(choice_axiom,[])).
% 2.57/1.01  
% 2.57/1.01  fof(f46,plain,(
% 2.57/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.57/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f44,f45])).
% 2.57/1.01  
% 2.57/1.01  fof(f64,plain,(
% 2.57/1.01    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.57/1.01    inference(cnf_transformation,[],[f46])).
% 2.57/1.01  
% 2.57/1.01  fof(f8,axiom,(
% 2.57/1.01    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 2.57/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f26,plain,(
% 2.57/1.01    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.57/1.01    inference(ennf_transformation,[],[f8])).
% 2.57/1.01  
% 2.57/1.01  fof(f27,plain,(
% 2.57/1.01    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.57/1.01    inference(flattening,[],[f26])).
% 2.57/1.01  
% 2.57/1.01  fof(f47,plain,(
% 2.57/1.01    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.57/1.01    inference(nnf_transformation,[],[f27])).
% 2.57/1.01  
% 2.57/1.01  fof(f48,plain,(
% 2.57/1.01    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.57/1.01    inference(flattening,[],[f47])).
% 2.57/1.01  
% 2.57/1.01  fof(f70,plain,(
% 2.57/1.01    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.57/1.01    inference(cnf_transformation,[],[f48])).
% 2.57/1.01  
% 2.57/1.01  fof(f84,plain,(
% 2.57/1.01    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.57/1.01    inference(equality_resolution,[],[f70])).
% 2.57/1.01  
% 2.57/1.01  fof(f80,plain,(
% 2.57/1.01    v1_funct_1(sK7)),
% 2.57/1.01    inference(cnf_transformation,[],[f55])).
% 2.57/1.01  
% 2.57/1.01  fof(f1,axiom,(
% 2.57/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.57/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f37,plain,(
% 2.57/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.57/1.01    inference(nnf_transformation,[],[f1])).
% 2.57/1.01  
% 2.57/1.01  fof(f38,plain,(
% 2.57/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.57/1.01    inference(rectify,[],[f37])).
% 2.57/1.01  
% 2.57/1.01  fof(f39,plain,(
% 2.57/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.57/1.01    introduced(choice_axiom,[])).
% 2.57/1.01  
% 2.57/1.01  fof(f40,plain,(
% 2.57/1.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.57/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).
% 2.57/1.01  
% 2.57/1.01  fof(f56,plain,(
% 2.57/1.01    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.57/1.01    inference(cnf_transformation,[],[f40])).
% 2.57/1.01  
% 2.57/1.01  fof(f82,plain,(
% 2.57/1.01    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))),
% 2.57/1.01    inference(cnf_transformation,[],[f55])).
% 2.57/1.01  
% 2.57/1.01  fof(f76,plain,(
% 2.57/1.01    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK3(X1,X2,X3,X4),X2) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.57/1.01    inference(cnf_transformation,[],[f52])).
% 2.57/1.01  
% 2.57/1.01  fof(f3,axiom,(
% 2.57/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.57/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f20,plain,(
% 2.57/1.01    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.57/1.01    inference(ennf_transformation,[],[f3])).
% 2.57/1.01  
% 2.57/1.01  fof(f21,plain,(
% 2.57/1.01    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.57/1.01    inference(flattening,[],[f20])).
% 2.57/1.01  
% 2.57/1.01  fof(f60,plain,(
% 2.57/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.57/1.01    inference(cnf_transformation,[],[f21])).
% 2.57/1.01  
% 2.57/1.01  fof(f77,plain,(
% 2.57/1.01    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK3(X1,X2,X3,X4),X4),X3) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.57/1.01    inference(cnf_transformation,[],[f52])).
% 2.57/1.01  
% 2.57/1.01  fof(f69,plain,(
% 2.57/1.01    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.57/1.01    inference(cnf_transformation,[],[f48])).
% 2.57/1.01  
% 2.57/1.01  fof(f66,plain,(
% 2.57/1.01    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.57/1.01    inference(cnf_transformation,[],[f46])).
% 2.57/1.01  
% 2.57/1.01  fof(f83,plain,(
% 2.57/1.01    ( ! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~r2_hidden(X5,sK4)) )),
% 2.57/1.01    inference(cnf_transformation,[],[f55])).
% 2.57/1.01  
% 2.57/1.01  cnf(c_26,negated_conjecture,
% 2.57/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 2.57/1.01      inference(cnf_transformation,[],[f81]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1068,plain,
% 2.57/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_18,plain,
% 2.57/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.57/1.01      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.57/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1076,plain,
% 2.57/1.01      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.57/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2265,plain,
% 2.57/1.01      ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_1068,c_1076]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_21,plain,
% 2.57/1.01      ( ~ m1_subset_1(X0,X1)
% 2.57/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 2.57/1.01      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 2.57/1.01      | r2_hidden(sK3(X4,X3,X2,X0),X4)
% 2.57/1.01      | v1_xboole_0(X1)
% 2.57/1.01      | v1_xboole_0(X3)
% 2.57/1.01      | v1_xboole_0(X4) ),
% 2.57/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1073,plain,
% 2.57/1.01      ( m1_subset_1(X0,X1) != iProver_top
% 2.57/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 2.57/1.01      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 2.57/1.01      | r2_hidden(sK3(X4,X3,X2,X0),X4) = iProver_top
% 2.57/1.01      | v1_xboole_0(X1) = iProver_top
% 2.57/1.01      | v1_xboole_0(X3) = iProver_top
% 2.57/1.01      | v1_xboole_0(X4) = iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2664,plain,
% 2.57/1.01      ( m1_subset_1(X0,sK5) != iProver_top
% 2.57/1.01      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 2.57/1.01      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 2.57/1.01      | r2_hidden(sK3(X1,sK4,sK7,X0),X1) = iProver_top
% 2.57/1.01      | v1_xboole_0(X1) = iProver_top
% 2.57/1.01      | v1_xboole_0(sK5) = iProver_top
% 2.57/1.01      | v1_xboole_0(sK4) = iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_2265,c_1073]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_29,plain,
% 2.57/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_6,plain,
% 2.57/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.57/1.01      | ~ v1_relat_1(X1)
% 2.57/1.01      | v1_relat_1(X0) ),
% 2.57/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1334,plain,
% 2.57/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.57/1.01      | v1_relat_1(X0)
% 2.57/1.01      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.57/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1515,plain,
% 2.57/1.01      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 2.57/1.01      | ~ v1_relat_1(k2_zfmisc_1(sK4,sK5))
% 2.57/1.01      | v1_relat_1(sK7) ),
% 2.57/1.01      inference(instantiation,[status(thm)],[c_1334]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1516,plain,
% 2.57/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 2.57/1.01      | v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
% 2.57/1.01      | v1_relat_1(sK7) = iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_1515]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_7,plain,
% 2.57/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.57/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1543,plain,
% 2.57/1.01      ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
% 2.57/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1544,plain,
% 2.57/1.01      ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_1543]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_16,plain,
% 2.57/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.57/1.01      | ~ v1_xboole_0(X2)
% 2.57/1.01      | v1_xboole_0(X0) ),
% 2.57/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1078,plain,
% 2.57/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.57/1.01      | v1_xboole_0(X2) != iProver_top
% 2.57/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2350,plain,
% 2.57/1.01      ( v1_xboole_0(sK5) != iProver_top
% 2.57/1.01      | v1_xboole_0(sK7) = iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_1068,c_1078]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_15,plain,
% 2.57/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.57/1.01      | ~ v1_xboole_0(X1)
% 2.57/1.01      | v1_xboole_0(X0) ),
% 2.57/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1079,plain,
% 2.57/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.57/1.01      | v1_xboole_0(X1) != iProver_top
% 2.57/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2741,plain,
% 2.57/1.01      ( v1_xboole_0(sK4) != iProver_top
% 2.57/1.01      | v1_xboole_0(sK7) = iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_1068,c_1079]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_17,plain,
% 2.57/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.57/1.01      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
% 2.57/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1077,plain,
% 2.57/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.57/1.01      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2374,plain,
% 2.57/1.01      ( m1_subset_1(k9_relat_1(sK7,X0),k1_zfmisc_1(sK5)) = iProver_top
% 2.57/1.01      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_2265,c_1077]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2600,plain,
% 2.57/1.01      ( m1_subset_1(k9_relat_1(sK7,X0),k1_zfmisc_1(sK5)) = iProver_top ),
% 2.57/1.01      inference(global_propositional_subsumption,
% 2.57/1.01                [status(thm)],
% 2.57/1.01                [c_2374,c_29]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_5,plain,
% 2.57/1.01      ( m1_subset_1(X0,X1)
% 2.57/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.57/1.01      | ~ r2_hidden(X0,X2) ),
% 2.57/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1086,plain,
% 2.57/1.01      ( m1_subset_1(X0,X1) = iProver_top
% 2.57/1.01      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.57/1.01      | r2_hidden(X0,X2) != iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2760,plain,
% 2.57/1.01      ( m1_subset_1(X0,sK5) = iProver_top
% 2.57/1.01      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_2600,c_1086]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_11,plain,
% 2.57/1.01      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.57/1.01      | r2_hidden(sK2(X0,X2,X1),k1_relat_1(X1))
% 2.57/1.01      | ~ v1_relat_1(X1) ),
% 2.57/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1080,plain,
% 2.57/1.01      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 2.57/1.01      | r2_hidden(sK2(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 2.57/1.01      | v1_relat_1(X1) != iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_12,plain,
% 2.57/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.57/1.01      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 2.57/1.01      | ~ v1_funct_1(X1)
% 2.57/1.01      | ~ v1_relat_1(X1) ),
% 2.57/1.01      inference(cnf_transformation,[],[f84]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_27,negated_conjecture,
% 2.57/1.01      ( v1_funct_1(sK7) ),
% 2.57/1.01      inference(cnf_transformation,[],[f80]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_359,plain,
% 2.57/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.57/1.01      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 2.57/1.01      | ~ v1_relat_1(X1)
% 2.57/1.01      | sK7 != X1 ),
% 2.57/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_360,plain,
% 2.57/1.01      ( ~ r2_hidden(X0,k1_relat_1(sK7))
% 2.57/1.01      | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7)
% 2.57/1.01      | ~ v1_relat_1(sK7) ),
% 2.57/1.01      inference(unflattening,[status(thm)],[c_359]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1066,plain,
% 2.57/1.01      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 2.57/1.01      | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top
% 2.57/1.01      | v1_relat_1(sK7) != iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_360]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1,plain,
% 2.57/1.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.57/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1090,plain,
% 2.57/1.01      ( r2_hidden(X0,X1) != iProver_top
% 2.57/1.01      | v1_xboole_0(X1) != iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1452,plain,
% 2.57/1.01      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 2.57/1.01      | v1_relat_1(sK7) != iProver_top
% 2.57/1.01      | v1_xboole_0(sK7) != iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_1066,c_1090]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1838,plain,
% 2.57/1.01      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 2.57/1.01      | v1_xboole_0(sK7) != iProver_top ),
% 2.57/1.01      inference(global_propositional_subsumption,
% 2.57/1.01                [status(thm)],
% 2.57/1.01                [c_1452,c_29,c_1516,c_1544]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2901,plain,
% 2.57/1.01      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 2.57/1.01      | v1_relat_1(sK7) != iProver_top
% 2.57/1.01      | v1_xboole_0(sK7) != iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_1080,c_1838]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_3338,plain,
% 2.57/1.01      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 2.57/1.01      | r2_hidden(sK3(X1,sK4,sK7,X0),X1) = iProver_top
% 2.57/1.01      | v1_xboole_0(X1) = iProver_top ),
% 2.57/1.01      inference(global_propositional_subsumption,
% 2.57/1.01                [status(thm)],
% 2.57/1.01                [c_2664,c_29,c_1516,c_1544,c_2350,c_2741,c_2760,c_2901]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_25,negated_conjecture,
% 2.57/1.01      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
% 2.57/1.01      inference(cnf_transformation,[],[f82]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1069,plain,
% 2.57/1.01      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_23,plain,
% 2.57/1.01      ( ~ m1_subset_1(X0,X1)
% 2.57/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 2.57/1.01      | m1_subset_1(sK3(X4,X3,X2,X0),X3)
% 2.57/1.01      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 2.57/1.01      | v1_xboole_0(X1)
% 2.57/1.01      | v1_xboole_0(X3)
% 2.57/1.01      | v1_xboole_0(X4) ),
% 2.57/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1071,plain,
% 2.57/1.01      ( m1_subset_1(X0,X1) != iProver_top
% 2.57/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 2.57/1.01      | m1_subset_1(sK3(X4,X3,X2,X0),X3) = iProver_top
% 2.57/1.01      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 2.57/1.01      | v1_xboole_0(X1) = iProver_top
% 2.57/1.01      | v1_xboole_0(X3) = iProver_top
% 2.57/1.01      | v1_xboole_0(X4) = iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1572,plain,
% 2.57/1.01      ( m1_subset_1(sK3(sK6,sK4,sK7,sK8),sK4) = iProver_top
% 2.57/1.01      | m1_subset_1(sK8,sK5) != iProver_top
% 2.57/1.01      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 2.57/1.01      | v1_xboole_0(sK5) = iProver_top
% 2.57/1.01      | v1_xboole_0(sK4) = iProver_top
% 2.57/1.01      | v1_xboole_0(sK6) = iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_1069,c_1071]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_30,plain,
% 2.57/1.01      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1344,plain,
% 2.57/1.01      ( ~ m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(X0))
% 2.57/1.01      | m1_subset_1(sK8,X0)
% 2.57/1.01      | ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
% 2.57/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1470,plain,
% 2.57/1.01      ( ~ m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5))
% 2.57/1.01      | m1_subset_1(sK8,sK5)
% 2.57/1.01      | ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
% 2.57/1.01      inference(instantiation,[status(thm)],[c_1344]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1472,plain,
% 2.57/1.01      ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5)) != iProver_top
% 2.57/1.01      | m1_subset_1(sK8,sK5) = iProver_top
% 2.57/1.01      | r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) != iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_1470]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1367,plain,
% 2.57/1.01      ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,X0),k1_zfmisc_1(sK5))
% 2.57/1.01      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 2.57/1.01      inference(instantiation,[status(thm)],[c_17]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1471,plain,
% 2.57/1.01      ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5))
% 2.57/1.01      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 2.57/1.01      inference(instantiation,[status(thm)],[c_1367]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1474,plain,
% 2.57/1.01      ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5)) = iProver_top
% 2.57/1.01      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_1471]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1784,plain,
% 2.57/1.01      ( m1_subset_1(sK3(sK6,sK4,sK7,sK8),sK4) = iProver_top
% 2.57/1.01      | v1_xboole_0(sK5) = iProver_top
% 2.57/1.01      | v1_xboole_0(sK4) = iProver_top
% 2.57/1.01      | v1_xboole_0(sK6) = iProver_top ),
% 2.57/1.01      inference(global_propositional_subsumption,
% 2.57/1.01                [status(thm)],
% 2.57/1.01                [c_1572,c_29,c_30,c_1472,c_1474]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_4,plain,
% 2.57/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.57/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1087,plain,
% 2.57/1.01      ( m1_subset_1(X0,X1) != iProver_top
% 2.57/1.01      | r2_hidden(X0,X1) = iProver_top
% 2.57/1.01      | v1_xboole_0(X1) = iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1792,plain,
% 2.57/1.01      ( r2_hidden(sK3(sK6,sK4,sK7,sK8),sK4) = iProver_top
% 2.57/1.01      | v1_xboole_0(sK5) = iProver_top
% 2.57/1.01      | v1_xboole_0(sK4) = iProver_top
% 2.57/1.01      | v1_xboole_0(sK6) = iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_1784,c_1087]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2367,plain,
% 2.57/1.01      ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
% 2.57/1.01      inference(demodulation,[status(thm)],[c_2265,c_1069]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_22,plain,
% 2.57/1.01      ( ~ m1_subset_1(X0,X1)
% 2.57/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 2.57/1.01      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 2.57/1.01      | r2_hidden(k4_tarski(sK3(X4,X3,X2,X0),X0),X2)
% 2.57/1.01      | v1_xboole_0(X1)
% 2.57/1.01      | v1_xboole_0(X3)
% 2.57/1.01      | v1_xboole_0(X4) ),
% 2.57/1.01      inference(cnf_transformation,[],[f77]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1072,plain,
% 2.57/1.01      ( m1_subset_1(X0,X1) != iProver_top
% 2.57/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 2.57/1.01      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 2.57/1.01      | r2_hidden(k4_tarski(sK3(X4,X3,X2,X0),X0),X2) = iProver_top
% 2.57/1.01      | v1_xboole_0(X1) = iProver_top
% 2.57/1.01      | v1_xboole_0(X3) = iProver_top
% 2.57/1.01      | v1_xboole_0(X4) = iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2375,plain,
% 2.57/1.01      ( m1_subset_1(X0,sK5) != iProver_top
% 2.57/1.01      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 2.57/1.01      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 2.57/1.01      | r2_hidden(k4_tarski(sK3(X1,sK4,sK7,X0),X0),sK7) = iProver_top
% 2.57/1.01      | v1_xboole_0(X1) = iProver_top
% 2.57/1.01      | v1_xboole_0(sK5) = iProver_top
% 2.57/1.01      | v1_xboole_0(sK4) = iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_2265,c_1072]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_7283,plain,
% 2.57/1.01      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 2.57/1.01      | r2_hidden(k4_tarski(sK3(X1,sK4,sK7,X0),X0),sK7) = iProver_top
% 2.57/1.01      | v1_xboole_0(X1) = iProver_top ),
% 2.57/1.01      inference(global_propositional_subsumption,
% 2.57/1.01                [status(thm)],
% 2.57/1.01                [c_2375,c_29,c_1516,c_1544,c_2350,c_2741,c_2760,c_2901]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_13,plain,
% 2.57/1.01      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 2.57/1.01      | ~ v1_funct_1(X2)
% 2.57/1.01      | ~ v1_relat_1(X2)
% 2.57/1.01      | k1_funct_1(X2,X0) = X1 ),
% 2.57/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_374,plain,
% 2.57/1.01      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 2.57/1.01      | ~ v1_relat_1(X2)
% 2.57/1.01      | k1_funct_1(X2,X0) = X1
% 2.57/1.01      | sK7 != X2 ),
% 2.57/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_27]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_375,plain,
% 2.57/1.01      ( ~ r2_hidden(k4_tarski(X0,X1),sK7)
% 2.57/1.01      | ~ v1_relat_1(sK7)
% 2.57/1.01      | k1_funct_1(sK7,X0) = X1 ),
% 2.57/1.01      inference(unflattening,[status(thm)],[c_374]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1065,plain,
% 2.57/1.01      ( k1_funct_1(sK7,X0) = X1
% 2.57/1.01      | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
% 2.57/1.01      | v1_relat_1(sK7) != iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_375]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_7297,plain,
% 2.57/1.01      ( k1_funct_1(sK7,sK3(X0,sK4,sK7,X1)) = X1
% 2.57/1.01      | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
% 2.57/1.01      | v1_relat_1(sK7) != iProver_top
% 2.57/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_7283,c_1065]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_7373,plain,
% 2.57/1.01      ( r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
% 2.57/1.01      | k1_funct_1(sK7,sK3(X0,sK4,sK7,X1)) = X1
% 2.57/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.57/1.01      inference(global_propositional_subsumption,
% 2.57/1.01                [status(thm)],
% 2.57/1.01                [c_7297,c_29,c_1516,c_1544]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_7374,plain,
% 2.57/1.01      ( k1_funct_1(sK7,sK3(X0,sK4,sK7,X1)) = X1
% 2.57/1.01      | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
% 2.57/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.57/1.01      inference(renaming,[status(thm)],[c_7373]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_7386,plain,
% 2.57/1.01      ( k1_funct_1(sK7,sK3(sK6,sK4,sK7,sK8)) = sK8
% 2.57/1.01      | v1_xboole_0(sK6) = iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_2367,c_7374]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_9,plain,
% 2.57/1.01      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.57/1.01      | r2_hidden(sK2(X0,X2,X1),X2)
% 2.57/1.01      | ~ v1_relat_1(X1) ),
% 2.57/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1082,plain,
% 2.57/1.01      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 2.57/1.01      | r2_hidden(sK2(X0,X2,X1),X2) = iProver_top
% 2.57/1.01      | v1_relat_1(X1) != iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2816,plain,
% 2.57/1.01      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 2.57/1.01      | v1_relat_1(X1) != iProver_top
% 2.57/1.01      | v1_xboole_0(X2) != iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_1082,c_1090]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_7043,plain,
% 2.57/1.01      ( v1_relat_1(sK7) != iProver_top
% 2.57/1.01      | v1_xboole_0(sK6) != iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_2367,c_2816]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_7503,plain,
% 2.57/1.01      ( k1_funct_1(sK7,sK3(sK6,sK4,sK7,sK8)) = sK8 ),
% 2.57/1.01      inference(global_propositional_subsumption,
% 2.57/1.01                [status(thm)],
% 2.57/1.01                [c_7386,c_29,c_1516,c_1544,c_7043]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_24,negated_conjecture,
% 2.57/1.01      ( ~ r2_hidden(X0,sK4)
% 2.57/1.01      | ~ r2_hidden(X0,sK6)
% 2.57/1.01      | k1_funct_1(sK7,X0) != sK8 ),
% 2.57/1.01      inference(cnf_transformation,[],[f83]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1070,plain,
% 2.57/1.01      ( k1_funct_1(sK7,X0) != sK8
% 2.57/1.01      | r2_hidden(X0,sK4) != iProver_top
% 2.57/1.01      | r2_hidden(X0,sK6) != iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_7509,plain,
% 2.57/1.01      ( r2_hidden(sK3(sK6,sK4,sK7,sK8),sK4) != iProver_top
% 2.57/1.01      | r2_hidden(sK3(sK6,sK4,sK7,sK8),sK6) != iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_7503,c_1070]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_7539,plain,
% 2.57/1.01      ( r2_hidden(sK3(sK6,sK4,sK7,sK8),sK6) != iProver_top
% 2.57/1.01      | v1_xboole_0(sK5) = iProver_top
% 2.57/1.01      | v1_xboole_0(sK4) = iProver_top
% 2.57/1.01      | v1_xboole_0(sK6) = iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_1792,c_7509]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_7293,plain,
% 2.57/1.01      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 2.57/1.01      | v1_xboole_0(X1) = iProver_top
% 2.57/1.01      | v1_xboole_0(sK7) != iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_7283,c_1090]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_7731,plain,
% 2.57/1.01      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 2.57/1.01      | v1_xboole_0(sK7) != iProver_top ),
% 2.57/1.01      inference(global_propositional_subsumption,
% 2.57/1.01                [status(thm)],
% 2.57/1.01                [c_7293,c_29,c_1516,c_1544,c_2901]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_7743,plain,
% 2.57/1.01      ( v1_xboole_0(sK7) != iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_2367,c_7731]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_7915,plain,
% 2.57/1.01      ( r2_hidden(sK3(sK6,sK4,sK7,sK8),sK6) != iProver_top ),
% 2.57/1.01      inference(global_propositional_subsumption,
% 2.57/1.01                [status(thm)],
% 2.57/1.01                [c_7539,c_29,c_1516,c_1544,c_2350,c_2741,c_7043,c_7743]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_7920,plain,
% 2.57/1.01      ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
% 2.57/1.01      | v1_xboole_0(sK6) = iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_3338,c_7915]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(contradiction,plain,
% 2.57/1.01      ( $false ),
% 2.57/1.01      inference(minisat,
% 2.57/1.01                [status(thm)],
% 2.57/1.01                [c_7920,c_7043,c_2367,c_1544,c_1516,c_29]) ).
% 2.57/1.01  
% 2.57/1.01  
% 2.57/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.57/1.01  
% 2.57/1.01  ------                               Statistics
% 2.57/1.01  
% 2.57/1.01  ------ General
% 2.57/1.01  
% 2.57/1.01  abstr_ref_over_cycles:                  0
% 2.57/1.01  abstr_ref_under_cycles:                 0
% 2.57/1.01  gc_basic_clause_elim:                   0
% 2.57/1.01  forced_gc_time:                         0
% 2.57/1.01  parsing_time:                           0.01
% 2.57/1.01  unif_index_cands_time:                  0.
% 2.57/1.01  unif_index_add_time:                    0.
% 2.57/1.01  orderings_time:                         0.
% 2.57/1.01  out_proof_time:                         0.01
% 2.57/1.01  total_time:                             0.273
% 2.57/1.01  num_of_symbols:                         53
% 2.57/1.01  num_of_terms:                           9187
% 2.57/1.01  
% 2.57/1.01  ------ Preprocessing
% 2.57/1.01  
% 2.57/1.01  num_of_splits:                          0
% 2.57/1.01  num_of_split_atoms:                     0
% 2.57/1.01  num_of_reused_defs:                     0
% 2.57/1.01  num_eq_ax_congr_red:                    49
% 2.57/1.01  num_of_sem_filtered_clauses:            1
% 2.57/1.01  num_of_subtypes:                        0
% 2.57/1.01  monotx_restored_types:                  0
% 2.57/1.01  sat_num_of_epr_types:                   0
% 2.57/1.01  sat_num_of_non_cyclic_types:            0
% 2.57/1.01  sat_guarded_non_collapsed_types:        0
% 2.57/1.01  num_pure_diseq_elim:                    0
% 2.57/1.01  simp_replaced_by:                       0
% 2.57/1.01  res_preprocessed:                       132
% 2.57/1.01  prep_upred:                             0
% 2.57/1.01  prep_unflattend:                        11
% 2.57/1.01  smt_new_axioms:                         0
% 2.57/1.01  pred_elim_cands:                        5
% 2.57/1.01  pred_elim:                              1
% 2.57/1.01  pred_elim_cl:                           1
% 2.57/1.01  pred_elim_cycles:                       4
% 2.57/1.01  merged_defs:                            0
% 2.57/1.01  merged_defs_ncl:                        0
% 2.57/1.01  bin_hyper_res:                          0
% 2.57/1.01  prep_cycles:                            4
% 2.57/1.01  pred_elim_time:                         0.002
% 2.57/1.01  splitting_time:                         0.
% 2.57/1.01  sem_filter_time:                        0.
% 2.57/1.01  monotx_time:                            0.001
% 2.57/1.01  subtype_inf_time:                       0.
% 2.57/1.01  
% 2.57/1.01  ------ Problem properties
% 2.57/1.01  
% 2.57/1.01  clauses:                                27
% 2.57/1.01  conjectures:                            3
% 2.57/1.01  epr:                                    2
% 2.57/1.01  horn:                                   20
% 2.57/1.01  ground:                                 2
% 2.57/1.01  unary:                                  3
% 2.57/1.01  binary:                                 6
% 2.57/1.01  lits:                                   89
% 2.57/1.01  lits_eq:                                3
% 2.57/1.01  fd_pure:                                0
% 2.57/1.01  fd_pseudo:                              0
% 2.57/1.01  fd_cond:                                0
% 2.57/1.01  fd_pseudo_cond:                         1
% 2.57/1.01  ac_symbols:                             0
% 2.57/1.01  
% 2.57/1.01  ------ Propositional Solver
% 2.57/1.01  
% 2.57/1.01  prop_solver_calls:                      29
% 2.57/1.01  prop_fast_solver_calls:                 1222
% 2.57/1.01  smt_solver_calls:                       0
% 2.57/1.01  smt_fast_solver_calls:                  0
% 2.57/1.01  prop_num_of_clauses:                    2908
% 2.57/1.01  prop_preprocess_simplified:             8532
% 2.57/1.01  prop_fo_subsumed:                       45
% 2.57/1.01  prop_solver_time:                       0.
% 2.57/1.01  smt_solver_time:                        0.
% 2.57/1.01  smt_fast_solver_time:                   0.
% 2.57/1.01  prop_fast_solver_time:                  0.
% 2.57/1.01  prop_unsat_core_time:                   0.
% 2.57/1.01  
% 2.57/1.01  ------ QBF
% 2.57/1.01  
% 2.57/1.01  qbf_q_res:                              0
% 2.57/1.01  qbf_num_tautologies:                    0
% 2.57/1.01  qbf_prep_cycles:                        0
% 2.57/1.01  
% 2.57/1.01  ------ BMC1
% 2.57/1.01  
% 2.57/1.01  bmc1_current_bound:                     -1
% 2.57/1.01  bmc1_last_solved_bound:                 -1
% 2.57/1.01  bmc1_unsat_core_size:                   -1
% 2.57/1.01  bmc1_unsat_core_parents_size:           -1
% 2.57/1.01  bmc1_merge_next_fun:                    0
% 2.57/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.57/1.01  
% 2.57/1.01  ------ Instantiation
% 2.57/1.01  
% 2.57/1.01  inst_num_of_clauses:                    703
% 2.57/1.01  inst_num_in_passive:                    333
% 2.57/1.01  inst_num_in_active:                     311
% 2.57/1.01  inst_num_in_unprocessed:                59
% 2.57/1.01  inst_num_of_loops:                      460
% 2.57/1.01  inst_num_of_learning_restarts:          0
% 2.57/1.01  inst_num_moves_active_passive:          146
% 2.57/1.01  inst_lit_activity:                      0
% 2.57/1.01  inst_lit_activity_moves:                0
% 2.57/1.01  inst_num_tautologies:                   0
% 2.57/1.01  inst_num_prop_implied:                  0
% 2.57/1.01  inst_num_existing_simplified:           0
% 2.57/1.01  inst_num_eq_res_simplified:             0
% 2.57/1.01  inst_num_child_elim:                    0
% 2.57/1.01  inst_num_of_dismatching_blockings:      120
% 2.57/1.01  inst_num_of_non_proper_insts:           758
% 2.57/1.01  inst_num_of_duplicates:                 0
% 2.57/1.01  inst_inst_num_from_inst_to_res:         0
% 2.57/1.01  inst_dismatching_checking_time:         0.
% 2.57/1.01  
% 2.57/1.01  ------ Resolution
% 2.57/1.01  
% 2.57/1.01  res_num_of_clauses:                     0
% 2.57/1.01  res_num_in_passive:                     0
% 2.57/1.01  res_num_in_active:                      0
% 2.57/1.01  res_num_of_loops:                       136
% 2.57/1.01  res_forward_subset_subsumed:            19
% 2.57/1.01  res_backward_subset_subsumed:           0
% 2.57/1.01  res_forward_subsumed:                   0
% 2.57/1.01  res_backward_subsumed:                  0
% 2.57/1.01  res_forward_subsumption_resolution:     0
% 2.57/1.01  res_backward_subsumption_resolution:    0
% 2.57/1.01  res_clause_to_clause_subsumption:       579
% 2.57/1.01  res_orphan_elimination:                 0
% 2.57/1.01  res_tautology_del:                      41
% 2.57/1.01  res_num_eq_res_simplified:              0
% 2.57/1.01  res_num_sel_changes:                    0
% 2.57/1.01  res_moves_from_active_to_pass:          0
% 2.57/1.01  
% 2.57/1.01  ------ Superposition
% 2.57/1.01  
% 2.57/1.01  sup_time_total:                         0.
% 2.57/1.01  sup_time_generating:                    0.
% 2.57/1.01  sup_time_sim_full:                      0.
% 2.57/1.01  sup_time_sim_immed:                     0.
% 2.57/1.01  
% 2.57/1.01  sup_num_of_clauses:                     189
% 2.57/1.01  sup_num_in_active:                      85
% 2.57/1.01  sup_num_in_passive:                     104
% 2.57/1.01  sup_num_of_loops:                       91
% 2.57/1.01  sup_fw_superposition:                   111
% 2.57/1.01  sup_bw_superposition:                   107
% 2.57/1.01  sup_immediate_simplified:               25
% 2.57/1.01  sup_given_eliminated:                   1
% 2.57/1.01  comparisons_done:                       0
% 2.57/1.01  comparisons_avoided:                    0
% 2.57/1.01  
% 2.57/1.01  ------ Simplifications
% 2.57/1.01  
% 2.57/1.01  
% 2.57/1.01  sim_fw_subset_subsumed:                 16
% 2.57/1.01  sim_bw_subset_subsumed:                 10
% 2.57/1.01  sim_fw_subsumed:                        7
% 2.57/1.01  sim_bw_subsumed:                        2
% 2.57/1.01  sim_fw_subsumption_res:                 2
% 2.57/1.01  sim_bw_subsumption_res:                 0
% 2.57/1.01  sim_tautology_del:                      13
% 2.57/1.01  sim_eq_tautology_del:                   1
% 2.57/1.01  sim_eq_res_simp:                        0
% 2.57/1.01  sim_fw_demodulated:                     0
% 2.57/1.01  sim_bw_demodulated:                     2
% 2.57/1.01  sim_light_normalised:                   2
% 2.57/1.01  sim_joinable_taut:                      0
% 2.57/1.01  sim_joinable_simp:                      0
% 2.57/1.01  sim_ac_normalised:                      0
% 2.57/1.01  sim_smt_subsumption:                    0
% 2.57/1.01  
%------------------------------------------------------------------------------
