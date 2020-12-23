%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:00 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :  153 (1007 expanded)
%              Number of clauses        :   92 ( 323 expanded)
%              Number of leaves         :   17 ( 223 expanded)
%              Depth                    :   22
%              Number of atoms          :  569 (4496 expanded)
%              Number of equality atoms :  186 ( 843 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f14,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f27])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK8
            | ~ r2_hidden(X5,X2)
            | ~ m1_subset_1(X5,X0) )
        & r2_hidden(sK8,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK7,X5) != X4
              | ~ r2_hidden(X5,sK6)
              | ~ m1_subset_1(X5,sK4) )
          & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6)) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ! [X5] :
        ( k1_funct_1(sK7,X5) != sK8
        | ~ r2_hidden(X5,sK6)
        | ~ m1_subset_1(X5,sK4) )
    & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f28,f46,f45])).

fof(f70,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X4,X3,X2,X1] :
      ( ? [X6] :
          ( r2_hidden(X6,X1)
          & r2_hidden(k4_tarski(X6,X4),X3)
          & m1_subset_1(X6,X2) )
     => ( r2_hidden(sK3(X1,X2,X3,X4),X1)
        & r2_hidden(k4_tarski(sK3(X1,X2,X3,X4),X4),X3)
        & m1_subset_1(sK3(X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK3(X1,X2,X3,X4),X1)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f71,plain,(
    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f47])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
        & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK3(X1,X2,X3,X4),X4),X3)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f47])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f72,plain,(
    ! [X5] :
      ( k1_funct_1(sK7,X5) != sK8
      | ~ r2_hidden(X5,sK6)
      | ~ m1_subset_1(X5,sK4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK3(X1,X2,X3,X4),X2)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1217,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1224,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2311,plain,
    ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
    inference(superposition,[status(thm)],[c_1217,c_1224])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | r2_hidden(sK3(X4,X3,X2,X0),X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1222,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | r2_hidden(sK3(X4,X3,X2,X0),X4) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_37,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | r2_hidden(sK3(X4,X3,X2,X0),X4) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2756,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) ),
    inference(resolution,[status(thm)],[c_15,c_5])).

cnf(c_2757,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2756])).

cnf(c_3476,plain,
    ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | r2_hidden(sK3(X4,X3,X2,X0),X4) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1222,c_37,c_2757])).

cnf(c_3477,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(X3,k7_relset_1(X1,X2,X0,X4)) != iProver_top
    | r2_hidden(sK3(X4,X1,X0,X3),X4) = iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(renaming,[status(thm)],[c_3476])).

cnf(c_3490,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(X1,sK4,sK7,X0),X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2311,c_3477])).

cnf(c_26,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_27,plain,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1468,plain,
    ( ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
    | ~ v1_xboole_0(k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1469,plain,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) != iProver_top
    | v1_xboole_0(k7_relset_1(sK4,sK5,sK7,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1468])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1499,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1500,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1499])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1605,plain,
    ( ~ m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1844,plain,
    ( ~ m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5))
    | v1_xboole_0(k7_relset_1(sK4,sK5,sK7,sK6))
    | ~ v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1605])).

cnf(c_1846,plain,
    ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5)) != iProver_top
    | v1_xboole_0(k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1844])).

cnf(c_1541,plain,
    ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,X0),k1_zfmisc_1(sK5))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1845,plain,
    ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_1541])).

cnf(c_1848,plain,
    ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5)) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1845])).

cnf(c_762,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1622,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k7_relset_1(sK4,sK5,sK7,sK6))
    | k7_relset_1(sK4,sK5,sK7,sK6) != X0 ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_1859,plain,
    ( v1_xboole_0(k7_relset_1(sK4,sK5,sK7,sK6))
    | ~ v1_xboole_0(k9_relat_1(sK7,sK6))
    | k7_relset_1(sK4,sK5,sK7,sK6) != k9_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_1622])).

cnf(c_1861,plain,
    ( k7_relset_1(sK4,sK5,sK7,sK6) != k9_relat_1(sK7,sK6)
    | v1_xboole_0(k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top
    | v1_xboole_0(k9_relat_1(sK7,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1859])).

cnf(c_1556,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1860,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k7_relset_1(sK4,sK5,sK7,sK6) = k9_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_1556])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2199,plain,
    ( r2_hidden(sK0(k9_relat_1(sK7,sK6)),k9_relat_1(sK7,sK6))
    | v1_xboole_0(k9_relat_1(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2200,plain,
    ( r2_hidden(sK0(k9_relat_1(sK7,sK6)),k9_relat_1(sK7,sK6)) = iProver_top
    | v1_xboole_0(k9_relat_1(sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2199])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK2(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2497,plain,
    ( r2_hidden(k4_tarski(sK2(sK0(k9_relat_1(sK7,sK6)),sK6,sK7),sK0(k9_relat_1(sK7,sK6))),sK7)
    | ~ r2_hidden(sK0(k9_relat_1(sK7,sK6)),k9_relat_1(sK7,sK6))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2504,plain,
    ( r2_hidden(k4_tarski(sK2(sK0(k9_relat_1(sK7,sK6)),sK6,sK7),sK0(k9_relat_1(sK7,sK6))),sK7) = iProver_top
    | r2_hidden(sK0(k9_relat_1(sK7,sK6)),k9_relat_1(sK7,sK6)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2497])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1226,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2699,plain,
    ( v1_xboole_0(sK4) != iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1217,c_1226])).

cnf(c_4050,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK0(k9_relat_1(sK7,sK6)),sK6,sK7),sK0(k9_relat_1(sK7,sK6))),sK7)
    | ~ v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4051,plain,
    ( r2_hidden(k4_tarski(sK2(sK0(k9_relat_1(sK7,sK6)),sK6,sK7),sK0(k9_relat_1(sK7,sK6))),sK7) != iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4050])).

cnf(c_5393,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(X1,sK4,sK7,X0),X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3490,c_23,c_26,c_27,c_1469,c_1500,c_1846,c_1848,c_1861,c_1860,c_2200,c_2504,c_2699,c_4051])).

cnf(c_1218,plain,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2521,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2311,c_1218])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | r2_hidden(k4_tarski(sK3(X4,X3,X2,X0),X0),X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1221,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | r2_hidden(k4_tarski(sK3(X4,X3,X2,X0),X0),X2) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2541,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK3(X1,sK4,sK7,X0),X0),sK7) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2311,c_1221])).

cnf(c_1225,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2659,plain,
    ( m1_subset_1(k9_relat_1(sK7,X0),k1_zfmisc_1(sK5)) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2311,c_1225])).

cnf(c_3163,plain,
    ( m1_subset_1(k9_relat_1(sK7,X0),k1_zfmisc_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2659,c_26])).

cnf(c_1232,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3171,plain,
    ( m1_subset_1(X0,sK5) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3163,c_1232])).

cnf(c_3304,plain,
    ( v1_xboole_0(X1) = iProver_top
    | r2_hidden(k4_tarski(sK3(X1,sK4,sK7,X0),X0),sK7) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2541,c_26,c_27,c_1469,c_1846,c_1848,c_3171])).

cnf(c_3305,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK3(X1,sK4,sK7,X0),X0),sK7) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_3304])).

cnf(c_11,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_314,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_24])).

cnf(c_315,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK7)
    | ~ v1_relat_1(sK7)
    | k1_funct_1(sK7,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_314])).

cnf(c_1214,plain,
    ( k1_funct_1(sK7,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_315])).

cnf(c_316,plain,
    ( k1_funct_1(sK7,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_315])).

cnf(c_1512,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
    | k1_funct_1(sK7,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1214,c_26,c_316,c_1500])).

cnf(c_1513,plain,
    ( k1_funct_1(sK7,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_1512])).

cnf(c_3316,plain,
    ( k1_funct_1(sK7,sK3(X0,sK4,sK7,X1)) = X1
    | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3305,c_1513])).

cnf(c_3355,plain,
    ( k1_funct_1(sK7,sK3(sK6,sK4,sK7,sK8)) = sK8
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2521,c_3316])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2499,plain,
    ( r2_hidden(sK2(sK0(k9_relat_1(sK7,sK6)),sK6,sK7),sK6)
    | ~ r2_hidden(sK0(k9_relat_1(sK7,sK6)),k9_relat_1(sK7,sK6))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2722,plain,
    ( ~ v1_xboole_0(sK4)
    | v1_xboole_0(sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2699])).

cnf(c_3386,plain,
    ( v1_xboole_0(sK4)
    | v1_xboole_0(sK6)
    | k1_funct_1(sK7,sK3(sK6,sK4,sK7,sK8)) = sK8 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3355])).

cnf(c_4179,plain,
    ( ~ r2_hidden(sK2(sK0(k9_relat_1(sK7,sK6)),sK6,sK7),sK6)
    | ~ v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4660,plain,
    ( k1_funct_1(sK7,sK3(sK6,sK4,sK7,sK8)) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3355,c_23,c_22,c_1468,c_1499,c_1859,c_1860,c_2199,c_2499,c_2497,c_2722,c_3386,c_4050,c_4179])).

cnf(c_21,negated_conjecture,
    ( ~ m1_subset_1(X0,sK4)
    | ~ r2_hidden(X0,sK6)
    | k1_funct_1(sK7,X0) != sK8 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1219,plain,
    ( k1_funct_1(sK7,X0) != sK8
    | m1_subset_1(X0,sK4) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4665,plain,
    ( m1_subset_1(sK3(sK6,sK4,sK7,sK8),sK4) != iProver_top
    | r2_hidden(sK3(sK6,sK4,sK7,sK8),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4660,c_1219])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | m1_subset_1(sK3(X4,X3,X2,X0),X3)
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1220,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(sK3(X4,X3,X2,X0),X3) = iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1724,plain,
    ( m1_subset_1(sK3(sK6,sK4,sK7,sK8),sK4) = iProver_top
    | m1_subset_1(sK8,sK5) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1218,c_1220])).

cnf(c_1642,plain,
    ( m1_subset_1(X0,sK5)
    | ~ m1_subset_1(k7_relset_1(sK4,sK5,sK7,X1),k1_zfmisc_1(sK5))
    | ~ r2_hidden(X0,k7_relset_1(sK4,sK5,sK7,X1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1941,plain,
    ( ~ m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5))
    | m1_subset_1(sK8,sK5)
    | ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_1642])).

cnf(c_1942,plain,
    ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5)) != iProver_top
    | m1_subset_1(sK8,sK5) = iProver_top
    | r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1941])).

cnf(c_2235,plain,
    ( m1_subset_1(sK3(sK6,sK4,sK7,sK8),sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1724,c_26,c_27,c_1469,c_1846,c_1848,c_1942])).

cnf(c_2500,plain,
    ( r2_hidden(sK2(sK0(k9_relat_1(sK7,sK6)),sK6,sK7),sK6) = iProver_top
    | r2_hidden(sK0(k9_relat_1(sK7,sK6)),k9_relat_1(sK7,sK6)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2499])).

cnf(c_4180,plain,
    ( r2_hidden(sK2(sK0(k9_relat_1(sK7,sK6)),sK6,sK7),sK6) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4179])).

cnf(c_4686,plain,
    ( r2_hidden(sK3(sK6,sK4,sK7,sK8),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4665,c_23,c_26,c_27,c_1469,c_1500,c_1861,c_1860,c_2200,c_2235,c_2500,c_2504,c_2699,c_4051,c_4180])).

cnf(c_5411,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_5393,c_4686])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5411,c_4180,c_2521,c_2500,c_2200,c_1860,c_1861,c_1500,c_1469,c_27,c_26,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:59:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.80/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/0.99  
% 2.80/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.80/0.99  
% 2.80/0.99  ------  iProver source info
% 2.80/0.99  
% 2.80/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.80/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.80/0.99  git: non_committed_changes: false
% 2.80/0.99  git: last_make_outside_of_git: false
% 2.80/0.99  
% 2.80/0.99  ------ 
% 2.80/0.99  ------ Parsing...
% 2.80/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.80/0.99  
% 2.80/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.80/0.99  
% 2.80/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.80/0.99  
% 2.80/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.80/0.99  ------ Proving...
% 2.80/0.99  ------ Problem Properties 
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  clauses                                 24
% 2.80/0.99  conjectures                             3
% 2.80/0.99  EPR                                     1
% 2.80/0.99  Horn                                    18
% 2.80/0.99  unary                                   2
% 2.80/0.99  binary                                  7
% 2.80/0.99  lits                                    81
% 2.80/0.99  lits eq                                 3
% 2.80/0.99  fd_pure                                 0
% 2.80/0.99  fd_pseudo                               0
% 2.80/0.99  fd_cond                                 0
% 2.80/0.99  fd_pseudo_cond                          1
% 2.80/0.99  AC symbols                              0
% 2.80/0.99  
% 2.80/0.99  ------ Input Options Time Limit: Unbounded
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  ------ 
% 2.80/0.99  Current options:
% 2.80/0.99  ------ 
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  ------ Proving...
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  % SZS status Theorem for theBenchmark.p
% 2.80/0.99  
% 2.80/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.80/0.99  
% 2.80/0.99  fof(f12,conjecture,(
% 2.80/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f13,negated_conjecture,(
% 2.80/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.80/0.99    inference(negated_conjecture,[],[f12])).
% 2.80/0.99  
% 2.80/0.99  fof(f14,plain,(
% 2.80/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.80/0.99    inference(pure_predicate_removal,[],[f13])).
% 2.80/0.99  
% 2.80/0.99  fof(f27,plain,(
% 2.80/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 2.80/0.99    inference(ennf_transformation,[],[f14])).
% 2.80/0.99  
% 2.80/0.99  fof(f28,plain,(
% 2.80/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 2.80/0.99    inference(flattening,[],[f27])).
% 2.80/0.99  
% 2.80/0.99  fof(f46,plain,(
% 2.80/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK8 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(sK8,k7_relset_1(X0,X1,X3,X2)))) )),
% 2.80/0.99    introduced(choice_axiom,[])).
% 2.80/0.99  
% 2.80/0.99  fof(f45,plain,(
% 2.80/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK7,X5) != X4 | ~r2_hidden(X5,sK6) | ~m1_subset_1(X5,sK4)) & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_1(sK7))),
% 2.80/0.99    introduced(choice_axiom,[])).
% 2.80/0.99  
% 2.80/0.99  fof(f47,plain,(
% 2.80/0.99    (! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~m1_subset_1(X5,sK4)) & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_1(sK7)),
% 2.80/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f28,f46,f45])).
% 2.80/0.99  
% 2.80/0.99  fof(f70,plain,(
% 2.80/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 2.80/0.99    inference(cnf_transformation,[],[f47])).
% 2.80/0.99  
% 2.80/0.99  fof(f10,axiom,(
% 2.80/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f25,plain,(
% 2.80/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.80/0.99    inference(ennf_transformation,[],[f10])).
% 2.80/0.99  
% 2.80/0.99  fof(f64,plain,(
% 2.80/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.80/0.99    inference(cnf_transformation,[],[f25])).
% 2.80/0.99  
% 2.80/0.99  fof(f11,axiom,(
% 2.80/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 2.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f26,plain,(
% 2.80/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.80/0.99    inference(ennf_transformation,[],[f11])).
% 2.80/0.99  
% 2.80/0.99  fof(f41,plain,(
% 2.80/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.80/0.99    inference(nnf_transformation,[],[f26])).
% 2.80/0.99  
% 2.80/0.99  fof(f42,plain,(
% 2.80/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.80/0.99    inference(rectify,[],[f41])).
% 2.80/0.99  
% 2.80/0.99  fof(f43,plain,(
% 2.80/0.99    ! [X4,X3,X2,X1] : (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) => (r2_hidden(sK3(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK3(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK3(X1,X2,X3,X4),X2)))),
% 2.80/0.99    introduced(choice_axiom,[])).
% 2.80/0.99  
% 2.80/0.99  fof(f44,plain,(
% 2.80/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & ((r2_hidden(sK3(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK3(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK3(X1,X2,X3,X4),X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.80/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).
% 2.80/0.99  
% 2.80/0.99  fof(f67,plain,(
% 2.80/0.99    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK3(X1,X2,X3,X4),X1) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f44])).
% 2.80/0.99  
% 2.80/0.99  fof(f9,axiom,(
% 2.80/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 2.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f24,plain,(
% 2.80/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.80/0.99    inference(ennf_transformation,[],[f9])).
% 2.80/0.99  
% 2.80/0.99  fof(f63,plain,(
% 2.80/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.80/0.99    inference(cnf_transformation,[],[f24])).
% 2.80/0.99  
% 2.80/0.99  fof(f4,axiom,(
% 2.80/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f17,plain,(
% 2.80/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.80/0.99    inference(ennf_transformation,[],[f4])).
% 2.80/0.99  
% 2.80/0.99  fof(f18,plain,(
% 2.80/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.80/0.99    inference(flattening,[],[f17])).
% 2.80/0.99  
% 2.80/0.99  fof(f53,plain,(
% 2.80/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f18])).
% 2.80/0.99  
% 2.80/0.99  fof(f71,plain,(
% 2.80/0.99    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))),
% 2.80/0.99    inference(cnf_transformation,[],[f47])).
% 2.80/0.99  
% 2.80/0.99  fof(f1,axiom,(
% 2.80/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f29,plain,(
% 2.80/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.80/0.99    inference(nnf_transformation,[],[f1])).
% 2.80/0.99  
% 2.80/0.99  fof(f30,plain,(
% 2.80/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.80/0.99    inference(rectify,[],[f29])).
% 2.80/0.99  
% 2.80/0.99  fof(f31,plain,(
% 2.80/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.80/0.99    introduced(choice_axiom,[])).
% 2.80/0.99  
% 2.80/0.99  fof(f32,plain,(
% 2.80/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.80/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 2.80/0.99  
% 2.80/0.99  fof(f48,plain,(
% 2.80/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f32])).
% 2.80/0.99  
% 2.80/0.99  fof(f7,axiom,(
% 2.80/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f22,plain,(
% 2.80/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.80/0.99    inference(ennf_transformation,[],[f7])).
% 2.80/0.99  
% 2.80/0.99  fof(f61,plain,(
% 2.80/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.80/0.99    inference(cnf_transformation,[],[f22])).
% 2.80/0.99  
% 2.80/0.99  fof(f3,axiom,(
% 2.80/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f16,plain,(
% 2.80/0.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.80/0.99    inference(ennf_transformation,[],[f3])).
% 2.80/0.99  
% 2.80/0.99  fof(f52,plain,(
% 2.80/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f16])).
% 2.80/0.99  
% 2.80/0.99  fof(f49,plain,(
% 2.80/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f32])).
% 2.80/0.99  
% 2.80/0.99  fof(f5,axiom,(
% 2.80/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 2.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.00  
% 2.80/1.00  fof(f19,plain,(
% 2.80/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 2.80/1.00    inference(ennf_transformation,[],[f5])).
% 2.80/1.00  
% 2.80/1.00  fof(f35,plain,(
% 2.80/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.80/1.00    inference(nnf_transformation,[],[f19])).
% 2.80/1.00  
% 2.80/1.00  fof(f36,plain,(
% 2.80/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.80/1.00    inference(rectify,[],[f35])).
% 2.80/1.00  
% 2.80/1.00  fof(f37,plain,(
% 2.80/1.00    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))))),
% 2.80/1.00    introduced(choice_axiom,[])).
% 2.80/1.00  
% 2.80/1.00  fof(f38,plain,(
% 2.80/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.80/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).
% 2.80/1.00  
% 2.80/1.00  fof(f55,plain,(
% 2.80/1.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.80/1.00    inference(cnf_transformation,[],[f38])).
% 2.80/1.00  
% 2.80/1.00  fof(f8,axiom,(
% 2.80/1.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 2.80/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.00  
% 2.80/1.00  fof(f23,plain,(
% 2.80/1.00    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.80/1.00    inference(ennf_transformation,[],[f8])).
% 2.80/1.00  
% 2.80/1.00  fof(f62,plain,(
% 2.80/1.00    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.80/1.00    inference(cnf_transformation,[],[f23])).
% 2.80/1.00  
% 2.80/1.00  fof(f66,plain,(
% 2.80/1.00    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK3(X1,X2,X3,X4),X4),X3) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.80/1.00    inference(cnf_transformation,[],[f44])).
% 2.80/1.00  
% 2.80/1.00  fof(f6,axiom,(
% 2.80/1.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 2.80/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.00  
% 2.80/1.00  fof(f20,plain,(
% 2.80/1.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.80/1.00    inference(ennf_transformation,[],[f6])).
% 2.80/1.00  
% 2.80/1.00  fof(f21,plain,(
% 2.80/1.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.80/1.00    inference(flattening,[],[f20])).
% 2.80/1.00  
% 2.80/1.00  fof(f39,plain,(
% 2.80/1.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.80/1.00    inference(nnf_transformation,[],[f21])).
% 2.80/1.00  
% 2.80/1.00  fof(f40,plain,(
% 2.80/1.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.80/1.00    inference(flattening,[],[f39])).
% 2.80/1.00  
% 2.80/1.00  fof(f59,plain,(
% 2.80/1.00    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.80/1.00    inference(cnf_transformation,[],[f40])).
% 2.80/1.00  
% 2.80/1.00  fof(f69,plain,(
% 2.80/1.00    v1_funct_1(sK7)),
% 2.80/1.00    inference(cnf_transformation,[],[f47])).
% 2.80/1.00  
% 2.80/1.00  fof(f56,plain,(
% 2.80/1.00    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.80/1.00    inference(cnf_transformation,[],[f38])).
% 2.80/1.00  
% 2.80/1.00  fof(f72,plain,(
% 2.80/1.00    ( ! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~m1_subset_1(X5,sK4)) )),
% 2.80/1.00    inference(cnf_transformation,[],[f47])).
% 2.80/1.00  
% 2.80/1.00  fof(f65,plain,(
% 2.80/1.00    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK3(X1,X2,X3,X4),X2) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.80/1.00    inference(cnf_transformation,[],[f44])).
% 2.80/1.00  
% 2.80/1.00  cnf(c_23,negated_conjecture,
% 2.80/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 2.80/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1217,plain,
% 2.80/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 2.80/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_16,plain,
% 2.80/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/1.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.80/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1224,plain,
% 2.80/1.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.80/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.80/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_2311,plain,
% 2.80/1.00      ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
% 2.80/1.00      inference(superposition,[status(thm)],[c_1217,c_1224]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_18,plain,
% 2.80/1.00      ( ~ m1_subset_1(X0,X1)
% 2.80/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 2.80/1.00      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 2.80/1.00      | r2_hidden(sK3(X4,X3,X2,X0),X4)
% 2.80/1.00      | v1_xboole_0(X1)
% 2.80/1.00      | v1_xboole_0(X3)
% 2.80/1.00      | v1_xboole_0(X4) ),
% 2.80/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1222,plain,
% 2.80/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 2.80/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 2.80/1.00      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 2.80/1.00      | r2_hidden(sK3(X4,X3,X2,X0),X4) = iProver_top
% 2.80/1.00      | v1_xboole_0(X1) = iProver_top
% 2.80/1.00      | v1_xboole_0(X3) = iProver_top
% 2.80/1.00      | v1_xboole_0(X4) = iProver_top ),
% 2.80/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_37,plain,
% 2.80/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 2.80/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 2.80/1.00      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 2.80/1.00      | r2_hidden(sK3(X4,X3,X2,X0),X4) = iProver_top
% 2.80/1.00      | v1_xboole_0(X1) = iProver_top
% 2.80/1.00      | v1_xboole_0(X3) = iProver_top
% 2.80/1.00      | v1_xboole_0(X4) = iProver_top ),
% 2.80/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_15,plain,
% 2.80/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/1.00      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
% 2.80/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_5,plain,
% 2.80/1.00      ( m1_subset_1(X0,X1)
% 2.80/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.80/1.00      | ~ r2_hidden(X0,X2) ),
% 2.80/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_2756,plain,
% 2.80/1.00      ( m1_subset_1(X0,X1)
% 2.80/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 2.80/1.00      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) ),
% 2.80/1.00      inference(resolution,[status(thm)],[c_15,c_5]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_2757,plain,
% 2.80/1.00      ( m1_subset_1(X0,X1) = iProver_top
% 2.80/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 2.80/1.00      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top ),
% 2.80/1.00      inference(predicate_to_equality,[status(thm)],[c_2756]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_3476,plain,
% 2.80/1.00      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 2.80/1.00      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 2.80/1.00      | r2_hidden(sK3(X4,X3,X2,X0),X4) = iProver_top
% 2.80/1.00      | v1_xboole_0(X1) = iProver_top
% 2.80/1.00      | v1_xboole_0(X3) = iProver_top
% 2.80/1.00      | v1_xboole_0(X4) = iProver_top ),
% 2.80/1.00      inference(global_propositional_subsumption,
% 2.80/1.00                [status(thm)],
% 2.80/1.00                [c_1222,c_37,c_2757]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_3477,plain,
% 2.80/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.80/1.00      | r2_hidden(X3,k7_relset_1(X1,X2,X0,X4)) != iProver_top
% 2.80/1.00      | r2_hidden(sK3(X4,X1,X0,X3),X4) = iProver_top
% 2.80/1.00      | v1_xboole_0(X2) = iProver_top
% 2.80/1.00      | v1_xboole_0(X1) = iProver_top
% 2.80/1.00      | v1_xboole_0(X4) = iProver_top ),
% 2.80/1.00      inference(renaming,[status(thm)],[c_3476]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_3490,plain,
% 2.80/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 2.80/1.00      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 2.80/1.00      | r2_hidden(sK3(X1,sK4,sK7,X0),X1) = iProver_top
% 2.80/1.00      | v1_xboole_0(X1) = iProver_top
% 2.80/1.00      | v1_xboole_0(sK5) = iProver_top
% 2.80/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 2.80/1.00      inference(superposition,[status(thm)],[c_2311,c_3477]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_26,plain,
% 2.80/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 2.80/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_22,negated_conjecture,
% 2.80/1.00      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
% 2.80/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_27,plain,
% 2.80/1.00      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
% 2.80/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1,plain,
% 2.80/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.80/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1468,plain,
% 2.80/1.00      ( ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
% 2.80/1.00      | ~ v1_xboole_0(k7_relset_1(sK4,sK5,sK7,sK6)) ),
% 2.80/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1469,plain,
% 2.80/1.00      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) != iProver_top
% 2.80/1.00      | v1_xboole_0(k7_relset_1(sK4,sK5,sK7,sK6)) != iProver_top ),
% 2.80/1.00      inference(predicate_to_equality,[status(thm)],[c_1468]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_13,plain,
% 2.80/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/1.00      | v1_relat_1(X0) ),
% 2.80/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1499,plain,
% 2.80/1.00      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 2.80/1.00      | v1_relat_1(sK7) ),
% 2.80/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1500,plain,
% 2.80/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 2.80/1.00      | v1_relat_1(sK7) = iProver_top ),
% 2.80/1.00      inference(predicate_to_equality,[status(thm)],[c_1499]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_4,plain,
% 2.80/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.80/1.00      | ~ v1_xboole_0(X1)
% 2.80/1.00      | v1_xboole_0(X0) ),
% 2.80/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1605,plain,
% 2.80/1.00      ( ~ m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(X0))
% 2.80/1.00      | ~ v1_xboole_0(X0)
% 2.80/1.00      | v1_xboole_0(k7_relset_1(sK4,sK5,sK7,sK6)) ),
% 2.80/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1844,plain,
% 2.80/1.00      ( ~ m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5))
% 2.80/1.00      | v1_xboole_0(k7_relset_1(sK4,sK5,sK7,sK6))
% 2.80/1.00      | ~ v1_xboole_0(sK5) ),
% 2.80/1.00      inference(instantiation,[status(thm)],[c_1605]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1846,plain,
% 2.80/1.00      ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5)) != iProver_top
% 2.80/1.00      | v1_xboole_0(k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top
% 2.80/1.00      | v1_xboole_0(sK5) != iProver_top ),
% 2.80/1.00      inference(predicate_to_equality,[status(thm)],[c_1844]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1541,plain,
% 2.80/1.00      ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,X0),k1_zfmisc_1(sK5))
% 2.80/1.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 2.80/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1845,plain,
% 2.80/1.00      ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5))
% 2.80/1.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 2.80/1.00      inference(instantiation,[status(thm)],[c_1541]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1848,plain,
% 2.80/1.00      ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5)) = iProver_top
% 2.80/1.00      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
% 2.80/1.00      inference(predicate_to_equality,[status(thm)],[c_1845]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_762,plain,
% 2.80/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.80/1.00      theory(equality) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1622,plain,
% 2.80/1.00      ( ~ v1_xboole_0(X0)
% 2.80/1.00      | v1_xboole_0(k7_relset_1(sK4,sK5,sK7,sK6))
% 2.80/1.00      | k7_relset_1(sK4,sK5,sK7,sK6) != X0 ),
% 2.80/1.00      inference(instantiation,[status(thm)],[c_762]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1859,plain,
% 2.80/1.00      ( v1_xboole_0(k7_relset_1(sK4,sK5,sK7,sK6))
% 2.80/1.00      | ~ v1_xboole_0(k9_relat_1(sK7,sK6))
% 2.80/1.00      | k7_relset_1(sK4,sK5,sK7,sK6) != k9_relat_1(sK7,sK6) ),
% 2.80/1.00      inference(instantiation,[status(thm)],[c_1622]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1861,plain,
% 2.80/1.00      ( k7_relset_1(sK4,sK5,sK7,sK6) != k9_relat_1(sK7,sK6)
% 2.80/1.00      | v1_xboole_0(k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top
% 2.80/1.00      | v1_xboole_0(k9_relat_1(sK7,sK6)) != iProver_top ),
% 2.80/1.00      inference(predicate_to_equality,[status(thm)],[c_1859]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1556,plain,
% 2.80/1.00      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 2.80/1.00      | k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
% 2.80/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1860,plain,
% 2.80/1.00      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 2.80/1.00      | k7_relset_1(sK4,sK5,sK7,sK6) = k9_relat_1(sK7,sK6) ),
% 2.80/1.00      inference(instantiation,[status(thm)],[c_1556]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_0,plain,
% 2.80/1.00      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.80/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_2199,plain,
% 2.80/1.00      ( r2_hidden(sK0(k9_relat_1(sK7,sK6)),k9_relat_1(sK7,sK6))
% 2.80/1.00      | v1_xboole_0(k9_relat_1(sK7,sK6)) ),
% 2.80/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_2200,plain,
% 2.80/1.00      ( r2_hidden(sK0(k9_relat_1(sK7,sK6)),k9_relat_1(sK7,sK6)) = iProver_top
% 2.80/1.00      | v1_xboole_0(k9_relat_1(sK7,sK6)) = iProver_top ),
% 2.80/1.00      inference(predicate_to_equality,[status(thm)],[c_2199]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_8,plain,
% 2.80/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.80/1.00      | r2_hidden(k4_tarski(sK2(X0,X2,X1),X0),X1)
% 2.80/1.00      | ~ v1_relat_1(X1) ),
% 2.80/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_2497,plain,
% 2.80/1.00      ( r2_hidden(k4_tarski(sK2(sK0(k9_relat_1(sK7,sK6)),sK6,sK7),sK0(k9_relat_1(sK7,sK6))),sK7)
% 2.80/1.00      | ~ r2_hidden(sK0(k9_relat_1(sK7,sK6)),k9_relat_1(sK7,sK6))
% 2.80/1.00      | ~ v1_relat_1(sK7) ),
% 2.80/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_2504,plain,
% 2.80/1.00      ( r2_hidden(k4_tarski(sK2(sK0(k9_relat_1(sK7,sK6)),sK6,sK7),sK0(k9_relat_1(sK7,sK6))),sK7) = iProver_top
% 2.80/1.00      | r2_hidden(sK0(k9_relat_1(sK7,sK6)),k9_relat_1(sK7,sK6)) != iProver_top
% 2.80/1.00      | v1_relat_1(sK7) != iProver_top ),
% 2.80/1.00      inference(predicate_to_equality,[status(thm)],[c_2497]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_14,plain,
% 2.80/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/1.00      | ~ v1_xboole_0(X1)
% 2.80/1.00      | v1_xboole_0(X0) ),
% 2.80/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1226,plain,
% 2.80/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.80/1.00      | v1_xboole_0(X1) != iProver_top
% 2.80/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.80/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_2699,plain,
% 2.80/1.00      ( v1_xboole_0(sK4) != iProver_top
% 2.80/1.00      | v1_xboole_0(sK7) = iProver_top ),
% 2.80/1.00      inference(superposition,[status(thm)],[c_1217,c_1226]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_4050,plain,
% 2.80/1.00      ( ~ r2_hidden(k4_tarski(sK2(sK0(k9_relat_1(sK7,sK6)),sK6,sK7),sK0(k9_relat_1(sK7,sK6))),sK7)
% 2.80/1.00      | ~ v1_xboole_0(sK7) ),
% 2.80/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_4051,plain,
% 2.80/1.00      ( r2_hidden(k4_tarski(sK2(sK0(k9_relat_1(sK7,sK6)),sK6,sK7),sK0(k9_relat_1(sK7,sK6))),sK7) != iProver_top
% 2.80/1.00      | v1_xboole_0(sK7) != iProver_top ),
% 2.80/1.00      inference(predicate_to_equality,[status(thm)],[c_4050]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_5393,plain,
% 2.80/1.00      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 2.80/1.00      | r2_hidden(sK3(X1,sK4,sK7,X0),X1) = iProver_top
% 2.80/1.00      | v1_xboole_0(X1) = iProver_top ),
% 2.80/1.00      inference(global_propositional_subsumption,
% 2.80/1.00                [status(thm)],
% 2.80/1.00                [c_3490,c_23,c_26,c_27,c_1469,c_1500,c_1846,c_1848,
% 2.80/1.00                 c_1861,c_1860,c_2200,c_2504,c_2699,c_4051]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1218,plain,
% 2.80/1.00      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
% 2.80/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_2521,plain,
% 2.80/1.00      ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
% 2.80/1.00      inference(demodulation,[status(thm)],[c_2311,c_1218]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_19,plain,
% 2.80/1.00      ( ~ m1_subset_1(X0,X1)
% 2.80/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 2.80/1.00      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 2.80/1.00      | r2_hidden(k4_tarski(sK3(X4,X3,X2,X0),X0),X2)
% 2.80/1.00      | v1_xboole_0(X1)
% 2.80/1.00      | v1_xboole_0(X3)
% 2.80/1.00      | v1_xboole_0(X4) ),
% 2.80/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1221,plain,
% 2.80/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 2.80/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 2.80/1.00      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 2.80/1.00      | r2_hidden(k4_tarski(sK3(X4,X3,X2,X0),X0),X2) = iProver_top
% 2.80/1.00      | v1_xboole_0(X1) = iProver_top
% 2.80/1.00      | v1_xboole_0(X3) = iProver_top
% 2.80/1.00      | v1_xboole_0(X4) = iProver_top ),
% 2.80/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_2541,plain,
% 2.80/1.00      ( m1_subset_1(X0,sK5) != iProver_top
% 2.80/1.00      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 2.80/1.00      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 2.80/1.00      | r2_hidden(k4_tarski(sK3(X1,sK4,sK7,X0),X0),sK7) = iProver_top
% 2.80/1.00      | v1_xboole_0(X1) = iProver_top
% 2.80/1.00      | v1_xboole_0(sK5) = iProver_top
% 2.80/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 2.80/1.00      inference(superposition,[status(thm)],[c_2311,c_1221]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1225,plain,
% 2.80/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.80/1.00      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
% 2.80/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_2659,plain,
% 2.80/1.00      ( m1_subset_1(k9_relat_1(sK7,X0),k1_zfmisc_1(sK5)) = iProver_top
% 2.80/1.00      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
% 2.80/1.00      inference(superposition,[status(thm)],[c_2311,c_1225]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_3163,plain,
% 2.80/1.00      ( m1_subset_1(k9_relat_1(sK7,X0),k1_zfmisc_1(sK5)) = iProver_top ),
% 2.80/1.00      inference(global_propositional_subsumption,
% 2.80/1.00                [status(thm)],
% 2.80/1.00                [c_2659,c_26]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1232,plain,
% 2.80/1.00      ( m1_subset_1(X0,X1) = iProver_top
% 2.80/1.00      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.80/1.00      | r2_hidden(X0,X2) != iProver_top ),
% 2.80/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_3171,plain,
% 2.80/1.00      ( m1_subset_1(X0,sK5) = iProver_top
% 2.80/1.00      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
% 2.80/1.00      inference(superposition,[status(thm)],[c_3163,c_1232]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_3304,plain,
% 2.80/1.00      ( v1_xboole_0(X1) = iProver_top
% 2.80/1.00      | r2_hidden(k4_tarski(sK3(X1,sK4,sK7,X0),X0),sK7) = iProver_top
% 2.80/1.00      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 2.80/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 2.80/1.00      inference(global_propositional_subsumption,
% 2.80/1.00                [status(thm)],
% 2.80/1.00                [c_2541,c_26,c_27,c_1469,c_1846,c_1848,c_3171]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_3305,plain,
% 2.80/1.00      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 2.80/1.00      | r2_hidden(k4_tarski(sK3(X1,sK4,sK7,X0),X0),sK7) = iProver_top
% 2.80/1.00      | v1_xboole_0(X1) = iProver_top
% 2.80/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 2.80/1.00      inference(renaming,[status(thm)],[c_3304]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_11,plain,
% 2.80/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 2.80/1.00      | ~ v1_funct_1(X2)
% 2.80/1.00      | ~ v1_relat_1(X2)
% 2.80/1.00      | k1_funct_1(X2,X0) = X1 ),
% 2.80/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_24,negated_conjecture,
% 2.80/1.00      ( v1_funct_1(sK7) ),
% 2.80/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_314,plain,
% 2.80/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 2.80/1.00      | ~ v1_relat_1(X2)
% 2.80/1.00      | k1_funct_1(X2,X0) = X1
% 2.80/1.00      | sK7 != X2 ),
% 2.80/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_24]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_315,plain,
% 2.80/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),sK7)
% 2.80/1.00      | ~ v1_relat_1(sK7)
% 2.80/1.00      | k1_funct_1(sK7,X0) = X1 ),
% 2.80/1.00      inference(unflattening,[status(thm)],[c_314]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1214,plain,
% 2.80/1.00      ( k1_funct_1(sK7,X0) = X1
% 2.80/1.00      | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
% 2.80/1.00      | v1_relat_1(sK7) != iProver_top ),
% 2.80/1.00      inference(predicate_to_equality,[status(thm)],[c_315]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_316,plain,
% 2.80/1.00      ( k1_funct_1(sK7,X0) = X1
% 2.80/1.00      | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
% 2.80/1.00      | v1_relat_1(sK7) != iProver_top ),
% 2.80/1.00      inference(predicate_to_equality,[status(thm)],[c_315]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1512,plain,
% 2.80/1.00      ( r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
% 2.80/1.00      | k1_funct_1(sK7,X0) = X1 ),
% 2.80/1.00      inference(global_propositional_subsumption,
% 2.80/1.00                [status(thm)],
% 2.80/1.00                [c_1214,c_26,c_316,c_1500]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1513,plain,
% 2.80/1.00      ( k1_funct_1(sK7,X0) = X1
% 2.80/1.00      | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top ),
% 2.80/1.00      inference(renaming,[status(thm)],[c_1512]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_3316,plain,
% 2.80/1.00      ( k1_funct_1(sK7,sK3(X0,sK4,sK7,X1)) = X1
% 2.80/1.00      | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
% 2.80/1.00      | v1_xboole_0(X0) = iProver_top
% 2.80/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 2.80/1.00      inference(superposition,[status(thm)],[c_3305,c_1513]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_3355,plain,
% 2.80/1.00      ( k1_funct_1(sK7,sK3(sK6,sK4,sK7,sK8)) = sK8
% 2.80/1.00      | v1_xboole_0(sK4) = iProver_top
% 2.80/1.00      | v1_xboole_0(sK6) = iProver_top ),
% 2.80/1.00      inference(superposition,[status(thm)],[c_2521,c_3316]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_7,plain,
% 2.80/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.80/1.00      | r2_hidden(sK2(X0,X2,X1),X2)
% 2.80/1.00      | ~ v1_relat_1(X1) ),
% 2.80/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_2499,plain,
% 2.80/1.00      ( r2_hidden(sK2(sK0(k9_relat_1(sK7,sK6)),sK6,sK7),sK6)
% 2.80/1.00      | ~ r2_hidden(sK0(k9_relat_1(sK7,sK6)),k9_relat_1(sK7,sK6))
% 2.80/1.00      | ~ v1_relat_1(sK7) ),
% 2.80/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_2722,plain,
% 2.80/1.00      ( ~ v1_xboole_0(sK4) | v1_xboole_0(sK7) ),
% 2.80/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2699]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_3386,plain,
% 2.80/1.00      ( v1_xboole_0(sK4)
% 2.80/1.00      | v1_xboole_0(sK6)
% 2.80/1.00      | k1_funct_1(sK7,sK3(sK6,sK4,sK7,sK8)) = sK8 ),
% 2.80/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3355]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_4179,plain,
% 2.80/1.00      ( ~ r2_hidden(sK2(sK0(k9_relat_1(sK7,sK6)),sK6,sK7),sK6)
% 2.80/1.00      | ~ v1_xboole_0(sK6) ),
% 2.80/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_4660,plain,
% 2.80/1.00      ( k1_funct_1(sK7,sK3(sK6,sK4,sK7,sK8)) = sK8 ),
% 2.80/1.00      inference(global_propositional_subsumption,
% 2.80/1.00                [status(thm)],
% 2.80/1.00                [c_3355,c_23,c_22,c_1468,c_1499,c_1859,c_1860,c_2199,
% 2.80/1.00                 c_2499,c_2497,c_2722,c_3386,c_4050,c_4179]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_21,negated_conjecture,
% 2.80/1.00      ( ~ m1_subset_1(X0,sK4)
% 2.80/1.00      | ~ r2_hidden(X0,sK6)
% 2.80/1.00      | k1_funct_1(sK7,X0) != sK8 ),
% 2.80/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1219,plain,
% 2.80/1.00      ( k1_funct_1(sK7,X0) != sK8
% 2.80/1.00      | m1_subset_1(X0,sK4) != iProver_top
% 2.80/1.00      | r2_hidden(X0,sK6) != iProver_top ),
% 2.80/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_4665,plain,
% 2.80/1.00      ( m1_subset_1(sK3(sK6,sK4,sK7,sK8),sK4) != iProver_top
% 2.80/1.00      | r2_hidden(sK3(sK6,sK4,sK7,sK8),sK6) != iProver_top ),
% 2.80/1.00      inference(superposition,[status(thm)],[c_4660,c_1219]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_20,plain,
% 2.80/1.00      ( ~ m1_subset_1(X0,X1)
% 2.80/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 2.80/1.00      | m1_subset_1(sK3(X4,X3,X2,X0),X3)
% 2.80/1.00      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 2.80/1.00      | v1_xboole_0(X1)
% 2.80/1.00      | v1_xboole_0(X3)
% 2.80/1.00      | v1_xboole_0(X4) ),
% 2.80/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1220,plain,
% 2.80/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 2.80/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 2.80/1.00      | m1_subset_1(sK3(X4,X3,X2,X0),X3) = iProver_top
% 2.80/1.00      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 2.80/1.00      | v1_xboole_0(X1) = iProver_top
% 2.80/1.00      | v1_xboole_0(X3) = iProver_top
% 2.80/1.00      | v1_xboole_0(X4) = iProver_top ),
% 2.80/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1724,plain,
% 2.80/1.00      ( m1_subset_1(sK3(sK6,sK4,sK7,sK8),sK4) = iProver_top
% 2.80/1.00      | m1_subset_1(sK8,sK5) != iProver_top
% 2.80/1.00      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 2.80/1.00      | v1_xboole_0(sK5) = iProver_top
% 2.80/1.00      | v1_xboole_0(sK4) = iProver_top
% 2.80/1.00      | v1_xboole_0(sK6) = iProver_top ),
% 2.80/1.00      inference(superposition,[status(thm)],[c_1218,c_1220]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1642,plain,
% 2.80/1.00      ( m1_subset_1(X0,sK5)
% 2.80/1.00      | ~ m1_subset_1(k7_relset_1(sK4,sK5,sK7,X1),k1_zfmisc_1(sK5))
% 2.80/1.00      | ~ r2_hidden(X0,k7_relset_1(sK4,sK5,sK7,X1)) ),
% 2.80/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1941,plain,
% 2.80/1.00      ( ~ m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5))
% 2.80/1.00      | m1_subset_1(sK8,sK5)
% 2.80/1.00      | ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
% 2.80/1.00      inference(instantiation,[status(thm)],[c_1642]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_1942,plain,
% 2.80/1.00      ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5)) != iProver_top
% 2.80/1.00      | m1_subset_1(sK8,sK5) = iProver_top
% 2.80/1.00      | r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) != iProver_top ),
% 2.80/1.00      inference(predicate_to_equality,[status(thm)],[c_1941]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_2235,plain,
% 2.80/1.00      ( m1_subset_1(sK3(sK6,sK4,sK7,sK8),sK4) = iProver_top
% 2.80/1.00      | v1_xboole_0(sK4) = iProver_top
% 2.80/1.00      | v1_xboole_0(sK6) = iProver_top ),
% 2.80/1.00      inference(global_propositional_subsumption,
% 2.80/1.00                [status(thm)],
% 2.80/1.00                [c_1724,c_26,c_27,c_1469,c_1846,c_1848,c_1942]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_2500,plain,
% 2.80/1.00      ( r2_hidden(sK2(sK0(k9_relat_1(sK7,sK6)),sK6,sK7),sK6) = iProver_top
% 2.80/1.00      | r2_hidden(sK0(k9_relat_1(sK7,sK6)),k9_relat_1(sK7,sK6)) != iProver_top
% 2.80/1.00      | v1_relat_1(sK7) != iProver_top ),
% 2.80/1.00      inference(predicate_to_equality,[status(thm)],[c_2499]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_4180,plain,
% 2.80/1.00      ( r2_hidden(sK2(sK0(k9_relat_1(sK7,sK6)),sK6,sK7),sK6) != iProver_top
% 2.80/1.00      | v1_xboole_0(sK6) != iProver_top ),
% 2.80/1.00      inference(predicate_to_equality,[status(thm)],[c_4179]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_4686,plain,
% 2.80/1.00      ( r2_hidden(sK3(sK6,sK4,sK7,sK8),sK6) != iProver_top ),
% 2.80/1.00      inference(global_propositional_subsumption,
% 2.80/1.00                [status(thm)],
% 2.80/1.00                [c_4665,c_23,c_26,c_27,c_1469,c_1500,c_1861,c_1860,
% 2.80/1.00                 c_2200,c_2235,c_2500,c_2504,c_2699,c_4051,c_4180]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(c_5411,plain,
% 2.80/1.00      ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
% 2.80/1.00      | v1_xboole_0(sK6) = iProver_top ),
% 2.80/1.00      inference(superposition,[status(thm)],[c_5393,c_4686]) ).
% 2.80/1.00  
% 2.80/1.00  cnf(contradiction,plain,
% 2.80/1.00      ( $false ),
% 2.80/1.00      inference(minisat,
% 2.80/1.00                [status(thm)],
% 2.80/1.00                [c_5411,c_4180,c_2521,c_2500,c_2200,c_1860,c_1861,c_1500,
% 2.80/1.00                 c_1469,c_27,c_26,c_23]) ).
% 2.80/1.00  
% 2.80/1.00  
% 2.80/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.80/1.00  
% 2.80/1.00  ------                               Statistics
% 2.80/1.00  
% 2.80/1.00  ------ Selected
% 2.80/1.00  
% 2.80/1.00  total_time:                             0.147
% 2.80/1.00  
%------------------------------------------------------------------------------
