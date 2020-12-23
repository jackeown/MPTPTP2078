%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:51 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :  197 (1165 expanded)
%              Number of clauses        :  121 ( 381 expanded)
%              Number of leaves         :   23 ( 254 expanded)
%              Depth                    :   22
%              Number of atoms          :  698 (5583 expanded)
%              Number of equality atoms :  243 (1133 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f30])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK9
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X5,X0) )
        & r2_hidden(sK9,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
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
              ( k1_funct_1(sK8,X5) != X4
              | ~ r2_hidden(X5,sK7)
              | ~ r2_hidden(X5,sK5) )
          & r2_hidden(X4,k7_relset_1(sK5,sK6,sK8,sK7)) )
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ! [X5] :
        ( k1_funct_1(sK8,X5) != sK9
        | ~ r2_hidden(X5,sK7)
        | ~ r2_hidden(X5,sK5) )
    & r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f31,f52,f51])).

fof(f78,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f53])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

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
    inference(nnf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f81,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f64])).

fof(f77,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f53])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X5] :
              ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
              & r2_hidden(X5,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(rectify,[],[f42])).

fof(f45,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK3(X1,X2),X6),X2)
        & r2_hidden(sK3(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK3(X1,X2),X6),X2)
            & r2_hidden(sK3(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f43,f45,f44])).

fof(f71,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relset_1(X1,X0,X2) = X1
      | ~ r2_hidden(k4_tarski(sK3(X1,X2),X6),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f79,plain,(
    r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(cnf_transformation,[],[f53])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
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

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X4,X3,X2,X1] :
      ( ? [X6] :
          ( r2_hidden(X6,X1)
          & r2_hidden(k4_tarski(X6,X4),X3)
          & m1_subset_1(X6,X2) )
     => ( r2_hidden(sK4(X1,X2,X3,X4),X1)
        & r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3)
        & m1_subset_1(sK4(X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

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
                        & ( ( r2_hidden(sK4(X1,X2,X3,X4),X1)
                            & r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3)
                            & m1_subset_1(sK4(X1,X2,X3,X4),X2) )
                          | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f48,f49])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK4(X1,X2,X3,X4),X2)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
            & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK4(X1,X2,X3,X4),X1)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X1,X0,X2) = X1
      | r2_hidden(sK3(X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f80,plain,(
    ! [X5] :
      ( k1_funct_1(sK8,X5) != sK9
      | ~ r2_hidden(X5,sK7)
      | ~ r2_hidden(X5,sK5) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1261,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_321,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_26])).

cnf(c_322,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8)
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_321])).

cnf(c_1259,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_322])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1536,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1563,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8)
    | ~ r2_hidden(X0,k1_relat_1(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_322,c_25,c_1536])).

cnf(c_1564,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) ),
    inference(renaming,[status(thm)],[c_1563])).

cnf(c_1565,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1564])).

cnf(c_1650,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1259,c_1565])).

cnf(c_1651,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) = iProver_top ),
    inference(renaming,[status(thm)],[c_1650])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(k4_tarski(sK3(X1,X0),X3),X0)
    | k1_relset_1(X1,X2,X0) = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1269,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(k4_tarski(sK3(X0,X2),X3),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4414,plain,
    ( k1_relset_1(X0,X1,sK8) = X0
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(sK3(X0,sK8),k1_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1651,c_1269])).

cnf(c_4731,plain,
    ( k1_relset_1(sK5,sK6,sK8) = sK5
    | r2_hidden(sK3(sK5,sK8),k1_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1261,c_4414])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1272,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1850,plain,
    ( k1_relset_1(sK5,sK6,sK8) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_1261,c_1272])).

cnf(c_4732,plain,
    ( k1_relat_1(sK8) = sK5
    | r2_hidden(sK3(sK5,sK8),k1_relat_1(sK8)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4731,c_1850])).

cnf(c_28,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_29,plain,
    ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1537,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1536])).

cnf(c_792,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1754,plain,
    ( sK9 = sK9 ),
    inference(instantiation,[status(thm)],[c_792])).

cnf(c_3,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1748,plain,
    ( m1_subset_1(X0,sK6)
    | ~ m1_subset_1(k7_relset_1(sK5,sK6,sK8,X1),k1_zfmisc_1(sK6))
    | ~ r2_hidden(X0,k7_relset_1(sK5,sK6,sK8,X1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1949,plain,
    ( ~ m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6))
    | m1_subset_1(sK9,sK6)
    | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_1748])).

cnf(c_1950,plain,
    ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6)) != iProver_top
    | m1_subset_1(sK9,sK6) = iProver_top
    | r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1949])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1634,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | k7_relset_1(sK5,sK6,sK8,X0) = k9_relat_1(sK8,X0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2088,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | k7_relset_1(sK5,sK6,sK8,sK7) = k9_relat_1(sK8,sK7) ),
    inference(instantiation,[status(thm)],[c_1634])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1619,plain,
    ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,X0),k1_zfmisc_1(sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2154,plain,
    ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_1619])).

cnf(c_2155,plain,
    ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6)) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2154])).

cnf(c_793,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1888,plain,
    ( X0 != X1
    | X0 = k7_relset_1(sK5,sK6,sK8,sK7)
    | k7_relset_1(sK5,sK6,sK8,sK7) != X1 ),
    inference(instantiation,[status(thm)],[c_793])).

cnf(c_2087,plain,
    ( X0 = k7_relset_1(sK5,sK6,sK8,sK7)
    | X0 != k9_relat_1(sK8,sK7)
    | k7_relset_1(sK5,sK6,sK8,sK7) != k9_relat_1(sK8,sK7) ),
    inference(instantiation,[status(thm)],[c_1888])).

cnf(c_2160,plain,
    ( k7_relset_1(sK5,sK6,sK8,sK7) != k9_relat_1(sK8,sK7)
    | k9_relat_1(sK8,sK7) = k7_relset_1(sK5,sK6,sK8,sK7)
    | k9_relat_1(sK8,sK7) != k9_relat_1(sK8,sK7) ),
    inference(instantiation,[status(thm)],[c_2087])).

cnf(c_2161,plain,
    ( k9_relat_1(sK8,sK7) = k9_relat_1(sK8,sK7) ),
    inference(instantiation,[status(thm)],[c_792])).

cnf(c_1262,plain,
    ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | m1_subset_1(sK4(X4,X3,X2,X0),X3)
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1264,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(sK4(X4,X3,X2,X0),X3) = iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1769,plain,
    ( m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
    | m1_subset_1(sK9,sK6) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1262,c_1264])).

cnf(c_2107,plain,
    ( m1_subset_1(sK9,sK6) != iProver_top
    | m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1769,c_28])).

cnf(c_2108,plain,
    ( m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
    | m1_subset_1(sK9,sK6) != iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_2107])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1281,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2116,plain,
    ( m1_subset_1(sK9,sK6) != iProver_top
    | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2108,c_1281])).

cnf(c_2175,plain,
    ( r2_hidden(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2116,c_28,c_29,c_1950,c_2155])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1274,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2429,plain,
    ( v1_xboole_0(sK6) != iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_1261,c_1274])).

cnf(c_794,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1624,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
    | X1 != k7_relset_1(sK5,sK6,sK8,sK7)
    | X0 != sK9 ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_1753,plain,
    ( r2_hidden(sK9,X0)
    | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
    | X0 != k7_relset_1(sK5,sK6,sK8,sK7)
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_1624])).

cnf(c_2522,plain,
    ( ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
    | r2_hidden(sK9,k9_relat_1(sK8,sK7))
    | k9_relat_1(sK8,sK7) != k7_relset_1(sK5,sK6,sK8,sK7)
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_1753])).

cnf(c_2523,plain,
    ( k9_relat_1(sK8,sK7) != k7_relset_1(sK5,sK6,sK8,sK7)
    | sK9 != sK9
    | r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2522])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | r2_hidden(k4_tarski(sK4(X4,X3,X2,X0),X0),X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1265,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | r2_hidden(k4_tarski(sK4(X4,X3,X2,X0),X0),X2) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2263,plain,
    ( m1_subset_1(sK9,sK6) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | r2_hidden(k4_tarski(sK4(sK7,sK5,sK8,sK9),sK9),sK8) = iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1262,c_1265])).

cnf(c_2797,plain,
    ( r2_hidden(k4_tarski(sK4(sK7,sK5,sK8,sK9),sK9),sK8) = iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2263,c_28,c_29,c_1950,c_2155])).

cnf(c_9,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_336,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_26])).

cnf(c_337,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK8)
    | ~ v1_relat_1(sK8)
    | k1_funct_1(sK8,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_1258,plain,
    ( k1_funct_1(sK8,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_337])).

cnf(c_338,plain,
    ( k1_funct_1(sK8,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_337])).

cnf(c_1588,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
    | k1_funct_1(sK8,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1258,c_28,c_338,c_1537])).

cnf(c_1589,plain,
    ( k1_funct_1(sK8,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_1588])).

cnf(c_2807,plain,
    ( k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) = sK9
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2797,c_1589])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2883,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),sK7)
    | ~ r2_hidden(sK9,k9_relat_1(sK8,sK7))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2884,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),sK7) = iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2883])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2881,plain,
    ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8)
    | ~ r2_hidden(sK9,k9_relat_1(sK8,sK7))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2888,plain,
    ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2881])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3784,plain,
    ( ~ r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8)
    | ~ v1_xboole_0(sK8) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3785,plain,
    ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) != iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3784])).

cnf(c_3912,plain,
    ( ~ r2_hidden(sK1(sK9,sK7,sK8),sK7)
    | ~ v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3913,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),sK7) != iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3912])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | r2_hidden(sK4(X4,X3,X2,X0),X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_4096,plain,
    ( ~ m1_subset_1(sK9,sK6)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7)
    | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
    | v1_xboole_0(sK6)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_4097,plain,
    ( m1_subset_1(sK9,sK6) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7) = iProver_top
    | r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4096])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(sK3(X1,X0),X1)
    | k1_relset_1(X1,X2,X0) = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1268,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(sK3(X0,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3338,plain,
    ( k1_relset_1(sK5,sK6,sK8) = sK5
    | r2_hidden(sK3(sK5,sK8),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1261,c_1268])).

cnf(c_3341,plain,
    ( k1_relat_1(sK8) = sK5
    | r2_hidden(sK3(sK5,sK8),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3338,c_1850])).

cnf(c_1282,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4113,plain,
    ( k1_relat_1(sK8) = sK5
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3341,c_1282])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | ~ r2_hidden(X0,sK7)
    | k1_funct_1(sK8,X0) != sK9 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_4677,plain,
    ( ~ r2_hidden(sK4(sK7,sK5,sK8,sK9),sK5)
    | ~ r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7)
    | k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) != sK9 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_4678,plain,
    ( k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) != sK9
    | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK5) != iProver_top
    | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4677])).

cnf(c_4905,plain,
    ( k1_relat_1(sK8) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4732,c_25,c_28,c_29,c_1537,c_1754,c_1950,c_2088,c_2155,c_2160,c_2161,c_2175,c_2429,c_2523,c_2807,c_2884,c_2888,c_3785,c_3913,c_4097,c_4113,c_4678])).

cnf(c_1271,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2297,plain,
    ( k7_relset_1(sK5,sK6,sK8,X0) = k9_relat_1(sK8,X0) ),
    inference(superposition,[status(thm)],[c_1261,c_1271])).

cnf(c_2550,plain,
    ( r2_hidden(sK9,k9_relat_1(sK8,sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2297,c_1262])).

cnf(c_1277,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3479,plain,
    ( k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0
    | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1277,c_1589])).

cnf(c_3825,plain,
    ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3479,c_28,c_1537])).

cnf(c_3826,plain,
    ( k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0
    | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3825])).

cnf(c_3836,plain,
    ( k1_funct_1(sK8,sK1(sK9,sK7,sK8)) = sK9 ),
    inference(superposition,[status(thm)],[c_2550,c_3826])).

cnf(c_3865,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_3836,c_1651])).

cnf(c_3971,plain,
    ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3865,c_25,c_28,c_29,c_1537,c_1754,c_2088,c_2160,c_2161,c_2523,c_2888])).

cnf(c_10,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_306,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_26])).

cnf(c_307,plain,
    ( r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(k4_tarski(X0,X1),sK8)
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_1260,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_307])).

cnf(c_1544,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK8)
    | r2_hidden(X0,k1_relat_1(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_307,c_25,c_1536])).

cnf(c_1545,plain,
    ( r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(k4_tarski(X0,X1),sK8) ),
    inference(renaming,[status(thm)],[c_1544])).

cnf(c_1546,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1545])).

cnf(c_1643,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1260,c_1546])).

cnf(c_1644,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_1643])).

cnf(c_3977,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3971,c_1644])).

cnf(c_4105,plain,
    ( v1_xboole_0(k1_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3977,c_1282])).

cnf(c_4909,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4905,c_4105])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4909,c_4678,c_4097,c_3913,c_3785,c_2888,c_2884,c_2807,c_2523,c_2429,c_2175,c_2161,c_2160,c_2155,c_2088,c_1950,c_1754,c_1537,c_29,c_28,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:25:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.83/1.05  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.05  
% 1.83/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.83/1.05  
% 1.83/1.05  ------  iProver source info
% 1.83/1.05  
% 1.83/1.05  git: date: 2020-06-30 10:37:57 +0100
% 1.83/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.83/1.05  git: non_committed_changes: false
% 1.83/1.05  git: last_make_outside_of_git: false
% 1.83/1.05  
% 1.83/1.05  ------ 
% 1.83/1.05  ------ Parsing...
% 1.83/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.83/1.05  
% 1.83/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.83/1.05  
% 1.83/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.83/1.05  
% 1.83/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.83/1.05  ------ Proving...
% 1.83/1.05  ------ Problem Properties 
% 1.83/1.05  
% 1.83/1.05  
% 1.83/1.05  clauses                                 26
% 1.83/1.05  conjectures                             3
% 1.83/1.05  EPR                                     2
% 1.83/1.05  Horn                                    19
% 1.83/1.05  unary                                   2
% 1.83/1.05  binary                                  6
% 1.83/1.05  lits                                    89
% 1.83/1.05  lits eq                                 7
% 1.83/1.05  fd_pure                                 0
% 1.83/1.05  fd_pseudo                               0
% 1.83/1.05  fd_cond                                 0
% 1.83/1.05  fd_pseudo_cond                          1
% 1.83/1.05  AC symbols                              0
% 1.83/1.05  
% 1.83/1.05  ------ Input Options Time Limit: Unbounded
% 1.83/1.05  
% 1.83/1.05  
% 1.83/1.05  ------ 
% 1.83/1.05  Current options:
% 1.83/1.05  ------ 
% 1.83/1.05  
% 1.83/1.05  
% 1.83/1.05  
% 1.83/1.05  
% 1.83/1.05  ------ Proving...
% 1.83/1.05  
% 1.83/1.05  
% 1.83/1.05  % SZS status Theorem for theBenchmark.p
% 1.83/1.05  
% 1.83/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 1.83/1.05  
% 1.83/1.05  fof(f13,conjecture,(
% 1.83/1.05    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.83/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.83/1.05  
% 1.83/1.05  fof(f14,negated_conjecture,(
% 1.83/1.05    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.83/1.05    inference(negated_conjecture,[],[f13])).
% 1.83/1.05  
% 1.83/1.05  fof(f15,plain,(
% 1.83/1.05    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.83/1.05    inference(pure_predicate_removal,[],[f14])).
% 1.83/1.05  
% 1.83/1.05  fof(f30,plain,(
% 1.83/1.05    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 1.83/1.05    inference(ennf_transformation,[],[f15])).
% 1.83/1.05  
% 1.83/1.05  fof(f31,plain,(
% 1.83/1.05    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 1.83/1.05    inference(flattening,[],[f30])).
% 1.83/1.05  
% 1.83/1.05  fof(f52,plain,(
% 1.83/1.05    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK9 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(sK9,k7_relset_1(X0,X1,X3,X2)))) )),
% 1.83/1.05    introduced(choice_axiom,[])).
% 1.83/1.05  
% 1.83/1.05  fof(f51,plain,(
% 1.83/1.05    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK8,X5) != X4 | ~r2_hidden(X5,sK7) | ~r2_hidden(X5,sK5)) & r2_hidden(X4,k7_relset_1(sK5,sK6,sK8,sK7))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_1(sK8))),
% 1.83/1.05    introduced(choice_axiom,[])).
% 1.83/1.05  
% 1.83/1.05  fof(f53,plain,(
% 1.83/1.05    (! [X5] : (k1_funct_1(sK8,X5) != sK9 | ~r2_hidden(X5,sK7) | ~r2_hidden(X5,sK5)) & r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_1(sK8)),
% 1.83/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f31,f52,f51])).
% 1.83/1.05  
% 1.83/1.05  fof(f78,plain,(
% 1.83/1.05    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 1.83/1.05    inference(cnf_transformation,[],[f53])).
% 1.83/1.05  
% 1.83/1.05  fof(f5,axiom,(
% 1.83/1.05    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.83/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.83/1.05  
% 1.83/1.05  fof(f21,plain,(
% 1.83/1.05    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.83/1.05    inference(ennf_transformation,[],[f5])).
% 1.83/1.05  
% 1.83/1.05  fof(f22,plain,(
% 1.83/1.05    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.83/1.05    inference(flattening,[],[f21])).
% 1.83/1.05  
% 1.83/1.05  fof(f40,plain,(
% 1.83/1.05    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.83/1.05    inference(nnf_transformation,[],[f22])).
% 1.83/1.05  
% 1.83/1.05  fof(f41,plain,(
% 1.83/1.05    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.83/1.05    inference(flattening,[],[f40])).
% 1.83/1.05  
% 1.83/1.05  fof(f64,plain,(
% 1.83/1.05    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.83/1.05    inference(cnf_transformation,[],[f41])).
% 1.83/1.05  
% 1.83/1.05  fof(f81,plain,(
% 1.83/1.05    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.83/1.05    inference(equality_resolution,[],[f64])).
% 1.83/1.05  
% 1.83/1.05  fof(f77,plain,(
% 1.83/1.05    v1_funct_1(sK8)),
% 1.83/1.05    inference(cnf_transformation,[],[f53])).
% 1.83/1.05  
% 1.83/1.05  fof(f6,axiom,(
% 1.83/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.83/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.83/1.05  
% 1.83/1.05  fof(f23,plain,(
% 1.83/1.05    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.83/1.05    inference(ennf_transformation,[],[f6])).
% 1.83/1.05  
% 1.83/1.05  fof(f65,plain,(
% 1.83/1.05    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.83/1.05    inference(cnf_transformation,[],[f23])).
% 1.83/1.05  
% 1.83/1.05  fof(f11,axiom,(
% 1.83/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 1.83/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.83/1.05  
% 1.83/1.05  fof(f28,plain,(
% 1.83/1.05    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.83/1.05    inference(ennf_transformation,[],[f11])).
% 1.83/1.05  
% 1.83/1.05  fof(f42,plain,(
% 1.83/1.05    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.83/1.05    inference(nnf_transformation,[],[f28])).
% 1.83/1.05  
% 1.83/1.05  fof(f43,plain,(
% 1.83/1.05    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.83/1.05    inference(rectify,[],[f42])).
% 1.83/1.05  
% 1.83/1.05  fof(f45,plain,(
% 1.83/1.05    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK3(X1,X2),X6),X2) & r2_hidden(sK3(X1,X2),X1)))),
% 1.83/1.05    introduced(choice_axiom,[])).
% 1.83/1.05  
% 1.83/1.05  fof(f44,plain,(
% 1.83/1.05    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2))),
% 1.83/1.05    introduced(choice_axiom,[])).
% 1.83/1.05  
% 1.83/1.05  fof(f46,plain,(
% 1.83/1.05    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK3(X1,X2),X6),X2) & r2_hidden(sK3(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.83/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f43,f45,f44])).
% 1.83/1.05  
% 1.83/1.05  fof(f71,plain,(
% 1.83/1.05    ( ! [X6,X2,X0,X1] : (k1_relset_1(X1,X0,X2) = X1 | ~r2_hidden(k4_tarski(sK3(X1,X2),X6),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 1.83/1.05    inference(cnf_transformation,[],[f46])).
% 1.83/1.05  
% 1.83/1.05  fof(f9,axiom,(
% 1.83/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.83/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.83/1.05  
% 1.83/1.05  fof(f26,plain,(
% 1.83/1.05    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.83/1.05    inference(ennf_transformation,[],[f9])).
% 1.83/1.05  
% 1.83/1.05  fof(f68,plain,(
% 1.83/1.05    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.83/1.05    inference(cnf_transformation,[],[f26])).
% 1.83/1.05  
% 1.83/1.05  fof(f79,plain,(
% 1.83/1.05    r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))),
% 1.83/1.05    inference(cnf_transformation,[],[f53])).
% 1.83/1.05  
% 1.83/1.05  fof(f3,axiom,(
% 1.83/1.05    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.83/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.83/1.05  
% 1.83/1.05  fof(f18,plain,(
% 1.83/1.05    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.83/1.05    inference(ennf_transformation,[],[f3])).
% 1.83/1.05  
% 1.83/1.05  fof(f19,plain,(
% 1.83/1.05    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.83/1.05    inference(flattening,[],[f18])).
% 1.83/1.05  
% 1.83/1.05  fof(f57,plain,(
% 1.83/1.05    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.83/1.05    inference(cnf_transformation,[],[f19])).
% 1.83/1.05  
% 1.83/1.05  fof(f10,axiom,(
% 1.83/1.05    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 1.83/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.83/1.05  
% 1.83/1.05  fof(f27,plain,(
% 1.83/1.05    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.83/1.05    inference(ennf_transformation,[],[f10])).
% 1.83/1.05  
% 1.83/1.05  fof(f69,plain,(
% 1.83/1.05    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.83/1.05    inference(cnf_transformation,[],[f27])).
% 1.83/1.05  
% 1.83/1.05  fof(f8,axiom,(
% 1.83/1.05    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 1.83/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.83/1.05  
% 1.83/1.05  fof(f25,plain,(
% 1.83/1.05    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.83/1.05    inference(ennf_transformation,[],[f8])).
% 1.83/1.05  
% 1.83/1.05  fof(f67,plain,(
% 1.83/1.05    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.83/1.05    inference(cnf_transformation,[],[f25])).
% 1.83/1.05  
% 1.83/1.05  fof(f12,axiom,(
% 1.83/1.05    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 1.83/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.83/1.05  
% 1.83/1.05  fof(f29,plain,(
% 1.83/1.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.83/1.05    inference(ennf_transformation,[],[f12])).
% 1.83/1.05  
% 1.83/1.05  fof(f47,plain,(
% 1.83/1.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.83/1.05    inference(nnf_transformation,[],[f29])).
% 1.83/1.05  
% 1.83/1.05  fof(f48,plain,(
% 1.83/1.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.83/1.05    inference(rectify,[],[f47])).
% 1.83/1.05  
% 1.83/1.05  fof(f49,plain,(
% 1.83/1.05    ! [X4,X3,X2,X1] : (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) => (r2_hidden(sK4(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK4(X1,X2,X3,X4),X2)))),
% 1.83/1.05    introduced(choice_axiom,[])).
% 1.83/1.05  
% 1.83/1.05  fof(f50,plain,(
% 1.83/1.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & ((r2_hidden(sK4(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK4(X1,X2,X3,X4),X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.83/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f48,f49])).
% 1.83/1.05  
% 1.83/1.05  fof(f73,plain,(
% 1.83/1.05    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK4(X1,X2,X3,X4),X2) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.83/1.05    inference(cnf_transformation,[],[f50])).
% 1.83/1.05  
% 1.83/1.05  fof(f2,axiom,(
% 1.83/1.05    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.83/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.83/1.05  
% 1.83/1.05  fof(f16,plain,(
% 1.83/1.05    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.83/1.05    inference(ennf_transformation,[],[f2])).
% 1.83/1.05  
% 1.83/1.05  fof(f17,plain,(
% 1.83/1.05    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.83/1.05    inference(flattening,[],[f16])).
% 1.83/1.05  
% 1.83/1.05  fof(f56,plain,(
% 1.83/1.05    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.83/1.05    inference(cnf_transformation,[],[f17])).
% 1.83/1.05  
% 1.83/1.05  fof(f7,axiom,(
% 1.83/1.05    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 1.83/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.83/1.05  
% 1.83/1.05  fof(f24,plain,(
% 1.83/1.05    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 1.83/1.05    inference(ennf_transformation,[],[f7])).
% 1.83/1.05  
% 1.83/1.05  fof(f66,plain,(
% 1.83/1.05    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 1.83/1.05    inference(cnf_transformation,[],[f24])).
% 1.83/1.05  
% 1.83/1.05  fof(f74,plain,(
% 1.83/1.05    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.83/1.05    inference(cnf_transformation,[],[f50])).
% 1.83/1.05  
% 1.83/1.05  fof(f63,plain,(
% 1.83/1.05    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.83/1.05    inference(cnf_transformation,[],[f41])).
% 1.83/1.05  
% 1.83/1.05  fof(f4,axiom,(
% 1.83/1.05    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.83/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.83/1.05  
% 1.83/1.05  fof(f20,plain,(
% 1.83/1.05    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.83/1.05    inference(ennf_transformation,[],[f4])).
% 1.83/1.05  
% 1.83/1.05  fof(f36,plain,(
% 1.83/1.05    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.83/1.05    inference(nnf_transformation,[],[f20])).
% 1.83/1.05  
% 1.83/1.05  fof(f37,plain,(
% 1.83/1.05    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.83/1.05    inference(rectify,[],[f36])).
% 1.83/1.05  
% 1.83/1.05  fof(f38,plain,(
% 1.83/1.05    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 1.83/1.05    introduced(choice_axiom,[])).
% 1.83/1.05  
% 1.83/1.05  fof(f39,plain,(
% 1.83/1.05    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.83/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).
% 1.83/1.05  
% 1.83/1.05  fof(f60,plain,(
% 1.83/1.05    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.83/1.05    inference(cnf_transformation,[],[f39])).
% 1.83/1.05  
% 1.83/1.05  fof(f59,plain,(
% 1.83/1.05    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.83/1.05    inference(cnf_transformation,[],[f39])).
% 1.83/1.05  
% 1.83/1.05  fof(f1,axiom,(
% 1.83/1.05    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.83/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.83/1.05  
% 1.83/1.05  fof(f32,plain,(
% 1.83/1.05    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.83/1.05    inference(nnf_transformation,[],[f1])).
% 1.83/1.05  
% 1.83/1.05  fof(f33,plain,(
% 1.83/1.05    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.83/1.05    inference(rectify,[],[f32])).
% 1.83/1.05  
% 1.83/1.05  fof(f34,plain,(
% 1.83/1.05    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.83/1.05    introduced(choice_axiom,[])).
% 1.83/1.05  
% 1.83/1.05  fof(f35,plain,(
% 1.83/1.05    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.83/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 1.83/1.05  
% 1.83/1.05  fof(f54,plain,(
% 1.83/1.05    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.83/1.05    inference(cnf_transformation,[],[f35])).
% 1.83/1.05  
% 1.83/1.05  fof(f75,plain,(
% 1.83/1.05    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK4(X1,X2,X3,X4),X1) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.83/1.05    inference(cnf_transformation,[],[f50])).
% 1.83/1.05  
% 1.83/1.05  fof(f70,plain,(
% 1.83/1.05    ( ! [X2,X0,X1] : (k1_relset_1(X1,X0,X2) = X1 | r2_hidden(sK3(X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 1.83/1.05    inference(cnf_transformation,[],[f46])).
% 1.83/1.05  
% 1.83/1.05  fof(f80,plain,(
% 1.83/1.05    ( ! [X5] : (k1_funct_1(sK8,X5) != sK9 | ~r2_hidden(X5,sK7) | ~r2_hidden(X5,sK5)) )),
% 1.83/1.05    inference(cnf_transformation,[],[f53])).
% 1.83/1.05  
% 1.83/1.05  fof(f62,plain,(
% 1.83/1.05    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.83/1.05    inference(cnf_transformation,[],[f41])).
% 1.83/1.05  
% 1.83/1.05  cnf(c_25,negated_conjecture,
% 1.83/1.05      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 1.83/1.05      inference(cnf_transformation,[],[f78]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1261,plain,
% 1.83/1.05      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 1.83/1.05      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_8,plain,
% 1.83/1.05      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.83/1.05      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 1.83/1.05      | ~ v1_funct_1(X1)
% 1.83/1.05      | ~ v1_relat_1(X1) ),
% 1.83/1.05      inference(cnf_transformation,[],[f81]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_26,negated_conjecture,
% 1.83/1.05      ( v1_funct_1(sK8) ),
% 1.83/1.05      inference(cnf_transformation,[],[f77]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_321,plain,
% 1.83/1.05      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.83/1.05      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 1.83/1.05      | ~ v1_relat_1(X1)
% 1.83/1.05      | sK8 != X1 ),
% 1.83/1.05      inference(resolution_lifted,[status(thm)],[c_8,c_26]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_322,plain,
% 1.83/1.05      ( ~ r2_hidden(X0,k1_relat_1(sK8))
% 1.83/1.05      | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8)
% 1.83/1.05      | ~ v1_relat_1(sK8) ),
% 1.83/1.05      inference(unflattening,[status(thm)],[c_321]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1259,plain,
% 1.83/1.05      ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 1.83/1.05      | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) = iProver_top
% 1.83/1.05      | v1_relat_1(sK8) != iProver_top ),
% 1.83/1.05      inference(predicate_to_equality,[status(thm)],[c_322]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_11,plain,
% 1.83/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.83/1.05      | v1_relat_1(X0) ),
% 1.83/1.05      inference(cnf_transformation,[],[f65]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1536,plain,
% 1.83/1.05      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 1.83/1.05      | v1_relat_1(sK8) ),
% 1.83/1.05      inference(instantiation,[status(thm)],[c_11]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1563,plain,
% 1.83/1.05      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8)
% 1.83/1.05      | ~ r2_hidden(X0,k1_relat_1(sK8)) ),
% 1.83/1.05      inference(global_propositional_subsumption,
% 1.83/1.05                [status(thm)],
% 1.83/1.05                [c_322,c_25,c_1536]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1564,plain,
% 1.83/1.05      ( ~ r2_hidden(X0,k1_relat_1(sK8))
% 1.83/1.05      | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) ),
% 1.83/1.05      inference(renaming,[status(thm)],[c_1563]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1565,plain,
% 1.83/1.05      ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 1.83/1.05      | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) = iProver_top ),
% 1.83/1.05      inference(predicate_to_equality,[status(thm)],[c_1564]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1650,plain,
% 1.83/1.05      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) = iProver_top
% 1.83/1.05      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
% 1.83/1.05      inference(global_propositional_subsumption,
% 1.83/1.05                [status(thm)],
% 1.83/1.05                [c_1259,c_1565]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1651,plain,
% 1.83/1.05      ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 1.83/1.05      | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) = iProver_top ),
% 1.83/1.05      inference(renaming,[status(thm)],[c_1650]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_17,plain,
% 1.83/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.83/1.05      | ~ r2_hidden(k4_tarski(sK3(X1,X0),X3),X0)
% 1.83/1.05      | k1_relset_1(X1,X2,X0) = X1 ),
% 1.83/1.05      inference(cnf_transformation,[],[f71]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1269,plain,
% 1.83/1.05      ( k1_relset_1(X0,X1,X2) = X0
% 1.83/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 1.83/1.05      | r2_hidden(k4_tarski(sK3(X0,X2),X3),X2) != iProver_top ),
% 1.83/1.05      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_4414,plain,
% 1.83/1.05      ( k1_relset_1(X0,X1,sK8) = X0
% 1.83/1.05      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 1.83/1.05      | r2_hidden(sK3(X0,sK8),k1_relat_1(sK8)) != iProver_top ),
% 1.83/1.05      inference(superposition,[status(thm)],[c_1651,c_1269]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_4731,plain,
% 1.83/1.05      ( k1_relset_1(sK5,sK6,sK8) = sK5
% 1.83/1.05      | r2_hidden(sK3(sK5,sK8),k1_relat_1(sK8)) != iProver_top ),
% 1.83/1.05      inference(superposition,[status(thm)],[c_1261,c_4414]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_14,plain,
% 1.83/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.83/1.05      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.83/1.05      inference(cnf_transformation,[],[f68]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1272,plain,
% 1.83/1.05      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.83/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.83/1.05      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1850,plain,
% 1.83/1.05      ( k1_relset_1(sK5,sK6,sK8) = k1_relat_1(sK8) ),
% 1.83/1.05      inference(superposition,[status(thm)],[c_1261,c_1272]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_4732,plain,
% 1.83/1.05      ( k1_relat_1(sK8) = sK5
% 1.83/1.05      | r2_hidden(sK3(sK5,sK8),k1_relat_1(sK8)) != iProver_top ),
% 1.83/1.05      inference(demodulation,[status(thm)],[c_4731,c_1850]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_28,plain,
% 1.83/1.05      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 1.83/1.05      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_24,negated_conjecture,
% 1.83/1.05      ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
% 1.83/1.05      inference(cnf_transformation,[],[f79]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_29,plain,
% 1.83/1.05      ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top ),
% 1.83/1.05      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1537,plain,
% 1.83/1.05      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 1.83/1.05      | v1_relat_1(sK8) = iProver_top ),
% 1.83/1.05      inference(predicate_to_equality,[status(thm)],[c_1536]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_792,plain,( X0 = X0 ),theory(equality) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1754,plain,
% 1.83/1.05      ( sK9 = sK9 ),
% 1.83/1.05      inference(instantiation,[status(thm)],[c_792]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_3,plain,
% 1.83/1.05      ( m1_subset_1(X0,X1)
% 1.83/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 1.83/1.05      | ~ r2_hidden(X0,X2) ),
% 1.83/1.05      inference(cnf_transformation,[],[f57]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1748,plain,
% 1.83/1.05      ( m1_subset_1(X0,sK6)
% 1.83/1.05      | ~ m1_subset_1(k7_relset_1(sK5,sK6,sK8,X1),k1_zfmisc_1(sK6))
% 1.83/1.05      | ~ r2_hidden(X0,k7_relset_1(sK5,sK6,sK8,X1)) ),
% 1.83/1.05      inference(instantiation,[status(thm)],[c_3]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1949,plain,
% 1.83/1.05      ( ~ m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6))
% 1.83/1.05      | m1_subset_1(sK9,sK6)
% 1.83/1.05      | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
% 1.83/1.05      inference(instantiation,[status(thm)],[c_1748]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1950,plain,
% 1.83/1.05      ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6)) != iProver_top
% 1.83/1.05      | m1_subset_1(sK9,sK6) = iProver_top
% 1.83/1.05      | r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top ),
% 1.83/1.05      inference(predicate_to_equality,[status(thm)],[c_1949]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_15,plain,
% 1.83/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.83/1.05      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 1.83/1.05      inference(cnf_transformation,[],[f69]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1634,plain,
% 1.83/1.05      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 1.83/1.05      | k7_relset_1(sK5,sK6,sK8,X0) = k9_relat_1(sK8,X0) ),
% 1.83/1.05      inference(instantiation,[status(thm)],[c_15]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_2088,plain,
% 1.83/1.05      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 1.83/1.05      | k7_relset_1(sK5,sK6,sK8,sK7) = k9_relat_1(sK8,sK7) ),
% 1.83/1.05      inference(instantiation,[status(thm)],[c_1634]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_13,plain,
% 1.83/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.83/1.05      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
% 1.83/1.05      inference(cnf_transformation,[],[f67]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1619,plain,
% 1.83/1.05      ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,X0),k1_zfmisc_1(sK6))
% 1.83/1.05      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 1.83/1.05      inference(instantiation,[status(thm)],[c_13]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_2154,plain,
% 1.83/1.05      ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6))
% 1.83/1.05      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 1.83/1.05      inference(instantiation,[status(thm)],[c_1619]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_2155,plain,
% 1.83/1.05      ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6)) = iProver_top
% 1.83/1.05      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
% 1.83/1.05      inference(predicate_to_equality,[status(thm)],[c_2154]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_793,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1888,plain,
% 1.83/1.05      ( X0 != X1
% 1.83/1.05      | X0 = k7_relset_1(sK5,sK6,sK8,sK7)
% 1.83/1.05      | k7_relset_1(sK5,sK6,sK8,sK7) != X1 ),
% 1.83/1.05      inference(instantiation,[status(thm)],[c_793]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_2087,plain,
% 1.83/1.05      ( X0 = k7_relset_1(sK5,sK6,sK8,sK7)
% 1.83/1.05      | X0 != k9_relat_1(sK8,sK7)
% 1.83/1.05      | k7_relset_1(sK5,sK6,sK8,sK7) != k9_relat_1(sK8,sK7) ),
% 1.83/1.05      inference(instantiation,[status(thm)],[c_1888]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_2160,plain,
% 1.83/1.05      ( k7_relset_1(sK5,sK6,sK8,sK7) != k9_relat_1(sK8,sK7)
% 1.83/1.05      | k9_relat_1(sK8,sK7) = k7_relset_1(sK5,sK6,sK8,sK7)
% 1.83/1.05      | k9_relat_1(sK8,sK7) != k9_relat_1(sK8,sK7) ),
% 1.83/1.05      inference(instantiation,[status(thm)],[c_2087]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_2161,plain,
% 1.83/1.05      ( k9_relat_1(sK8,sK7) = k9_relat_1(sK8,sK7) ),
% 1.83/1.05      inference(instantiation,[status(thm)],[c_792]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1262,plain,
% 1.83/1.05      ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top ),
% 1.83/1.05      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_22,plain,
% 1.83/1.05      ( ~ m1_subset_1(X0,X1)
% 1.83/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 1.83/1.05      | m1_subset_1(sK4(X4,X3,X2,X0),X3)
% 1.83/1.05      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 1.83/1.05      | v1_xboole_0(X1)
% 1.83/1.05      | v1_xboole_0(X3)
% 1.83/1.05      | v1_xboole_0(X4) ),
% 1.83/1.05      inference(cnf_transformation,[],[f73]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1264,plain,
% 1.83/1.05      ( m1_subset_1(X0,X1) != iProver_top
% 1.83/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 1.83/1.05      | m1_subset_1(sK4(X4,X3,X2,X0),X3) = iProver_top
% 1.83/1.05      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 1.83/1.05      | v1_xboole_0(X1) = iProver_top
% 1.83/1.05      | v1_xboole_0(X3) = iProver_top
% 1.83/1.05      | v1_xboole_0(X4) = iProver_top ),
% 1.83/1.05      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1769,plain,
% 1.83/1.05      ( m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
% 1.83/1.05      | m1_subset_1(sK9,sK6) != iProver_top
% 1.83/1.05      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 1.83/1.05      | v1_xboole_0(sK6) = iProver_top
% 1.83/1.05      | v1_xboole_0(sK5) = iProver_top
% 1.83/1.05      | v1_xboole_0(sK7) = iProver_top ),
% 1.83/1.05      inference(superposition,[status(thm)],[c_1262,c_1264]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_2107,plain,
% 1.83/1.05      ( m1_subset_1(sK9,sK6) != iProver_top
% 1.83/1.05      | m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
% 1.83/1.05      | v1_xboole_0(sK6) = iProver_top
% 1.83/1.05      | v1_xboole_0(sK5) = iProver_top
% 1.83/1.05      | v1_xboole_0(sK7) = iProver_top ),
% 1.83/1.05      inference(global_propositional_subsumption,
% 1.83/1.05                [status(thm)],
% 1.83/1.05                [c_1769,c_28]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_2108,plain,
% 1.83/1.05      ( m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
% 1.83/1.05      | m1_subset_1(sK9,sK6) != iProver_top
% 1.83/1.05      | v1_xboole_0(sK6) = iProver_top
% 1.83/1.05      | v1_xboole_0(sK5) = iProver_top
% 1.83/1.05      | v1_xboole_0(sK7) = iProver_top ),
% 1.83/1.05      inference(renaming,[status(thm)],[c_2107]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_2,plain,
% 1.83/1.05      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.83/1.05      inference(cnf_transformation,[],[f56]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1281,plain,
% 1.83/1.05      ( m1_subset_1(X0,X1) != iProver_top
% 1.83/1.05      | r2_hidden(X0,X1) = iProver_top
% 1.83/1.05      | v1_xboole_0(X1) = iProver_top ),
% 1.83/1.05      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_2116,plain,
% 1.83/1.05      ( m1_subset_1(sK9,sK6) != iProver_top
% 1.83/1.05      | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
% 1.83/1.05      | v1_xboole_0(sK6) = iProver_top
% 1.83/1.05      | v1_xboole_0(sK5) = iProver_top
% 1.83/1.05      | v1_xboole_0(sK7) = iProver_top ),
% 1.83/1.05      inference(superposition,[status(thm)],[c_2108,c_1281]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_2175,plain,
% 1.83/1.05      ( r2_hidden(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
% 1.83/1.05      | v1_xboole_0(sK6) = iProver_top
% 1.83/1.05      | v1_xboole_0(sK5) = iProver_top
% 1.83/1.05      | v1_xboole_0(sK7) = iProver_top ),
% 1.83/1.05      inference(global_propositional_subsumption,
% 1.83/1.05                [status(thm)],
% 1.83/1.05                [c_2116,c_28,c_29,c_1950,c_2155]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_12,plain,
% 1.83/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.83/1.05      | ~ v1_xboole_0(X2)
% 1.83/1.05      | v1_xboole_0(X0) ),
% 1.83/1.05      inference(cnf_transformation,[],[f66]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1274,plain,
% 1.83/1.05      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 1.83/1.05      | v1_xboole_0(X2) != iProver_top
% 1.83/1.05      | v1_xboole_0(X0) = iProver_top ),
% 1.83/1.05      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_2429,plain,
% 1.83/1.05      ( v1_xboole_0(sK6) != iProver_top
% 1.83/1.05      | v1_xboole_0(sK8) = iProver_top ),
% 1.83/1.05      inference(superposition,[status(thm)],[c_1261,c_1274]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_794,plain,
% 1.83/1.05      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.83/1.05      theory(equality) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1624,plain,
% 1.83/1.05      ( r2_hidden(X0,X1)
% 1.83/1.05      | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
% 1.83/1.05      | X1 != k7_relset_1(sK5,sK6,sK8,sK7)
% 1.83/1.05      | X0 != sK9 ),
% 1.83/1.05      inference(instantiation,[status(thm)],[c_794]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1753,plain,
% 1.83/1.05      ( r2_hidden(sK9,X0)
% 1.83/1.05      | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
% 1.83/1.05      | X0 != k7_relset_1(sK5,sK6,sK8,sK7)
% 1.83/1.05      | sK9 != sK9 ),
% 1.83/1.05      inference(instantiation,[status(thm)],[c_1624]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_2522,plain,
% 1.83/1.05      ( ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
% 1.83/1.05      | r2_hidden(sK9,k9_relat_1(sK8,sK7))
% 1.83/1.05      | k9_relat_1(sK8,sK7) != k7_relset_1(sK5,sK6,sK8,sK7)
% 1.83/1.05      | sK9 != sK9 ),
% 1.83/1.05      inference(instantiation,[status(thm)],[c_1753]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_2523,plain,
% 1.83/1.05      ( k9_relat_1(sK8,sK7) != k7_relset_1(sK5,sK6,sK8,sK7)
% 1.83/1.05      | sK9 != sK9
% 1.83/1.05      | r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top
% 1.83/1.05      | r2_hidden(sK9,k9_relat_1(sK8,sK7)) = iProver_top ),
% 1.83/1.05      inference(predicate_to_equality,[status(thm)],[c_2522]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_21,plain,
% 1.83/1.05      ( ~ m1_subset_1(X0,X1)
% 1.83/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 1.83/1.05      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 1.83/1.05      | r2_hidden(k4_tarski(sK4(X4,X3,X2,X0),X0),X2)
% 1.83/1.05      | v1_xboole_0(X1)
% 1.83/1.05      | v1_xboole_0(X3)
% 1.83/1.05      | v1_xboole_0(X4) ),
% 1.83/1.05      inference(cnf_transformation,[],[f74]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1265,plain,
% 1.83/1.05      ( m1_subset_1(X0,X1) != iProver_top
% 1.83/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 1.83/1.05      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 1.83/1.05      | r2_hidden(k4_tarski(sK4(X4,X3,X2,X0),X0),X2) = iProver_top
% 1.83/1.05      | v1_xboole_0(X1) = iProver_top
% 1.83/1.05      | v1_xboole_0(X3) = iProver_top
% 1.83/1.05      | v1_xboole_0(X4) = iProver_top ),
% 1.83/1.05      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_2263,plain,
% 1.83/1.05      ( m1_subset_1(sK9,sK6) != iProver_top
% 1.83/1.05      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 1.83/1.05      | r2_hidden(k4_tarski(sK4(sK7,sK5,sK8,sK9),sK9),sK8) = iProver_top
% 1.83/1.05      | v1_xboole_0(sK6) = iProver_top
% 1.83/1.05      | v1_xboole_0(sK5) = iProver_top
% 1.83/1.05      | v1_xboole_0(sK7) = iProver_top ),
% 1.83/1.05      inference(superposition,[status(thm)],[c_1262,c_1265]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_2797,plain,
% 1.83/1.05      ( r2_hidden(k4_tarski(sK4(sK7,sK5,sK8,sK9),sK9),sK8) = iProver_top
% 1.83/1.05      | v1_xboole_0(sK6) = iProver_top
% 1.83/1.05      | v1_xboole_0(sK5) = iProver_top
% 1.83/1.05      | v1_xboole_0(sK7) = iProver_top ),
% 1.83/1.05      inference(global_propositional_subsumption,
% 1.83/1.05                [status(thm)],
% 1.83/1.05                [c_2263,c_28,c_29,c_1950,c_2155]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_9,plain,
% 1.83/1.05      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 1.83/1.05      | ~ v1_funct_1(X2)
% 1.83/1.05      | ~ v1_relat_1(X2)
% 1.83/1.05      | k1_funct_1(X2,X0) = X1 ),
% 1.83/1.05      inference(cnf_transformation,[],[f63]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_336,plain,
% 1.83/1.05      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 1.83/1.05      | ~ v1_relat_1(X2)
% 1.83/1.05      | k1_funct_1(X2,X0) = X1
% 1.83/1.05      | sK8 != X2 ),
% 1.83/1.05      inference(resolution_lifted,[status(thm)],[c_9,c_26]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_337,plain,
% 1.83/1.05      ( ~ r2_hidden(k4_tarski(X0,X1),sK8)
% 1.83/1.05      | ~ v1_relat_1(sK8)
% 1.83/1.05      | k1_funct_1(sK8,X0) = X1 ),
% 1.83/1.05      inference(unflattening,[status(thm)],[c_336]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1258,plain,
% 1.83/1.05      ( k1_funct_1(sK8,X0) = X1
% 1.83/1.05      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
% 1.83/1.05      | v1_relat_1(sK8) != iProver_top ),
% 1.83/1.05      inference(predicate_to_equality,[status(thm)],[c_337]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_338,plain,
% 1.83/1.05      ( k1_funct_1(sK8,X0) = X1
% 1.83/1.05      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
% 1.83/1.05      | v1_relat_1(sK8) != iProver_top ),
% 1.83/1.05      inference(predicate_to_equality,[status(thm)],[c_337]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1588,plain,
% 1.83/1.05      ( r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
% 1.83/1.05      | k1_funct_1(sK8,X0) = X1 ),
% 1.83/1.05      inference(global_propositional_subsumption,
% 1.83/1.05                [status(thm)],
% 1.83/1.05                [c_1258,c_28,c_338,c_1537]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1589,plain,
% 1.83/1.05      ( k1_funct_1(sK8,X0) = X1
% 1.83/1.05      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top ),
% 1.83/1.05      inference(renaming,[status(thm)],[c_1588]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_2807,plain,
% 1.83/1.05      ( k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) = sK9
% 1.83/1.05      | v1_xboole_0(sK6) = iProver_top
% 1.83/1.05      | v1_xboole_0(sK5) = iProver_top
% 1.83/1.05      | v1_xboole_0(sK7) = iProver_top ),
% 1.83/1.05      inference(superposition,[status(thm)],[c_2797,c_1589]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_5,plain,
% 1.83/1.05      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 1.83/1.05      | r2_hidden(sK1(X0,X2,X1),X2)
% 1.83/1.05      | ~ v1_relat_1(X1) ),
% 1.83/1.05      inference(cnf_transformation,[],[f60]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_2883,plain,
% 1.83/1.05      ( r2_hidden(sK1(sK9,sK7,sK8),sK7)
% 1.83/1.05      | ~ r2_hidden(sK9,k9_relat_1(sK8,sK7))
% 1.83/1.05      | ~ v1_relat_1(sK8) ),
% 1.83/1.05      inference(instantiation,[status(thm)],[c_5]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_2884,plain,
% 1.83/1.05      ( r2_hidden(sK1(sK9,sK7,sK8),sK7) = iProver_top
% 1.83/1.05      | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
% 1.83/1.05      | v1_relat_1(sK8) != iProver_top ),
% 1.83/1.05      inference(predicate_to_equality,[status(thm)],[c_2883]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_6,plain,
% 1.83/1.05      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 1.83/1.05      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 1.83/1.05      | ~ v1_relat_1(X1) ),
% 1.83/1.05      inference(cnf_transformation,[],[f59]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_2881,plain,
% 1.83/1.05      ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8)
% 1.83/1.05      | ~ r2_hidden(sK9,k9_relat_1(sK8,sK7))
% 1.83/1.05      | ~ v1_relat_1(sK8) ),
% 1.83/1.05      inference(instantiation,[status(thm)],[c_6]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_2888,plain,
% 1.83/1.05      ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top
% 1.83/1.05      | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
% 1.83/1.05      | v1_relat_1(sK8) != iProver_top ),
% 1.83/1.05      inference(predicate_to_equality,[status(thm)],[c_2881]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1,plain,
% 1.83/1.05      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 1.83/1.05      inference(cnf_transformation,[],[f54]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_3784,plain,
% 1.83/1.05      ( ~ r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8)
% 1.83/1.05      | ~ v1_xboole_0(sK8) ),
% 1.83/1.05      inference(instantiation,[status(thm)],[c_1]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_3785,plain,
% 1.83/1.05      ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) != iProver_top
% 1.83/1.05      | v1_xboole_0(sK8) != iProver_top ),
% 1.83/1.05      inference(predicate_to_equality,[status(thm)],[c_3784]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_3912,plain,
% 1.83/1.05      ( ~ r2_hidden(sK1(sK9,sK7,sK8),sK7) | ~ v1_xboole_0(sK7) ),
% 1.83/1.05      inference(instantiation,[status(thm)],[c_1]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_3913,plain,
% 1.83/1.05      ( r2_hidden(sK1(sK9,sK7,sK8),sK7) != iProver_top
% 1.83/1.05      | v1_xboole_0(sK7) != iProver_top ),
% 1.83/1.05      inference(predicate_to_equality,[status(thm)],[c_3912]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_20,plain,
% 1.83/1.05      ( ~ m1_subset_1(X0,X1)
% 1.83/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 1.83/1.05      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 1.83/1.05      | r2_hidden(sK4(X4,X3,X2,X0),X4)
% 1.83/1.05      | v1_xboole_0(X1)
% 1.83/1.05      | v1_xboole_0(X3)
% 1.83/1.05      | v1_xboole_0(X4) ),
% 1.83/1.05      inference(cnf_transformation,[],[f75]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_4096,plain,
% 1.83/1.05      ( ~ m1_subset_1(sK9,sK6)
% 1.83/1.05      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 1.83/1.05      | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7)
% 1.83/1.05      | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
% 1.83/1.05      | v1_xboole_0(sK6)
% 1.83/1.05      | v1_xboole_0(sK5)
% 1.83/1.05      | v1_xboole_0(sK7) ),
% 1.83/1.05      inference(instantiation,[status(thm)],[c_20]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_4097,plain,
% 1.83/1.05      ( m1_subset_1(sK9,sK6) != iProver_top
% 1.83/1.05      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 1.83/1.05      | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7) = iProver_top
% 1.83/1.05      | r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top
% 1.83/1.05      | v1_xboole_0(sK6) = iProver_top
% 1.83/1.05      | v1_xboole_0(sK5) = iProver_top
% 1.83/1.05      | v1_xboole_0(sK7) = iProver_top ),
% 1.83/1.05      inference(predicate_to_equality,[status(thm)],[c_4096]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_18,plain,
% 1.83/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.83/1.05      | r2_hidden(sK3(X1,X0),X1)
% 1.83/1.05      | k1_relset_1(X1,X2,X0) = X1 ),
% 1.83/1.05      inference(cnf_transformation,[],[f70]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1268,plain,
% 1.83/1.05      ( k1_relset_1(X0,X1,X2) = X0
% 1.83/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 1.83/1.05      | r2_hidden(sK3(X0,X2),X0) = iProver_top ),
% 1.83/1.05      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_3338,plain,
% 1.83/1.05      ( k1_relset_1(sK5,sK6,sK8) = sK5
% 1.83/1.05      | r2_hidden(sK3(sK5,sK8),sK5) = iProver_top ),
% 1.83/1.05      inference(superposition,[status(thm)],[c_1261,c_1268]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_3341,plain,
% 1.83/1.05      ( k1_relat_1(sK8) = sK5
% 1.83/1.05      | r2_hidden(sK3(sK5,sK8),sK5) = iProver_top ),
% 1.83/1.05      inference(demodulation,[status(thm)],[c_3338,c_1850]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1282,plain,
% 1.83/1.05      ( r2_hidden(X0,X1) != iProver_top
% 1.83/1.05      | v1_xboole_0(X1) != iProver_top ),
% 1.83/1.05      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_4113,plain,
% 1.83/1.05      ( k1_relat_1(sK8) = sK5 | v1_xboole_0(sK5) != iProver_top ),
% 1.83/1.05      inference(superposition,[status(thm)],[c_3341,c_1282]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_23,negated_conjecture,
% 1.83/1.05      ( ~ r2_hidden(X0,sK5)
% 1.83/1.05      | ~ r2_hidden(X0,sK7)
% 1.83/1.05      | k1_funct_1(sK8,X0) != sK9 ),
% 1.83/1.05      inference(cnf_transformation,[],[f80]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_4677,plain,
% 1.83/1.05      ( ~ r2_hidden(sK4(sK7,sK5,sK8,sK9),sK5)
% 1.83/1.05      | ~ r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7)
% 1.83/1.05      | k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) != sK9 ),
% 1.83/1.05      inference(instantiation,[status(thm)],[c_23]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_4678,plain,
% 1.83/1.05      ( k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) != sK9
% 1.83/1.05      | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK5) != iProver_top
% 1.83/1.05      | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7) != iProver_top ),
% 1.83/1.05      inference(predicate_to_equality,[status(thm)],[c_4677]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_4905,plain,
% 1.83/1.05      ( k1_relat_1(sK8) = sK5 ),
% 1.83/1.05      inference(global_propositional_subsumption,
% 1.83/1.05                [status(thm)],
% 1.83/1.05                [c_4732,c_25,c_28,c_29,c_1537,c_1754,c_1950,c_2088,
% 1.83/1.05                 c_2155,c_2160,c_2161,c_2175,c_2429,c_2523,c_2807,c_2884,
% 1.83/1.05                 c_2888,c_3785,c_3913,c_4097,c_4113,c_4678]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1271,plain,
% 1.83/1.05      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 1.83/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.83/1.05      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_2297,plain,
% 1.83/1.05      ( k7_relset_1(sK5,sK6,sK8,X0) = k9_relat_1(sK8,X0) ),
% 1.83/1.05      inference(superposition,[status(thm)],[c_1261,c_1271]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_2550,plain,
% 1.83/1.05      ( r2_hidden(sK9,k9_relat_1(sK8,sK7)) = iProver_top ),
% 1.83/1.05      inference(demodulation,[status(thm)],[c_2297,c_1262]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1277,plain,
% 1.83/1.05      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 1.83/1.05      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
% 1.83/1.05      | v1_relat_1(X1) != iProver_top ),
% 1.83/1.05      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_3479,plain,
% 1.83/1.05      ( k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0
% 1.83/1.05      | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 1.83/1.05      | v1_relat_1(sK8) != iProver_top ),
% 1.83/1.05      inference(superposition,[status(thm)],[c_1277,c_1589]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_3825,plain,
% 1.83/1.05      ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 1.83/1.05      | k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0 ),
% 1.83/1.05      inference(global_propositional_subsumption,
% 1.83/1.05                [status(thm)],
% 1.83/1.05                [c_3479,c_28,c_1537]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_3826,plain,
% 1.83/1.05      ( k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0
% 1.83/1.05      | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top ),
% 1.83/1.05      inference(renaming,[status(thm)],[c_3825]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_3836,plain,
% 1.83/1.05      ( k1_funct_1(sK8,sK1(sK9,sK7,sK8)) = sK9 ),
% 1.83/1.05      inference(superposition,[status(thm)],[c_2550,c_3826]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_3865,plain,
% 1.83/1.05      ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) != iProver_top
% 1.83/1.05      | r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top ),
% 1.83/1.05      inference(superposition,[status(thm)],[c_3836,c_1651]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_3971,plain,
% 1.83/1.05      ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top ),
% 1.83/1.05      inference(global_propositional_subsumption,
% 1.83/1.05                [status(thm)],
% 1.83/1.05                [c_3865,c_25,c_28,c_29,c_1537,c_1754,c_2088,c_2160,
% 1.83/1.05                 c_2161,c_2523,c_2888]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_10,plain,
% 1.83/1.05      ( r2_hidden(X0,k1_relat_1(X1))
% 1.83/1.05      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 1.83/1.05      | ~ v1_funct_1(X1)
% 1.83/1.05      | ~ v1_relat_1(X1) ),
% 1.83/1.05      inference(cnf_transformation,[],[f62]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_306,plain,
% 1.83/1.05      ( r2_hidden(X0,k1_relat_1(X1))
% 1.83/1.05      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 1.83/1.05      | ~ v1_relat_1(X1)
% 1.83/1.05      | sK8 != X1 ),
% 1.83/1.05      inference(resolution_lifted,[status(thm)],[c_10,c_26]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_307,plain,
% 1.83/1.05      ( r2_hidden(X0,k1_relat_1(sK8))
% 1.83/1.05      | ~ r2_hidden(k4_tarski(X0,X1),sK8)
% 1.83/1.05      | ~ v1_relat_1(sK8) ),
% 1.83/1.05      inference(unflattening,[status(thm)],[c_306]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1260,plain,
% 1.83/1.05      ( r2_hidden(X0,k1_relat_1(sK8)) = iProver_top
% 1.83/1.05      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
% 1.83/1.05      | v1_relat_1(sK8) != iProver_top ),
% 1.83/1.05      inference(predicate_to_equality,[status(thm)],[c_307]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1544,plain,
% 1.83/1.05      ( ~ r2_hidden(k4_tarski(X0,X1),sK8)
% 1.83/1.05      | r2_hidden(X0,k1_relat_1(sK8)) ),
% 1.83/1.05      inference(global_propositional_subsumption,
% 1.83/1.05                [status(thm)],
% 1.83/1.05                [c_307,c_25,c_1536]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1545,plain,
% 1.83/1.05      ( r2_hidden(X0,k1_relat_1(sK8))
% 1.83/1.05      | ~ r2_hidden(k4_tarski(X0,X1),sK8) ),
% 1.83/1.05      inference(renaming,[status(thm)],[c_1544]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1546,plain,
% 1.83/1.05      ( r2_hidden(X0,k1_relat_1(sK8)) = iProver_top
% 1.83/1.05      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top ),
% 1.83/1.05      inference(predicate_to_equality,[status(thm)],[c_1545]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1643,plain,
% 1.83/1.05      ( r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
% 1.83/1.05      | r2_hidden(X0,k1_relat_1(sK8)) = iProver_top ),
% 1.83/1.05      inference(global_propositional_subsumption,
% 1.83/1.05                [status(thm)],
% 1.83/1.05                [c_1260,c_1546]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_1644,plain,
% 1.83/1.05      ( r2_hidden(X0,k1_relat_1(sK8)) = iProver_top
% 1.83/1.05      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top ),
% 1.83/1.05      inference(renaming,[status(thm)],[c_1643]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_3977,plain,
% 1.83/1.05      ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) = iProver_top ),
% 1.83/1.05      inference(superposition,[status(thm)],[c_3971,c_1644]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_4105,plain,
% 1.83/1.05      ( v1_xboole_0(k1_relat_1(sK8)) != iProver_top ),
% 1.83/1.05      inference(superposition,[status(thm)],[c_3977,c_1282]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(c_4909,plain,
% 1.83/1.05      ( v1_xboole_0(sK5) != iProver_top ),
% 1.83/1.05      inference(demodulation,[status(thm)],[c_4905,c_4105]) ).
% 1.83/1.05  
% 1.83/1.05  cnf(contradiction,plain,
% 1.83/1.05      ( $false ),
% 1.83/1.05      inference(minisat,
% 1.83/1.05                [status(thm)],
% 1.83/1.05                [c_4909,c_4678,c_4097,c_3913,c_3785,c_2888,c_2884,c_2807,
% 1.83/1.05                 c_2523,c_2429,c_2175,c_2161,c_2160,c_2155,c_2088,c_1950,
% 1.83/1.05                 c_1754,c_1537,c_29,c_28,c_25]) ).
% 1.83/1.05  
% 1.83/1.05  
% 1.83/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 1.83/1.05  
% 1.83/1.05  ------                               Statistics
% 1.83/1.05  
% 1.83/1.05  ------ Selected
% 1.83/1.05  
% 1.83/1.05  total_time:                             0.224
% 1.83/1.05  
%------------------------------------------------------------------------------
