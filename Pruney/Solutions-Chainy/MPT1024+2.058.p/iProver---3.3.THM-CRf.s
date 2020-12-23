%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:59 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 355 expanded)
%              Number of clauses        :   59 ( 128 expanded)
%              Number of leaves         :   13 (  73 expanded)
%              Depth                    :   22
%              Number of atoms          :  371 (1470 expanded)
%              Number of equality atoms :  106 ( 301 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK6
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X5,X0) )
        & r2_hidden(sK6,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
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
              ( k1_funct_1(sK5,X5) != X4
              | ~ r2_hidden(X5,sK4)
              | ~ r2_hidden(X5,sK2) )
          & r2_hidden(X4,k7_relset_1(sK2,sK3,sK5,sK4)) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ! [X5] :
        ( k1_funct_1(sK5,X5) != sK6
        | ~ r2_hidden(X5,sK4)
        | ~ r2_hidden(X5,sK2) )
    & r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f19,f34,f33])).

fof(f55,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f58,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f52])).

fof(f54,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f24])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f56,plain,(
    r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) ),
    inference(cnf_transformation,[],[f35])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f57,plain,(
    ! [X5] :
      ( k1_funct_1(sK5,X5) != sK6
      | ~ r2_hidden(X5,sK4)
      | ~ r2_hidden(X5,sK2) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1374,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK1(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1372,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1368,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1377,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1694,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1368,c_1377])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_357,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_358,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5)
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_1365,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_358])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1382,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2455,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),X1) = iProver_top
    | r1_tarski(sK5,X1) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1365,c_1382])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_173,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_174,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_173])).

cnf(c_219,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_174])).

cnf(c_1367,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_219])).

cnf(c_2269,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1694,c_1367])).

cnf(c_9,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1376,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2279,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2269,c_1376])).

cnf(c_2831,plain,
    ( r1_tarski(sK5,X1) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),X1) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2455,c_2279])).

cnf(c_2832,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),X1) = iProver_top
    | r1_tarski(sK5,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2831])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1379,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2843,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r1_tarski(sK5,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2832,c_1379])).

cnf(c_2953,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1694,c_2843])).

cnf(c_2963,plain,
    ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | r2_hidden(sK1(X0,X1,sK5),sK2) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1372,c_2953])).

cnf(c_4034,plain,
    ( r2_hidden(sK1(X0,X1,sK5),sK2) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2963,c_2279])).

cnf(c_4035,plain,
    ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | r2_hidden(sK1(X0,X1,sK5),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_4034])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1371,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1778,plain,
    ( k7_relset_1(sK2,sK3,sK5,X0) = k9_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_1368,c_1371])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1369,plain,
    ( r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1974,plain,
    ( r2_hidden(sK6,k9_relat_1(sK5,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1778,c_1369])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1373,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_15,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_372,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_21])).

cnf(c_373,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK5)
    | ~ v1_relat_1(sK5)
    | k1_funct_1(sK5,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_372])).

cnf(c_1364,plain,
    ( k1_funct_1(sK5,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_373])).

cnf(c_2550,plain,
    ( k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0
    | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1373,c_1364])).

cnf(c_2691,plain,
    ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2550,c_2279])).

cnf(c_2692,plain,
    ( k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0
    | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2691])).

cnf(c_2702,plain,
    ( k1_funct_1(sK5,sK1(sK6,sK4,sK5)) = sK6 ),
    inference(superposition,[status(thm)],[c_1974,c_2692])).

cnf(c_18,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(X0,sK4)
    | k1_funct_1(sK5,X0) != sK6 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1370,plain,
    ( k1_funct_1(sK5,X0) != sK6
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2764,plain,
    ( r2_hidden(sK1(sK6,sK4,sK5),sK2) != iProver_top
    | r2_hidden(sK1(sK6,sK4,sK5),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2702,c_1370])).

cnf(c_4043,plain,
    ( r2_hidden(sK1(sK6,sK4,sK5),sK4) != iProver_top
    | r2_hidden(sK6,k9_relat_1(sK5,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4035,c_2764])).

cnf(c_4059,plain,
    ( r2_hidden(sK1(sK6,sK4,sK5),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4043,c_1974])).

cnf(c_4064,plain,
    ( r2_hidden(sK6,k9_relat_1(sK5,sK4)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1374,c_4059])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4064,c_2279,c_1974])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:49:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.79/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/0.99  
% 2.79/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.79/0.99  
% 2.79/0.99  ------  iProver source info
% 2.79/0.99  
% 2.79/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.79/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.79/0.99  git: non_committed_changes: false
% 2.79/0.99  git: last_make_outside_of_git: false
% 2.79/0.99  
% 2.79/0.99  ------ 
% 2.79/0.99  
% 2.79/0.99  ------ Input Options
% 2.79/0.99  
% 2.79/0.99  --out_options                           all
% 2.79/0.99  --tptp_safe_out                         true
% 2.79/0.99  --problem_path                          ""
% 2.79/0.99  --include_path                          ""
% 2.79/0.99  --clausifier                            res/vclausify_rel
% 2.79/0.99  --clausifier_options                    --mode clausify
% 2.79/0.99  --stdin                                 false
% 2.79/0.99  --stats_out                             all
% 2.79/0.99  
% 2.79/0.99  ------ General Options
% 2.79/0.99  
% 2.79/0.99  --fof                                   false
% 2.79/0.99  --time_out_real                         305.
% 2.79/0.99  --time_out_virtual                      -1.
% 2.79/0.99  --symbol_type_check                     false
% 2.79/0.99  --clausify_out                          false
% 2.79/0.99  --sig_cnt_out                           false
% 2.79/0.99  --trig_cnt_out                          false
% 2.79/0.99  --trig_cnt_out_tolerance                1.
% 2.79/0.99  --trig_cnt_out_sk_spl                   false
% 2.79/0.99  --abstr_cl_out                          false
% 2.79/0.99  
% 2.79/0.99  ------ Global Options
% 2.79/0.99  
% 2.79/0.99  --schedule                              default
% 2.79/0.99  --add_important_lit                     false
% 2.79/0.99  --prop_solver_per_cl                    1000
% 2.79/0.99  --min_unsat_core                        false
% 2.79/0.99  --soft_assumptions                      false
% 2.79/0.99  --soft_lemma_size                       3
% 2.79/0.99  --prop_impl_unit_size                   0
% 2.79/0.99  --prop_impl_unit                        []
% 2.79/0.99  --share_sel_clauses                     true
% 2.79/0.99  --reset_solvers                         false
% 2.79/0.99  --bc_imp_inh                            [conj_cone]
% 2.79/0.99  --conj_cone_tolerance                   3.
% 2.79/0.99  --extra_neg_conj                        none
% 2.79/0.99  --large_theory_mode                     true
% 2.79/0.99  --prolific_symb_bound                   200
% 2.79/0.99  --lt_threshold                          2000
% 2.79/0.99  --clause_weak_htbl                      true
% 2.79/0.99  --gc_record_bc_elim                     false
% 2.79/0.99  
% 2.79/0.99  ------ Preprocessing Options
% 2.79/0.99  
% 2.79/0.99  --preprocessing_flag                    true
% 2.79/0.99  --time_out_prep_mult                    0.1
% 2.79/0.99  --splitting_mode                        input
% 2.79/0.99  --splitting_grd                         true
% 2.79/0.99  --splitting_cvd                         false
% 2.79/0.99  --splitting_cvd_svl                     false
% 2.79/0.99  --splitting_nvd                         32
% 2.79/0.99  --sub_typing                            true
% 2.79/0.99  --prep_gs_sim                           true
% 2.79/0.99  --prep_unflatten                        true
% 2.79/0.99  --prep_res_sim                          true
% 2.79/0.99  --prep_upred                            true
% 2.79/0.99  --prep_sem_filter                       exhaustive
% 2.79/0.99  --prep_sem_filter_out                   false
% 2.79/0.99  --pred_elim                             true
% 2.79/0.99  --res_sim_input                         true
% 2.79/0.99  --eq_ax_congr_red                       true
% 2.79/0.99  --pure_diseq_elim                       true
% 2.79/0.99  --brand_transform                       false
% 2.79/0.99  --non_eq_to_eq                          false
% 2.79/0.99  --prep_def_merge                        true
% 2.79/0.99  --prep_def_merge_prop_impl              false
% 2.79/0.99  --prep_def_merge_mbd                    true
% 2.79/0.99  --prep_def_merge_tr_red                 false
% 2.79/0.99  --prep_def_merge_tr_cl                  false
% 2.79/0.99  --smt_preprocessing                     true
% 2.79/0.99  --smt_ac_axioms                         fast
% 2.79/0.99  --preprocessed_out                      false
% 2.79/0.99  --preprocessed_stats                    false
% 2.79/0.99  
% 2.79/0.99  ------ Abstraction refinement Options
% 2.79/0.99  
% 2.79/0.99  --abstr_ref                             []
% 2.79/0.99  --abstr_ref_prep                        false
% 2.79/0.99  --abstr_ref_until_sat                   false
% 2.79/0.99  --abstr_ref_sig_restrict                funpre
% 2.79/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.79/0.99  --abstr_ref_under                       []
% 2.79/0.99  
% 2.79/0.99  ------ SAT Options
% 2.79/0.99  
% 2.79/0.99  --sat_mode                              false
% 2.79/0.99  --sat_fm_restart_options                ""
% 2.79/0.99  --sat_gr_def                            false
% 2.79/0.99  --sat_epr_types                         true
% 2.79/0.99  --sat_non_cyclic_types                  false
% 2.79/0.99  --sat_finite_models                     false
% 2.79/0.99  --sat_fm_lemmas                         false
% 2.79/0.99  --sat_fm_prep                           false
% 2.79/0.99  --sat_fm_uc_incr                        true
% 2.79/0.99  --sat_out_model                         small
% 2.79/0.99  --sat_out_clauses                       false
% 2.79/0.99  
% 2.79/0.99  ------ QBF Options
% 2.79/0.99  
% 2.79/0.99  --qbf_mode                              false
% 2.79/0.99  --qbf_elim_univ                         false
% 2.79/0.99  --qbf_dom_inst                          none
% 2.79/0.99  --qbf_dom_pre_inst                      false
% 2.79/0.99  --qbf_sk_in                             false
% 2.79/0.99  --qbf_pred_elim                         true
% 2.79/0.99  --qbf_split                             512
% 2.79/0.99  
% 2.79/0.99  ------ BMC1 Options
% 2.79/0.99  
% 2.79/0.99  --bmc1_incremental                      false
% 2.79/0.99  --bmc1_axioms                           reachable_all
% 2.79/0.99  --bmc1_min_bound                        0
% 2.79/0.99  --bmc1_max_bound                        -1
% 2.79/0.99  --bmc1_max_bound_default                -1
% 2.79/0.99  --bmc1_symbol_reachability              true
% 2.79/0.99  --bmc1_property_lemmas                  false
% 2.79/0.99  --bmc1_k_induction                      false
% 2.79/0.99  --bmc1_non_equiv_states                 false
% 2.79/0.99  --bmc1_deadlock                         false
% 2.79/0.99  --bmc1_ucm                              false
% 2.79/0.99  --bmc1_add_unsat_core                   none
% 2.79/0.99  --bmc1_unsat_core_children              false
% 2.79/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.79/0.99  --bmc1_out_stat                         full
% 2.79/0.99  --bmc1_ground_init                      false
% 2.79/0.99  --bmc1_pre_inst_next_state              false
% 2.79/0.99  --bmc1_pre_inst_state                   false
% 2.79/0.99  --bmc1_pre_inst_reach_state             false
% 2.79/0.99  --bmc1_out_unsat_core                   false
% 2.79/0.99  --bmc1_aig_witness_out                  false
% 2.79/0.99  --bmc1_verbose                          false
% 2.79/0.99  --bmc1_dump_clauses_tptp                false
% 2.79/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.79/0.99  --bmc1_dump_file                        -
% 2.79/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.79/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.79/0.99  --bmc1_ucm_extend_mode                  1
% 2.79/0.99  --bmc1_ucm_init_mode                    2
% 2.79/0.99  --bmc1_ucm_cone_mode                    none
% 2.79/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.79/0.99  --bmc1_ucm_relax_model                  4
% 2.79/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.79/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.79/0.99  --bmc1_ucm_layered_model                none
% 2.79/0.99  --bmc1_ucm_max_lemma_size               10
% 2.79/0.99  
% 2.79/0.99  ------ AIG Options
% 2.79/0.99  
% 2.79/0.99  --aig_mode                              false
% 2.79/0.99  
% 2.79/0.99  ------ Instantiation Options
% 2.79/0.99  
% 2.79/0.99  --instantiation_flag                    true
% 2.79/0.99  --inst_sos_flag                         false
% 2.79/0.99  --inst_sos_phase                        true
% 2.79/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.79/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.79/0.99  --inst_lit_sel_side                     num_symb
% 2.79/0.99  --inst_solver_per_active                1400
% 2.79/0.99  --inst_solver_calls_frac                1.
% 2.79/0.99  --inst_passive_queue_type               priority_queues
% 2.79/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.79/0.99  --inst_passive_queues_freq              [25;2]
% 2.79/0.99  --inst_dismatching                      true
% 2.79/0.99  --inst_eager_unprocessed_to_passive     true
% 2.79/0.99  --inst_prop_sim_given                   true
% 2.79/0.99  --inst_prop_sim_new                     false
% 2.79/0.99  --inst_subs_new                         false
% 2.79/0.99  --inst_eq_res_simp                      false
% 2.79/0.99  --inst_subs_given                       false
% 2.79/0.99  --inst_orphan_elimination               true
% 2.79/0.99  --inst_learning_loop_flag               true
% 2.79/0.99  --inst_learning_start                   3000
% 2.79/0.99  --inst_learning_factor                  2
% 2.79/0.99  --inst_start_prop_sim_after_learn       3
% 2.79/0.99  --inst_sel_renew                        solver
% 2.79/0.99  --inst_lit_activity_flag                true
% 2.79/0.99  --inst_restr_to_given                   false
% 2.79/0.99  --inst_activity_threshold               500
% 2.79/0.99  --inst_out_proof                        true
% 2.79/0.99  
% 2.79/0.99  ------ Resolution Options
% 2.79/0.99  
% 2.79/0.99  --resolution_flag                       true
% 2.79/0.99  --res_lit_sel                           adaptive
% 2.79/0.99  --res_lit_sel_side                      none
% 2.79/0.99  --res_ordering                          kbo
% 2.79/0.99  --res_to_prop_solver                    active
% 2.79/0.99  --res_prop_simpl_new                    false
% 2.79/0.99  --res_prop_simpl_given                  true
% 2.79/0.99  --res_passive_queue_type                priority_queues
% 2.79/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.79/0.99  --res_passive_queues_freq               [15;5]
% 2.79/0.99  --res_forward_subs                      full
% 2.79/0.99  --res_backward_subs                     full
% 2.79/0.99  --res_forward_subs_resolution           true
% 2.79/0.99  --res_backward_subs_resolution          true
% 2.79/0.99  --res_orphan_elimination                true
% 2.79/0.99  --res_time_limit                        2.
% 2.79/0.99  --res_out_proof                         true
% 2.79/0.99  
% 2.79/0.99  ------ Superposition Options
% 2.79/0.99  
% 2.79/0.99  --superposition_flag                    true
% 2.79/0.99  --sup_passive_queue_type                priority_queues
% 2.79/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.79/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.79/0.99  --demod_completeness_check              fast
% 2.79/0.99  --demod_use_ground                      true
% 2.79/0.99  --sup_to_prop_solver                    passive
% 2.79/0.99  --sup_prop_simpl_new                    true
% 2.79/0.99  --sup_prop_simpl_given                  true
% 2.79/0.99  --sup_fun_splitting                     false
% 2.79/0.99  --sup_smt_interval                      50000
% 2.79/0.99  
% 2.79/0.99  ------ Superposition Simplification Setup
% 2.79/0.99  
% 2.79/0.99  --sup_indices_passive                   []
% 2.79/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.79/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/0.99  --sup_full_bw                           [BwDemod]
% 2.79/0.99  --sup_immed_triv                        [TrivRules]
% 2.79/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.79/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/0.99  --sup_immed_bw_main                     []
% 2.79/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.79/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/0.99  
% 2.79/0.99  ------ Combination Options
% 2.79/0.99  
% 2.79/0.99  --comb_res_mult                         3
% 2.79/0.99  --comb_sup_mult                         2
% 2.79/0.99  --comb_inst_mult                        10
% 2.79/0.99  
% 2.79/0.99  ------ Debug Options
% 2.79/0.99  
% 2.79/0.99  --dbg_backtrace                         false
% 2.79/0.99  --dbg_dump_prop_clauses                 false
% 2.79/0.99  --dbg_dump_prop_clauses_file            -
% 2.79/0.99  --dbg_out_stat                          false
% 2.79/0.99  ------ Parsing...
% 2.79/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.79/0.99  
% 2.79/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.79/0.99  
% 2.79/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.79/0.99  
% 2.79/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.79/0.99  ------ Proving...
% 2.79/0.99  ------ Problem Properties 
% 2.79/0.99  
% 2.79/0.99  
% 2.79/0.99  clauses                                 21
% 2.79/0.99  conjectures                             3
% 2.79/0.99  EPR                                     2
% 2.79/0.99  Horn                                    20
% 2.79/0.99  unary                                   3
% 2.79/0.99  binary                                  7
% 2.79/0.99  lits                                    52
% 2.79/0.99  lits eq                                 3
% 2.79/0.99  fd_pure                                 0
% 2.79/0.99  fd_pseudo                               0
% 2.79/0.99  fd_cond                                 0
% 2.79/0.99  fd_pseudo_cond                          1
% 2.79/0.99  AC symbols                              0
% 2.79/0.99  
% 2.79/0.99  ------ Schedule dynamic 5 is on 
% 2.79/0.99  
% 2.79/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.79/0.99  
% 2.79/0.99  
% 2.79/0.99  ------ 
% 2.79/0.99  Current options:
% 2.79/0.99  ------ 
% 2.79/0.99  
% 2.79/0.99  ------ Input Options
% 2.79/0.99  
% 2.79/0.99  --out_options                           all
% 2.79/0.99  --tptp_safe_out                         true
% 2.79/0.99  --problem_path                          ""
% 2.79/0.99  --include_path                          ""
% 2.79/0.99  --clausifier                            res/vclausify_rel
% 2.79/0.99  --clausifier_options                    --mode clausify
% 2.79/0.99  --stdin                                 false
% 2.79/0.99  --stats_out                             all
% 2.79/0.99  
% 2.79/0.99  ------ General Options
% 2.79/0.99  
% 2.79/0.99  --fof                                   false
% 2.79/0.99  --time_out_real                         305.
% 2.79/0.99  --time_out_virtual                      -1.
% 2.79/0.99  --symbol_type_check                     false
% 2.79/0.99  --clausify_out                          false
% 2.79/0.99  --sig_cnt_out                           false
% 2.79/0.99  --trig_cnt_out                          false
% 2.79/0.99  --trig_cnt_out_tolerance                1.
% 2.79/0.99  --trig_cnt_out_sk_spl                   false
% 2.79/0.99  --abstr_cl_out                          false
% 2.79/0.99  
% 2.79/0.99  ------ Global Options
% 2.79/0.99  
% 2.79/0.99  --schedule                              default
% 2.79/0.99  --add_important_lit                     false
% 2.79/0.99  --prop_solver_per_cl                    1000
% 2.79/0.99  --min_unsat_core                        false
% 2.79/0.99  --soft_assumptions                      false
% 2.79/0.99  --soft_lemma_size                       3
% 2.79/0.99  --prop_impl_unit_size                   0
% 2.79/0.99  --prop_impl_unit                        []
% 2.79/0.99  --share_sel_clauses                     true
% 2.79/0.99  --reset_solvers                         false
% 2.79/0.99  --bc_imp_inh                            [conj_cone]
% 2.79/0.99  --conj_cone_tolerance                   3.
% 2.79/0.99  --extra_neg_conj                        none
% 2.79/0.99  --large_theory_mode                     true
% 2.79/0.99  --prolific_symb_bound                   200
% 2.79/0.99  --lt_threshold                          2000
% 2.79/0.99  --clause_weak_htbl                      true
% 2.79/0.99  --gc_record_bc_elim                     false
% 2.79/0.99  
% 2.79/0.99  ------ Preprocessing Options
% 2.79/0.99  
% 2.79/0.99  --preprocessing_flag                    true
% 2.79/0.99  --time_out_prep_mult                    0.1
% 2.79/0.99  --splitting_mode                        input
% 2.79/0.99  --splitting_grd                         true
% 2.79/0.99  --splitting_cvd                         false
% 2.79/0.99  --splitting_cvd_svl                     false
% 2.79/0.99  --splitting_nvd                         32
% 2.79/0.99  --sub_typing                            true
% 2.79/0.99  --prep_gs_sim                           true
% 2.79/0.99  --prep_unflatten                        true
% 2.79/0.99  --prep_res_sim                          true
% 2.79/0.99  --prep_upred                            true
% 2.79/0.99  --prep_sem_filter                       exhaustive
% 2.79/0.99  --prep_sem_filter_out                   false
% 2.79/0.99  --pred_elim                             true
% 2.79/0.99  --res_sim_input                         true
% 2.79/0.99  --eq_ax_congr_red                       true
% 2.79/0.99  --pure_diseq_elim                       true
% 2.79/0.99  --brand_transform                       false
% 2.79/0.99  --non_eq_to_eq                          false
% 2.79/0.99  --prep_def_merge                        true
% 2.79/0.99  --prep_def_merge_prop_impl              false
% 2.79/0.99  --prep_def_merge_mbd                    true
% 2.79/0.99  --prep_def_merge_tr_red                 false
% 2.79/0.99  --prep_def_merge_tr_cl                  false
% 2.79/0.99  --smt_preprocessing                     true
% 2.79/0.99  --smt_ac_axioms                         fast
% 2.79/0.99  --preprocessed_out                      false
% 2.79/0.99  --preprocessed_stats                    false
% 2.79/0.99  
% 2.79/0.99  ------ Abstraction refinement Options
% 2.79/0.99  
% 2.79/0.99  --abstr_ref                             []
% 2.79/0.99  --abstr_ref_prep                        false
% 2.79/0.99  --abstr_ref_until_sat                   false
% 2.79/0.99  --abstr_ref_sig_restrict                funpre
% 2.79/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.79/0.99  --abstr_ref_under                       []
% 2.79/0.99  
% 2.79/0.99  ------ SAT Options
% 2.79/0.99  
% 2.79/0.99  --sat_mode                              false
% 2.79/0.99  --sat_fm_restart_options                ""
% 2.79/0.99  --sat_gr_def                            false
% 2.79/0.99  --sat_epr_types                         true
% 2.79/0.99  --sat_non_cyclic_types                  false
% 2.79/0.99  --sat_finite_models                     false
% 2.79/0.99  --sat_fm_lemmas                         false
% 2.79/0.99  --sat_fm_prep                           false
% 2.79/0.99  --sat_fm_uc_incr                        true
% 2.79/0.99  --sat_out_model                         small
% 2.79/0.99  --sat_out_clauses                       false
% 2.79/0.99  
% 2.79/0.99  ------ QBF Options
% 2.79/0.99  
% 2.79/0.99  --qbf_mode                              false
% 2.79/0.99  --qbf_elim_univ                         false
% 2.79/0.99  --qbf_dom_inst                          none
% 2.79/0.99  --qbf_dom_pre_inst                      false
% 2.79/0.99  --qbf_sk_in                             false
% 2.79/0.99  --qbf_pred_elim                         true
% 2.79/0.99  --qbf_split                             512
% 2.79/0.99  
% 2.79/0.99  ------ BMC1 Options
% 2.79/0.99  
% 2.79/0.99  --bmc1_incremental                      false
% 2.79/0.99  --bmc1_axioms                           reachable_all
% 2.79/0.99  --bmc1_min_bound                        0
% 2.79/0.99  --bmc1_max_bound                        -1
% 2.79/0.99  --bmc1_max_bound_default                -1
% 2.79/0.99  --bmc1_symbol_reachability              true
% 2.79/0.99  --bmc1_property_lemmas                  false
% 2.79/0.99  --bmc1_k_induction                      false
% 2.79/0.99  --bmc1_non_equiv_states                 false
% 2.79/0.99  --bmc1_deadlock                         false
% 2.79/0.99  --bmc1_ucm                              false
% 2.79/0.99  --bmc1_add_unsat_core                   none
% 2.79/0.99  --bmc1_unsat_core_children              false
% 2.79/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.79/0.99  --bmc1_out_stat                         full
% 2.79/0.99  --bmc1_ground_init                      false
% 2.79/0.99  --bmc1_pre_inst_next_state              false
% 2.79/0.99  --bmc1_pre_inst_state                   false
% 2.79/0.99  --bmc1_pre_inst_reach_state             false
% 2.79/0.99  --bmc1_out_unsat_core                   false
% 2.79/0.99  --bmc1_aig_witness_out                  false
% 2.79/0.99  --bmc1_verbose                          false
% 2.79/0.99  --bmc1_dump_clauses_tptp                false
% 2.79/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.79/0.99  --bmc1_dump_file                        -
% 2.79/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.79/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.79/0.99  --bmc1_ucm_extend_mode                  1
% 2.79/0.99  --bmc1_ucm_init_mode                    2
% 2.79/0.99  --bmc1_ucm_cone_mode                    none
% 2.79/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.79/0.99  --bmc1_ucm_relax_model                  4
% 2.79/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.79/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.79/0.99  --bmc1_ucm_layered_model                none
% 2.79/0.99  --bmc1_ucm_max_lemma_size               10
% 2.79/0.99  
% 2.79/0.99  ------ AIG Options
% 2.79/0.99  
% 2.79/0.99  --aig_mode                              false
% 2.79/0.99  
% 2.79/0.99  ------ Instantiation Options
% 2.79/0.99  
% 2.79/0.99  --instantiation_flag                    true
% 2.79/0.99  --inst_sos_flag                         false
% 2.79/0.99  --inst_sos_phase                        true
% 2.79/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.79/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.79/0.99  --inst_lit_sel_side                     none
% 2.79/0.99  --inst_solver_per_active                1400
% 2.79/0.99  --inst_solver_calls_frac                1.
% 2.79/0.99  --inst_passive_queue_type               priority_queues
% 2.79/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.79/0.99  --inst_passive_queues_freq              [25;2]
% 2.79/0.99  --inst_dismatching                      true
% 2.79/0.99  --inst_eager_unprocessed_to_passive     true
% 2.79/0.99  --inst_prop_sim_given                   true
% 2.79/0.99  --inst_prop_sim_new                     false
% 2.79/0.99  --inst_subs_new                         false
% 2.79/0.99  --inst_eq_res_simp                      false
% 2.79/0.99  --inst_subs_given                       false
% 2.79/0.99  --inst_orphan_elimination               true
% 2.79/0.99  --inst_learning_loop_flag               true
% 2.79/0.99  --inst_learning_start                   3000
% 2.79/0.99  --inst_learning_factor                  2
% 2.79/0.99  --inst_start_prop_sim_after_learn       3
% 2.79/0.99  --inst_sel_renew                        solver
% 2.79/0.99  --inst_lit_activity_flag                true
% 2.79/0.99  --inst_restr_to_given                   false
% 2.79/0.99  --inst_activity_threshold               500
% 2.79/0.99  --inst_out_proof                        true
% 2.79/0.99  
% 2.79/0.99  ------ Resolution Options
% 2.79/0.99  
% 2.79/0.99  --resolution_flag                       false
% 2.79/0.99  --res_lit_sel                           adaptive
% 2.79/0.99  --res_lit_sel_side                      none
% 2.79/0.99  --res_ordering                          kbo
% 2.79/0.99  --res_to_prop_solver                    active
% 2.79/0.99  --res_prop_simpl_new                    false
% 2.79/0.99  --res_prop_simpl_given                  true
% 2.79/0.99  --res_passive_queue_type                priority_queues
% 2.79/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.79/0.99  --res_passive_queues_freq               [15;5]
% 2.79/0.99  --res_forward_subs                      full
% 2.79/0.99  --res_backward_subs                     full
% 2.79/0.99  --res_forward_subs_resolution           true
% 2.79/0.99  --res_backward_subs_resolution          true
% 2.79/0.99  --res_orphan_elimination                true
% 2.79/0.99  --res_time_limit                        2.
% 2.79/0.99  --res_out_proof                         true
% 2.79/0.99  
% 2.79/0.99  ------ Superposition Options
% 2.79/0.99  
% 2.79/0.99  --superposition_flag                    true
% 2.79/0.99  --sup_passive_queue_type                priority_queues
% 2.79/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.79/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.79/0.99  --demod_completeness_check              fast
% 2.79/0.99  --demod_use_ground                      true
% 2.79/0.99  --sup_to_prop_solver                    passive
% 2.79/0.99  --sup_prop_simpl_new                    true
% 2.79/0.99  --sup_prop_simpl_given                  true
% 2.79/0.99  --sup_fun_splitting                     false
% 2.79/0.99  --sup_smt_interval                      50000
% 2.79/0.99  
% 2.79/0.99  ------ Superposition Simplification Setup
% 2.79/0.99  
% 2.79/0.99  --sup_indices_passive                   []
% 2.79/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.79/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/0.99  --sup_full_bw                           [BwDemod]
% 2.79/0.99  --sup_immed_triv                        [TrivRules]
% 2.79/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.79/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/0.99  --sup_immed_bw_main                     []
% 2.79/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.79/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/0.99  
% 2.79/0.99  ------ Combination Options
% 2.79/0.99  
% 2.79/0.99  --comb_res_mult                         3
% 2.79/0.99  --comb_sup_mult                         2
% 2.79/0.99  --comb_inst_mult                        10
% 2.79/0.99  
% 2.79/0.99  ------ Debug Options
% 2.79/0.99  
% 2.79/0.99  --dbg_backtrace                         false
% 2.79/0.99  --dbg_dump_prop_clauses                 false
% 2.79/0.99  --dbg_dump_prop_clauses_file            -
% 2.79/0.99  --dbg_out_stat                          false
% 2.79/0.99  
% 2.79/0.99  
% 2.79/0.99  
% 2.79/0.99  
% 2.79/0.99  ------ Proving...
% 2.79/0.99  
% 2.79/0.99  
% 2.79/0.99  % SZS status Theorem for theBenchmark.p
% 2.79/0.99  
% 2.79/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.79/0.99  
% 2.79/0.99  fof(f6,axiom,(
% 2.79/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 2.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f14,plain,(
% 2.79/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 2.79/0.99    inference(ennf_transformation,[],[f6])).
% 2.79/0.99  
% 2.79/0.99  fof(f27,plain,(
% 2.79/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.79/0.99    inference(nnf_transformation,[],[f14])).
% 2.79/0.99  
% 2.79/0.99  fof(f28,plain,(
% 2.79/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.79/0.99    inference(rectify,[],[f27])).
% 2.79/0.99  
% 2.79/0.99  fof(f29,plain,(
% 2.79/0.99    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 2.79/0.99    introduced(choice_axiom,[])).
% 2.79/0.99  
% 2.79/0.99  fof(f30,plain,(
% 2.79/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.79/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).
% 2.79/0.99  
% 2.79/0.99  fof(f48,plain,(
% 2.79/0.99    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f30])).
% 2.79/0.99  
% 2.79/0.99  fof(f46,plain,(
% 2.79/0.99    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f30])).
% 2.79/0.99  
% 2.79/0.99  fof(f9,conjecture,(
% 2.79/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f10,negated_conjecture,(
% 2.79/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.79/0.99    inference(negated_conjecture,[],[f9])).
% 2.79/0.99  
% 2.79/0.99  fof(f11,plain,(
% 2.79/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.79/0.99    inference(pure_predicate_removal,[],[f10])).
% 2.79/0.99  
% 2.79/0.99  fof(f18,plain,(
% 2.79/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 2.79/0.99    inference(ennf_transformation,[],[f11])).
% 2.79/0.99  
% 2.79/0.99  fof(f19,plain,(
% 2.79/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 2.79/0.99    inference(flattening,[],[f18])).
% 2.79/0.99  
% 2.79/0.99  fof(f34,plain,(
% 2.79/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK6 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(sK6,k7_relset_1(X0,X1,X3,X2)))) )),
% 2.79/0.99    introduced(choice_axiom,[])).
% 2.79/0.99  
% 2.79/0.99  fof(f33,plain,(
% 2.79/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK5,X5) != X4 | ~r2_hidden(X5,sK4) | ~r2_hidden(X5,sK2)) & r2_hidden(X4,k7_relset_1(sK2,sK3,sK5,sK4))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_1(sK5))),
% 2.79/0.99    introduced(choice_axiom,[])).
% 2.79/0.99  
% 2.79/0.99  fof(f35,plain,(
% 2.79/0.99    (! [X5] : (k1_funct_1(sK5,X5) != sK6 | ~r2_hidden(X5,sK4) | ~r2_hidden(X5,sK2)) & r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_1(sK5)),
% 2.79/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f19,f34,f33])).
% 2.79/0.99  
% 2.79/0.99  fof(f55,plain,(
% 2.79/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.79/0.99    inference(cnf_transformation,[],[f35])).
% 2.79/0.99  
% 2.79/0.99  fof(f3,axiom,(
% 2.79/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f26,plain,(
% 2.79/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.79/0.99    inference(nnf_transformation,[],[f3])).
% 2.79/0.99  
% 2.79/0.99  fof(f42,plain,(
% 2.79/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.79/0.99    inference(cnf_transformation,[],[f26])).
% 2.79/0.99  
% 2.79/0.99  fof(f7,axiom,(
% 2.79/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 2.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f15,plain,(
% 2.79/0.99    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.79/0.99    inference(ennf_transformation,[],[f7])).
% 2.79/0.99  
% 2.79/0.99  fof(f16,plain,(
% 2.79/0.99    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.79/0.99    inference(flattening,[],[f15])).
% 2.79/0.99  
% 2.79/0.99  fof(f31,plain,(
% 2.79/0.99    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.79/0.99    inference(nnf_transformation,[],[f16])).
% 2.79/0.99  
% 2.79/0.99  fof(f32,plain,(
% 2.79/0.99    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.79/0.99    inference(flattening,[],[f31])).
% 2.79/0.99  
% 2.79/0.99  fof(f52,plain,(
% 2.79/0.99    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f32])).
% 2.79/0.99  
% 2.79/0.99  fof(f58,plain,(
% 2.79/0.99    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.79/0.99    inference(equality_resolution,[],[f52])).
% 2.79/0.99  
% 2.79/0.99  fof(f54,plain,(
% 2.79/0.99    v1_funct_1(sK5)),
% 2.79/0.99    inference(cnf_transformation,[],[f35])).
% 2.79/0.99  
% 2.79/0.99  fof(f1,axiom,(
% 2.79/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f12,plain,(
% 2.79/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.79/0.99    inference(ennf_transformation,[],[f1])).
% 2.79/0.99  
% 2.79/0.99  fof(f20,plain,(
% 2.79/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.79/0.99    inference(nnf_transformation,[],[f12])).
% 2.79/0.99  
% 2.79/0.99  fof(f21,plain,(
% 2.79/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.79/0.99    inference(rectify,[],[f20])).
% 2.79/0.99  
% 2.79/0.99  fof(f22,plain,(
% 2.79/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.79/0.99    introduced(choice_axiom,[])).
% 2.79/0.99  
% 2.79/0.99  fof(f23,plain,(
% 2.79/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.79/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 2.79/0.99  
% 2.79/0.99  fof(f36,plain,(
% 2.79/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f23])).
% 2.79/0.99  
% 2.79/0.99  fof(f4,axiom,(
% 2.79/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f13,plain,(
% 2.79/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.79/0.99    inference(ennf_transformation,[],[f4])).
% 2.79/0.99  
% 2.79/0.99  fof(f44,plain,(
% 2.79/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f13])).
% 2.79/0.99  
% 2.79/0.99  fof(f43,plain,(
% 2.79/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f26])).
% 2.79/0.99  
% 2.79/0.99  fof(f5,axiom,(
% 2.79/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f45,plain,(
% 2.79/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.79/0.99    inference(cnf_transformation,[],[f5])).
% 2.79/0.99  
% 2.79/0.99  fof(f2,axiom,(
% 2.79/0.99    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 2.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f24,plain,(
% 2.79/0.99    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.79/0.99    inference(nnf_transformation,[],[f2])).
% 2.79/0.99  
% 2.79/0.99  fof(f25,plain,(
% 2.79/0.99    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.79/0.99    inference(flattening,[],[f24])).
% 2.79/0.99  
% 2.79/0.99  fof(f39,plain,(
% 2.79/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 2.79/0.99    inference(cnf_transformation,[],[f25])).
% 2.79/0.99  
% 2.79/0.99  fof(f8,axiom,(
% 2.79/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f17,plain,(
% 2.79/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.79/0.99    inference(ennf_transformation,[],[f8])).
% 2.79/0.99  
% 2.79/0.99  fof(f53,plain,(
% 2.79/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.79/0.99    inference(cnf_transformation,[],[f17])).
% 2.79/0.99  
% 2.79/0.99  fof(f56,plain,(
% 2.79/0.99    r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4))),
% 2.79/0.99    inference(cnf_transformation,[],[f35])).
% 2.79/0.99  
% 2.79/0.99  fof(f47,plain,(
% 2.79/0.99    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f30])).
% 2.79/0.99  
% 2.79/0.99  fof(f51,plain,(
% 2.79/0.99    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f32])).
% 2.79/0.99  
% 2.79/0.99  fof(f57,plain,(
% 2.79/0.99    ( ! [X5] : (k1_funct_1(sK5,X5) != sK6 | ~r2_hidden(X5,sK4) | ~r2_hidden(X5,sK2)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f35])).
% 2.79/0.99  
% 2.79/0.99  cnf(c_11,plain,
% 2.79/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.79/0.99      | r2_hidden(sK1(X0,X2,X1),X2)
% 2.79/0.99      | ~ v1_relat_1(X1) ),
% 2.79/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1374,plain,
% 2.79/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 2.79/0.99      | r2_hidden(sK1(X0,X2,X1),X2) = iProver_top
% 2.79/0.99      | v1_relat_1(X1) != iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_13,plain,
% 2.79/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.79/0.99      | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1))
% 2.79/0.99      | ~ v1_relat_1(X1) ),
% 2.79/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1372,plain,
% 2.79/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 2.79/0.99      | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 2.79/0.99      | v1_relat_1(X1) != iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_20,negated_conjecture,
% 2.79/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.79/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1368,plain,
% 2.79/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_7,plain,
% 2.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.79/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1377,plain,
% 2.79/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.79/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1694,plain,
% 2.79/0.99      ( r1_tarski(sK5,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_1368,c_1377]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_14,plain,
% 2.79/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.79/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 2.79/0.99      | ~ v1_funct_1(X1)
% 2.79/0.99      | ~ v1_relat_1(X1) ),
% 2.79/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_21,negated_conjecture,
% 2.79/0.99      ( v1_funct_1(sK5) ),
% 2.79/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_357,plain,
% 2.79/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.79/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 2.79/0.99      | ~ v1_relat_1(X1)
% 2.79/0.99      | sK5 != X1 ),
% 2.79/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_358,plain,
% 2.79/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 2.79/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5)
% 2.79/0.99      | ~ v1_relat_1(sK5) ),
% 2.79/0.99      inference(unflattening,[status(thm)],[c_357]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1365,plain,
% 2.79/0.99      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 2.79/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
% 2.79/0.99      | v1_relat_1(sK5) != iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_358]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2,plain,
% 2.79/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.79/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1382,plain,
% 2.79/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.79/0.99      | r2_hidden(X0,X2) = iProver_top
% 2.79/0.99      | r1_tarski(X1,X2) != iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2455,plain,
% 2.79/0.99      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 2.79/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),X1) = iProver_top
% 2.79/0.99      | r1_tarski(sK5,X1) != iProver_top
% 2.79/0.99      | v1_relat_1(sK5) != iProver_top ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_1365,c_1382]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_8,plain,
% 2.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.79/0.99      | ~ v1_relat_1(X1)
% 2.79/0.99      | v1_relat_1(X0) ),
% 2.79/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_6,plain,
% 2.79/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.79/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_173,plain,
% 2.79/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.79/0.99      inference(prop_impl,[status(thm)],[c_6]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_174,plain,
% 2.79/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.79/0.99      inference(renaming,[status(thm)],[c_173]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_219,plain,
% 2.79/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.79/0.99      inference(bin_hyper_res,[status(thm)],[c_8,c_174]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1367,plain,
% 2.79/0.99      ( r1_tarski(X0,X1) != iProver_top
% 2.79/0.99      | v1_relat_1(X1) != iProver_top
% 2.79/0.99      | v1_relat_1(X0) = iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_219]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2269,plain,
% 2.79/0.99      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
% 2.79/0.99      | v1_relat_1(sK5) = iProver_top ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_1694,c_1367]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_9,plain,
% 2.79/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.79/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1376,plain,
% 2.79/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2279,plain,
% 2.79/0.99      ( v1_relat_1(sK5) = iProver_top ),
% 2.79/0.99      inference(forward_subsumption_resolution,
% 2.79/0.99                [status(thm)],
% 2.79/0.99                [c_2269,c_1376]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2831,plain,
% 2.79/0.99      ( r1_tarski(sK5,X1) != iProver_top
% 2.79/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),X1) = iProver_top
% 2.79/0.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 2.79/0.99      inference(global_propositional_subsumption,
% 2.79/0.99                [status(thm)],
% 2.79/0.99                [c_2455,c_2279]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2832,plain,
% 2.79/0.99      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 2.79/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),X1) = iProver_top
% 2.79/0.99      | r1_tarski(sK5,X1) != iProver_top ),
% 2.79/0.99      inference(renaming,[status(thm)],[c_2831]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_5,plain,
% 2.79/0.99      ( r2_hidden(X0,X1)
% 2.79/0.99      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 2.79/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1379,plain,
% 2.79/0.99      ( r2_hidden(X0,X1) = iProver_top
% 2.79/0.99      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2843,plain,
% 2.79/0.99      ( r2_hidden(X0,X1) = iProver_top
% 2.79/0.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 2.79/0.99      | r1_tarski(sK5,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_2832,c_1379]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2953,plain,
% 2.79/0.99      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 2.79/0.99      | r2_hidden(X0,sK2) = iProver_top ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_1694,c_2843]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2963,plain,
% 2.79/0.99      ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
% 2.79/0.99      | r2_hidden(sK1(X0,X1,sK5),sK2) = iProver_top
% 2.79/0.99      | v1_relat_1(sK5) != iProver_top ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_1372,c_2953]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_4034,plain,
% 2.79/0.99      ( r2_hidden(sK1(X0,X1,sK5),sK2) = iProver_top
% 2.79/0.99      | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top ),
% 2.79/0.99      inference(global_propositional_subsumption,
% 2.79/0.99                [status(thm)],
% 2.79/0.99                [c_2963,c_2279]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_4035,plain,
% 2.79/0.99      ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
% 2.79/0.99      | r2_hidden(sK1(X0,X1,sK5),sK2) = iProver_top ),
% 2.79/0.99      inference(renaming,[status(thm)],[c_4034]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_17,plain,
% 2.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.79/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.79/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1371,plain,
% 2.79/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.79/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1778,plain,
% 2.79/0.99      ( k7_relset_1(sK2,sK3,sK5,X0) = k9_relat_1(sK5,X0) ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_1368,c_1371]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_19,negated_conjecture,
% 2.79/0.99      ( r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) ),
% 2.79/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1369,plain,
% 2.79/0.99      ( r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) = iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1974,plain,
% 2.79/0.99      ( r2_hidden(sK6,k9_relat_1(sK5,sK4)) = iProver_top ),
% 2.79/0.99      inference(demodulation,[status(thm)],[c_1778,c_1369]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_12,plain,
% 2.79/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.79/0.99      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 2.79/0.99      | ~ v1_relat_1(X1) ),
% 2.79/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1373,plain,
% 2.79/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 2.79/0.99      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
% 2.79/0.99      | v1_relat_1(X1) != iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_15,plain,
% 2.79/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 2.79/0.99      | ~ v1_funct_1(X2)
% 2.79/0.99      | ~ v1_relat_1(X2)
% 2.79/0.99      | k1_funct_1(X2,X0) = X1 ),
% 2.79/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_372,plain,
% 2.79/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 2.79/0.99      | ~ v1_relat_1(X2)
% 2.79/0.99      | k1_funct_1(X2,X0) = X1
% 2.79/0.99      | sK5 != X2 ),
% 2.79/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_21]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_373,plain,
% 2.79/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),sK5)
% 2.79/0.99      | ~ v1_relat_1(sK5)
% 2.79/0.99      | k1_funct_1(sK5,X0) = X1 ),
% 2.79/0.99      inference(unflattening,[status(thm)],[c_372]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1364,plain,
% 2.79/0.99      ( k1_funct_1(sK5,X0) = X1
% 2.79/0.99      | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
% 2.79/0.99      | v1_relat_1(sK5) != iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_373]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2550,plain,
% 2.79/0.99      ( k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0
% 2.79/0.99      | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
% 2.79/0.99      | v1_relat_1(sK5) != iProver_top ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_1373,c_1364]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2691,plain,
% 2.79/0.99      ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
% 2.79/0.99      | k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0 ),
% 2.79/0.99      inference(global_propositional_subsumption,
% 2.79/0.99                [status(thm)],
% 2.79/0.99                [c_2550,c_2279]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2692,plain,
% 2.79/0.99      ( k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0
% 2.79/0.99      | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top ),
% 2.79/0.99      inference(renaming,[status(thm)],[c_2691]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2702,plain,
% 2.79/0.99      ( k1_funct_1(sK5,sK1(sK6,sK4,sK5)) = sK6 ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_1974,c_2692]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_18,negated_conjecture,
% 2.79/0.99      ( ~ r2_hidden(X0,sK2)
% 2.79/0.99      | ~ r2_hidden(X0,sK4)
% 2.79/0.99      | k1_funct_1(sK5,X0) != sK6 ),
% 2.79/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1370,plain,
% 2.79/0.99      ( k1_funct_1(sK5,X0) != sK6
% 2.79/0.99      | r2_hidden(X0,sK2) != iProver_top
% 2.79/0.99      | r2_hidden(X0,sK4) != iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2764,plain,
% 2.79/0.99      ( r2_hidden(sK1(sK6,sK4,sK5),sK2) != iProver_top
% 2.79/0.99      | r2_hidden(sK1(sK6,sK4,sK5),sK4) != iProver_top ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_2702,c_1370]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_4043,plain,
% 2.79/0.99      ( r2_hidden(sK1(sK6,sK4,sK5),sK4) != iProver_top
% 2.79/0.99      | r2_hidden(sK6,k9_relat_1(sK5,sK4)) != iProver_top ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_4035,c_2764]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_4059,plain,
% 2.79/0.99      ( r2_hidden(sK1(sK6,sK4,sK5),sK4) != iProver_top ),
% 2.79/0.99      inference(global_propositional_subsumption,
% 2.79/0.99                [status(thm)],
% 2.79/0.99                [c_4043,c_1974]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_4064,plain,
% 2.79/0.99      ( r2_hidden(sK6,k9_relat_1(sK5,sK4)) != iProver_top
% 2.79/0.99      | v1_relat_1(sK5) != iProver_top ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_1374,c_4059]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(contradiction,plain,
% 2.79/0.99      ( $false ),
% 2.79/0.99      inference(minisat,[status(thm)],[c_4064,c_2279,c_1974]) ).
% 2.79/0.99  
% 2.79/0.99  
% 2.79/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.79/0.99  
% 2.79/0.99  ------                               Statistics
% 2.79/0.99  
% 2.79/0.99  ------ General
% 2.79/0.99  
% 2.79/0.99  abstr_ref_over_cycles:                  0
% 2.79/0.99  abstr_ref_under_cycles:                 0
% 2.79/0.99  gc_basic_clause_elim:                   0
% 2.79/0.99  forced_gc_time:                         0
% 2.79/0.99  parsing_time:                           0.01
% 2.79/0.99  unif_index_cands_time:                  0.
% 2.79/0.99  unif_index_add_time:                    0.
% 2.79/0.99  orderings_time:                         0.
% 2.79/0.99  out_proof_time:                         0.009
% 2.79/0.99  total_time:                             0.15
% 2.79/0.99  num_of_symbols:                         50
% 2.79/0.99  num_of_terms:                           5103
% 2.79/0.99  
% 2.79/0.99  ------ Preprocessing
% 2.79/0.99  
% 2.79/0.99  num_of_splits:                          0
% 2.79/0.99  num_of_split_atoms:                     0
% 2.79/0.99  num_of_reused_defs:                     0
% 2.79/0.99  num_eq_ax_congr_red:                    31
% 2.79/0.99  num_of_sem_filtered_clauses:            1
% 2.79/0.99  num_of_subtypes:                        0
% 2.79/0.99  monotx_restored_types:                  0
% 2.79/0.99  sat_num_of_epr_types:                   0
% 2.79/0.99  sat_num_of_non_cyclic_types:            0
% 2.79/0.99  sat_guarded_non_collapsed_types:        0
% 2.79/0.99  num_pure_diseq_elim:                    0
% 2.79/0.99  simp_replaced_by:                       0
% 2.79/0.99  res_preprocessed:                       108
% 2.79/0.99  prep_upred:                             0
% 2.79/0.99  prep_unflattend:                        21
% 2.79/0.99  smt_new_axioms:                         0
% 2.79/0.99  pred_elim_cands:                        4
% 2.79/0.99  pred_elim:                              1
% 2.79/0.99  pred_elim_cl:                           1
% 2.79/0.99  pred_elim_cycles:                       5
% 2.79/0.99  merged_defs:                            8
% 2.79/0.99  merged_defs_ncl:                        0
% 2.79/0.99  bin_hyper_res:                          9
% 2.79/0.99  prep_cycles:                            4
% 2.79/0.99  pred_elim_time:                         0.006
% 2.79/0.99  splitting_time:                         0.
% 2.79/0.99  sem_filter_time:                        0.
% 2.79/0.99  monotx_time:                            0.
% 2.79/0.99  subtype_inf_time:                       0.
% 2.79/0.99  
% 2.79/0.99  ------ Problem properties
% 2.79/0.99  
% 2.79/0.99  clauses:                                21
% 2.79/0.99  conjectures:                            3
% 2.79/0.99  epr:                                    2
% 2.79/0.99  horn:                                   20
% 2.79/0.99  ground:                                 2
% 2.79/0.99  unary:                                  3
% 2.79/0.99  binary:                                 7
% 2.79/0.99  lits:                                   52
% 2.79/0.99  lits_eq:                                3
% 2.79/0.99  fd_pure:                                0
% 2.79/0.99  fd_pseudo:                              0
% 2.79/0.99  fd_cond:                                0
% 2.79/0.99  fd_pseudo_cond:                         1
% 2.79/0.99  ac_symbols:                             0
% 2.79/0.99  
% 2.79/0.99  ------ Propositional Solver
% 2.79/0.99  
% 2.79/0.99  prop_solver_calls:                      26
% 2.79/0.99  prop_fast_solver_calls:                 733
% 2.79/0.99  smt_solver_calls:                       0
% 2.79/0.99  smt_fast_solver_calls:                  0
% 2.79/0.99  prop_num_of_clauses:                    1523
% 2.79/0.99  prop_preprocess_simplified:             4914
% 2.79/0.99  prop_fo_subsumed:                       6
% 2.79/0.99  prop_solver_time:                       0.
% 2.79/0.99  smt_solver_time:                        0.
% 2.79/0.99  smt_fast_solver_time:                   0.
% 2.79/0.99  prop_fast_solver_time:                  0.
% 2.79/0.99  prop_unsat_core_time:                   0.
% 2.79/0.99  
% 2.79/0.99  ------ QBF
% 2.79/0.99  
% 2.79/0.99  qbf_q_res:                              0
% 2.79/0.99  qbf_num_tautologies:                    0
% 2.79/0.99  qbf_prep_cycles:                        0
% 2.79/0.99  
% 2.79/0.99  ------ BMC1
% 2.79/0.99  
% 2.79/0.99  bmc1_current_bound:                     -1
% 2.79/0.99  bmc1_last_solved_bound:                 -1
% 2.79/0.99  bmc1_unsat_core_size:                   -1
% 2.79/0.99  bmc1_unsat_core_parents_size:           -1
% 2.79/0.99  bmc1_merge_next_fun:                    0
% 2.79/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.79/0.99  
% 2.79/0.99  ------ Instantiation
% 2.79/0.99  
% 2.79/0.99  inst_num_of_clauses:                    380
% 2.79/0.99  inst_num_in_passive:                    129
% 2.79/0.99  inst_num_in_active:                     170
% 2.79/0.99  inst_num_in_unprocessed:                81
% 2.79/0.99  inst_num_of_loops:                      210
% 2.79/0.99  inst_num_of_learning_restarts:          0
% 2.79/0.99  inst_num_moves_active_passive:          37
% 2.79/0.99  inst_lit_activity:                      0
% 2.79/0.99  inst_lit_activity_moves:                0
% 2.79/0.99  inst_num_tautologies:                   0
% 2.79/0.99  inst_num_prop_implied:                  0
% 2.79/0.99  inst_num_existing_simplified:           0
% 2.79/0.99  inst_num_eq_res_simplified:             0
% 2.79/0.99  inst_num_child_elim:                    0
% 2.79/0.99  inst_num_of_dismatching_blockings:      125
% 2.79/0.99  inst_num_of_non_proper_insts:           226
% 2.79/0.99  inst_num_of_duplicates:                 0
% 2.79/0.99  inst_inst_num_from_inst_to_res:         0
% 2.79/0.99  inst_dismatching_checking_time:         0.
% 2.79/0.99  
% 2.79/0.99  ------ Resolution
% 2.79/0.99  
% 2.79/0.99  res_num_of_clauses:                     0
% 2.79/0.99  res_num_in_passive:                     0
% 2.79/0.99  res_num_in_active:                      0
% 2.79/0.99  res_num_of_loops:                       112
% 2.79/0.99  res_forward_subset_subsumed:            19
% 2.79/0.99  res_backward_subset_subsumed:           0
% 2.79/0.99  res_forward_subsumed:                   0
% 2.79/0.99  res_backward_subsumed:                  0
% 2.79/0.99  res_forward_subsumption_resolution:     0
% 2.79/0.99  res_backward_subsumption_resolution:    0
% 2.79/0.99  res_clause_to_clause_subsumption:       201
% 2.79/0.99  res_orphan_elimination:                 0
% 2.79/1.00  res_tautology_del:                      28
% 2.79/1.00  res_num_eq_res_simplified:              0
% 2.79/1.00  res_num_sel_changes:                    0
% 2.79/1.00  res_moves_from_active_to_pass:          0
% 2.79/1.00  
% 2.79/1.00  ------ Superposition
% 2.79/1.00  
% 2.79/1.00  sup_time_total:                         0.
% 2.79/1.00  sup_time_generating:                    0.
% 2.79/1.00  sup_time_sim_full:                      0.
% 2.79/1.00  sup_time_sim_immed:                     0.
% 2.79/1.00  
% 2.79/1.00  sup_num_of_clauses:                     73
% 2.79/1.00  sup_num_in_active:                      41
% 2.79/1.00  sup_num_in_passive:                     32
% 2.79/1.00  sup_num_of_loops:                       41
% 2.79/1.00  sup_fw_superposition:                   30
% 2.79/1.00  sup_bw_superposition:                   39
% 2.79/1.00  sup_immediate_simplified:               3
% 2.79/1.00  sup_given_eliminated:                   0
% 2.79/1.00  comparisons_done:                       0
% 2.79/1.00  comparisons_avoided:                    0
% 2.79/1.00  
% 2.79/1.00  ------ Simplifications
% 2.79/1.00  
% 2.79/1.00  
% 2.79/1.00  sim_fw_subset_subsumed:                 2
% 2.79/1.00  sim_bw_subset_subsumed:                 1
% 2.79/1.00  sim_fw_subsumed:                        1
% 2.79/1.00  sim_bw_subsumed:                        0
% 2.79/1.00  sim_fw_subsumption_res:                 1
% 2.79/1.00  sim_bw_subsumption_res:                 0
% 2.79/1.00  sim_tautology_del:                      8
% 2.79/1.00  sim_eq_tautology_del:                   2
% 2.79/1.00  sim_eq_res_simp:                        0
% 2.79/1.00  sim_fw_demodulated:                     0
% 2.79/1.00  sim_bw_demodulated:                     1
% 2.79/1.00  sim_light_normalised:                   0
% 2.79/1.00  sim_joinable_taut:                      0
% 2.79/1.00  sim_joinable_simp:                      0
% 2.79/1.00  sim_ac_normalised:                      0
% 2.79/1.00  sim_smt_subsumption:                    0
% 2.79/1.00  
%------------------------------------------------------------------------------
