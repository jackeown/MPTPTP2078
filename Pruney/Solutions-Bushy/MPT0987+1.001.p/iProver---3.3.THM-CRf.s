%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0987+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:35 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 576 expanded)
%              Number of clauses        :   84 ( 156 expanded)
%              Number of leaves         :   12 ( 113 expanded)
%              Depth                    :   23
%              Number of atoms          :  425 (3343 expanded)
%              Number of equality atoms :  128 ( 215 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X3,X0,X1)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                    & v1_funct_2(X4,X1,X2)
                    & v1_funct_1(X4) )
                 => ( ( v2_funct_2(X4,X2)
                      & v2_funct_2(X3,X1) )
                   => v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X3,X0,X1)
                  & v1_funct_1(X3) )
               => ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                      & v1_funct_2(X4,X1,X2)
                      & v1_funct_1(X4) )
                   => ( ( v2_funct_2(X4,X2)
                        & v2_funct_2(X3,X1) )
                     => v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f13,plain,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X3) )
               => ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                      & v1_funct_1(X4) )
                   => ( ( v2_funct_2(X4,X2)
                        & v2_funct_2(X3,X1) )
                     => v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f14,plain,(
    ~ ! [X1,X0,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(X4) )
           => ( ( v2_funct_2(X4,X2)
                & v2_funct_2(X3,X1) )
             => v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f29,plain,(
    ? [X1,X0,X2,X3] :
      ( ? [X4] :
          ( ~ v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2)
          & v2_funct_2(X4,X2)
          & v2_funct_2(X3,X1)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ? [X1,X0,X2,X3] :
      ( ? [X4] :
          ( ~ v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2)
          & v2_funct_2(X4,X2)
          & v2_funct_2(X3,X1)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f29])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ v2_funct_2(k1_partfun1(X1,X0,X0,X2,X3,X4),X2)
          & v2_funct_2(X4,X2)
          & v2_funct_2(X3,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      & v1_funct_1(X3) ) ),
    inference(rectify,[],[f30])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ v2_funct_2(k1_partfun1(X1,X0,X0,X2,X3,X4),X2)
          & v2_funct_2(X4,X2)
          & v2_funct_2(X3,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          & v1_funct_1(X4) )
     => ( ~ v2_funct_2(k1_partfun1(X1,X0,X0,X2,X3,sK4),X2)
        & v2_funct_2(sK4,X2)
        & v2_funct_2(X3,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ~ v2_funct_2(k1_partfun1(X1,X0,X0,X2,X3,X4),X2)
            & v2_funct_2(X4,X2)
            & v2_funct_2(X3,X0)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ~ v2_funct_2(k1_partfun1(sK1,sK0,sK0,sK2,sK3,X4),sK2)
          & v2_funct_2(X4,sK2)
          & v2_funct_2(sK3,sK0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ v2_funct_2(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4),sK2)
    & v2_funct_2(sK4,sK2)
    & v2_funct_2(sK3,sK0)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f32,f34,f33])).

fof(f50,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f35])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f23])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f49,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f20])).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f51,plain,(
    v2_funct_2(sK3,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f8])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    v2_funct_2(sK4,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f39])).

fof(f53,plain,(
    ~ v2_funct_2(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_430,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_701,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_430])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_428,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_703,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_428])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_432,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47)))
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(X1_46)
    | k1_partfun1(X2_47,X3_47,X0_47,X1_47,X1_46,X0_46) = k5_relat_1(X1_46,X0_46) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_699,plain,
    ( k1_partfun1(X0_47,X1_47,X2_47,X3_47,X0_46,X1_46) = k5_relat_1(X0_46,X1_46)
    | m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47))) != iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | v1_funct_1(X1_46) != iProver_top
    | v1_funct_1(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_432])).

cnf(c_1337,plain,
    ( k1_partfun1(sK1,sK0,X0_47,X1_47,sK3,X0_46) = k5_relat_1(sK3,X0_46)
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_703,c_699])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_18,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2016,plain,
    ( v1_funct_1(X0_46) != iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | k1_partfun1(sK1,sK0,X0_47,X1_47,sK3,X0_46) = k5_relat_1(sK3,X0_46) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1337,c_18])).

cnf(c_2017,plain,
    ( k1_partfun1(sK1,sK0,X0_47,X1_47,sK3,X0_46) = k5_relat_1(sK3,X0_46)
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | v1_funct_1(X0_46) != iProver_top ),
    inference(renaming,[status(thm)],[c_2016])).

cnf(c_2023,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_701,c_2017])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_854,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(X0_47,X1_47,sK0,sK2,X0_46,sK4) = k5_relat_1(X0_46,sK4) ),
    inference(instantiation,[status(thm)],[c_432])).

cnf(c_943,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_854])).

cnf(c_2624,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2023,c_17,c_16,c_15,c_14,c_943])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_435,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47)))
    | m1_subset_1(k1_partfun1(X2_47,X3_47,X0_47,X1_47,X1_46,X0_46),k1_zfmisc_1(k2_zfmisc_1(X2_47,X1_47)))
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(X1_46) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_696,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47))) != iProver_top
    | m1_subset_1(k1_partfun1(X2_47,X3_47,X0_47,X1_47,X1_46,X0_46),k1_zfmisc_1(k2_zfmisc_1(X2_47,X1_47))) = iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(X1_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_435])).

cnf(c_2635,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2624,c_696])).

cnf(c_19,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_20,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_21,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4191,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2635,c_18,c_19,c_20,c_21])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_431,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | k1_relset_1(X0_47,X1_47,X0_46) = k1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_700,plain,
    ( k1_relset_1(X0_47,X1_47,X0_46) = k1_relat_1(X0_46)
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_431])).

cnf(c_993,plain,
    ( k1_relset_1(sK0,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_701,c_700])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_433,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | m1_subset_1(k1_relset_1(X0_47,X1_47,X0_46),k1_zfmisc_1(X0_47)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_698,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | m1_subset_1(k1_relset_1(X0_47,X1_47,X0_46),k1_zfmisc_1(X0_47)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_433])).

cnf(c_1491,plain,
    ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK0)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_993,c_698])).

cnf(c_2477,plain,
    ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1491,c_21])).

cnf(c_1,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_3,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_224,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_1,c_3])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_236,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_224,c_0])).

cnf(c_13,negated_conjecture,
    ( v2_funct_2(sK3,sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_291,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relat_1(X0) = X2
    | sK3 != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_236,c_13])).

cnf(c_292,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | k2_relat_1(sK3) = sK0 ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_423,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_47,sK0)))
    | k2_relat_1(sK3) = sK0 ),
    inference(subtyping,[status(esa)],[c_292])).

cnf(c_707,plain,
    ( k2_relat_1(sK3) = sK0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_47,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_423])).

cnf(c_810,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k2_relat_1(sK3) = sK0 ),
    inference(instantiation,[status(thm)],[c_423])).

cnf(c_931,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_707,c_16,c_810])).

cnf(c_9,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_10,plain,
    ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_201,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | k1_relat_1(X2) != X0
    | k2_relat_1(X3) != X1
    | k2_relat_1(k5_relat_1(X3,X2)) = k2_relat_1(X2) ),
    inference(resolution_lifted,[status(thm)],[c_9,c_10])).

cnf(c_202,plain,
    ( ~ m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(k2_relat_1(X1)))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_201])).

cnf(c_426,plain,
    ( ~ m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k2_relat_1(X1_46)))
    | ~ v1_relat_1(X0_46)
    | ~ v1_relat_1(X1_46)
    | k2_relat_1(k5_relat_1(X1_46,X0_46)) = k2_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_202])).

cnf(c_705,plain,
    ( k2_relat_1(k5_relat_1(X0_46,X1_46)) = k2_relat_1(X1_46)
    | m1_subset_1(k1_relat_1(X1_46),k1_zfmisc_1(k2_relat_1(X0_46))) != iProver_top
    | v1_relat_1(X1_46) != iProver_top
    | v1_relat_1(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_426])).

cnf(c_3763,plain,
    ( k2_relat_1(k5_relat_1(sK3,X0_46)) = k2_relat_1(X0_46)
    | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(sK0)) != iProver_top
    | v1_relat_1(X0_46) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_931,c_705])).

cnf(c_436,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | v1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_816,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_436])).

cnf(c_817,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_816])).

cnf(c_3962,plain,
    ( v1_relat_1(X0_46) != iProver_top
    | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(sK0)) != iProver_top
    | k2_relat_1(k5_relat_1(sK3,X0_46)) = k2_relat_1(X0_46) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3763,c_19,c_817])).

cnf(c_3963,plain,
    ( k2_relat_1(k5_relat_1(sK3,X0_46)) = k2_relat_1(X0_46)
    | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(sK0)) != iProver_top
    | v1_relat_1(X0_46) != iProver_top ),
    inference(renaming,[status(thm)],[c_3962])).

cnf(c_3969,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = k2_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2477,c_3963])).

cnf(c_12,negated_conjecture,
    ( v2_funct_2(sK4,sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_281,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relat_1(X0) = X2
    | sK4 != X0
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_236,c_12])).

cnf(c_282,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | k2_relat_1(sK4) = sK2 ),
    inference(unflattening,[status(thm)],[c_281])).

cnf(c_284,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k2_relat_1(sK4) = sK2 ),
    inference(instantiation,[status(thm)],[c_282])).

cnf(c_286,plain,
    ( k2_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_282,c_14,c_284])).

cnf(c_424,plain,
    ( k2_relat_1(sK4) = sK2 ),
    inference(subtyping,[status(esa)],[c_286])).

cnf(c_3977,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3969,c_424])).

cnf(c_813,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_436])).

cnf(c_814,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_813])).

cnf(c_3995,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3977,c_21,c_814])).

cnf(c_2,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_243,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X0)
    | X0 != X1
    | k2_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_244,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_243])).

cnf(c_254,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_244,c_0])).

cnf(c_11,negated_conjecture,
    ( ~ v2_funct_2(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_269,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4) != X0
    | k2_relat_1(X0) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_254,c_11])).

cnf(c_270,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4)))))
    | k2_relat_1(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4)) != sK2 ),
    inference(unflattening,[status(thm)],[c_269])).

cnf(c_425,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X0_47,k2_relat_1(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4)))))
    | k2_relat_1(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4)) != sK2 ),
    inference(subtyping,[status(esa)],[c_270])).

cnf(c_706,plain,
    ( k2_relat_1(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4)) != sK2
    | m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X0_47,k2_relat_1(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_425])).

cnf(c_2816,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) != sK2
    | m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X0_47,k2_relat_1(k5_relat_1(sK3,sK4))))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_706,c_2624])).

cnf(c_3998,plain,
    ( sK2 != sK2
    | m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X0_47,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3995,c_2816])).

cnf(c_4006,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X0_47,sK2))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3998])).

cnf(c_4196,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4191,c_4006])).


%------------------------------------------------------------------------------
