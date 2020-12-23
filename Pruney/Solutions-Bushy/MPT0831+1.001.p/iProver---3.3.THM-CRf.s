%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0831+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:12 EST 2020

% Result     : Theorem 11.57s
% Output     : CNFRefutation 11.57s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 156 expanded)
%              Number of clauses        :   57 (  63 expanded)
%              Number of leaves         :   14 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  388 ( 609 expanded)
%              Number of equality atoms :   75 (  88 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f32])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
            & r2_hidden(sK0(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK0(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
                    & r2_hidden(sK0(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( r1_tarski(X1,X2)
         => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f24])).

fof(f34,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ~ r2_relset_1(sK3,sK2,k5_relset_1(sK3,sK2,sK5,sK4),sK5)
      & r1_tarski(sK3,sK4)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ r2_relset_1(sK3,sK2,k5_relset_1(sK3,sK2,sK5,sK4),sK5)
    & r1_tarski(sK3,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f25,f34])).

fof(f53,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f16])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f45])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,(
    ~ r2_relset_1(sK3,sK2,k5_relset_1(sK3,sK2,sK5,sK4),sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_34944,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK4))
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_35742,plain,
    ( ~ r2_hidden(sK0(sK5,sK4,sK5),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK4))
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_34944])).

cnf(c_34934,plain,
    ( ~ r2_hidden(X0,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_xboole_0(k2_zfmisc_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_35669,plain,
    ( ~ r2_hidden(k4_tarski(sK0(sK5,sK4,sK5),sK1(sK5,sK4,sK5)),sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_xboole_0(k2_zfmisc_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_34934])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_35519,plain,
    ( r2_hidden(sK0(sK5,sK4,sK5),sK3)
    | ~ r2_hidden(k4_tarski(sK0(sK5,sK4,sK5),X0),k2_zfmisc_1(sK3,X1)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_35536,plain,
    ( r2_hidden(sK0(sK5,sK4,sK5),sK3)
    | ~ r2_hidden(k4_tarski(sK0(sK5,sK4,sK5),X0),k2_zfmisc_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_35519])).

cnf(c_35652,plain,
    ( r2_hidden(sK0(sK5,sK4,sK5),sK3)
    | ~ r2_hidden(k4_tarski(sK0(sK5,sK4,sK5),sK1(sK5,sK4,sK5)),k2_zfmisc_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_35536])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_34972,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK3,sK2))
    | ~ m1_subset_1(X0,k2_zfmisc_1(sK3,sK2))
    | v1_xboole_0(k2_zfmisc_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_35544,plain,
    ( r2_hidden(k4_tarski(sK0(sK5,sK4,sK5),X0),k2_zfmisc_1(sK3,sK2))
    | ~ m1_subset_1(k4_tarski(sK0(sK5,sK4,sK5),X0),k2_zfmisc_1(sK3,sK2))
    | v1_xboole_0(k2_zfmisc_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_34972])).

cnf(c_35641,plain,
    ( r2_hidden(k4_tarski(sK0(sK5,sK4,sK5),sK1(sK5,sK4,sK5)),k2_zfmisc_1(sK3,sK2))
    | ~ m1_subset_1(k4_tarski(sK0(sK5,sK4,sK5),sK1(sK5,sK4,sK5)),k2_zfmisc_1(sK3,sK2))
    | v1_xboole_0(k2_zfmisc_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_35544])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_34905,plain,
    ( ~ r2_hidden(X0,sK5)
    | m1_subset_1(X0,k2_zfmisc_1(sK3,sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_35556,plain,
    ( ~ r2_hidden(k4_tarski(sK0(sK5,sK4,sK5),X0),sK5)
    | m1_subset_1(k4_tarski(sK0(sK5,sK4,sK5),X0),k2_zfmisc_1(sK3,sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(instantiation,[status(thm)],[c_34905])).

cnf(c_35631,plain,
    ( ~ r2_hidden(k4_tarski(sK0(sK5,sK4,sK5),sK1(sK5,sK4,sK5)),sK5)
    | m1_subset_1(k4_tarski(sK0(sK5,sK4,sK5),sK1(sK5,sK4,sK5)),k2_zfmisc_1(sK3,sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(instantiation,[status(thm)],[c_35556])).

cnf(c_34945,plain,
    ( ~ r2_hidden(X0,sK3)
    | m1_subset_1(X0,sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_35509,plain,
    ( ~ r2_hidden(sK0(sK5,sK4,sK5),sK3)
    | m1_subset_1(sK0(sK5,sK4,sK5),sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_34945])).

cnf(c_35011,plain,
    ( r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_35287,plain,
    ( r2_hidden(sK0(sK5,sK4,sK5),sK4)
    | ~ m1_subset_1(sK0(sK5,sK4,sK5),sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_35011])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
    | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_34955,plain,
    ( ~ r2_hidden(sK0(sK5,X0,X1),X0)
    | ~ r2_hidden(k4_tarski(sK0(sK5,X0,X1),sK1(sK5,X0,X1)),X1)
    | ~ r2_hidden(k4_tarski(sK0(sK5,X0,X1),sK1(sK5,X0,X1)),sK5)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(sK5)
    | k7_relat_1(sK5,X0) = X1 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_35069,plain,
    ( ~ r2_hidden(sK0(sK5,X0,sK5),X0)
    | ~ r2_hidden(k4_tarski(sK0(sK5,X0,sK5),sK1(sK5,X0,sK5)),sK5)
    | ~ v1_relat_1(sK5)
    | k7_relat_1(sK5,X0) = sK5 ),
    inference(instantiation,[status(thm)],[c_34955])).

cnf(c_35187,plain,
    ( ~ r2_hidden(sK0(sK5,sK4,sK5),sK4)
    | ~ r2_hidden(k4_tarski(sK0(sK5,sK4,sK5),sK1(sK5,sK4,sK5)),sK5)
    | ~ v1_relat_1(sK5)
    | k7_relat_1(sK5,sK4) = sK5 ),
    inference(instantiation,[status(thm)],[c_35069])).

cnf(c_2,plain,
    ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_34954,plain,
    ( r2_hidden(k4_tarski(sK0(sK5,X0,X1),sK1(sK5,X0,X1)),X1)
    | r2_hidden(k4_tarski(sK0(sK5,X0,X1),sK1(sK5,X0,X1)),sK5)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(sK5)
    | k7_relat_1(sK5,X0) = X1 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_35031,plain,
    ( r2_hidden(k4_tarski(sK0(sK5,X0,sK5),sK1(sK5,X0,sK5)),sK5)
    | ~ v1_relat_1(sK5)
    | k7_relat_1(sK5,X0) = sK5 ),
    inference(instantiation,[status(thm)],[c_34954])).

cnf(c_35188,plain,
    ( r2_hidden(k4_tarski(sK0(sK5,sK4,sK5),sK1(sK5,sK4,sK5)),sK5)
    | ~ v1_relat_1(sK5)
    | k7_relat_1(sK5,sK4) = sK5 ),
    inference(instantiation,[status(thm)],[c_35031])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_6976,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | k5_relset_1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_7621,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | k5_relset_1(sK3,sK2,sK5,sK4) = k7_relat_1(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_6976])).

cnf(c_192,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_7103,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_192])).

cnf(c_7105,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_7103])).

cnf(c_7106,plain,
    ( X0 != sK5
    | sK5 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_7105])).

cnf(c_7164,plain,
    ( k7_relat_1(sK5,X0) != sK5
    | sK5 = k7_relat_1(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_7106])).

cnf(c_7259,plain,
    ( k7_relat_1(sK5,sK4) != sK5
    | sK5 = k7_relat_1(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_7164])).

cnf(c_7088,plain,
    ( k5_relset_1(sK3,sK2,sK5,sK4) != X0
    | k5_relset_1(sK3,sK2,sK5,sK4) = sK5
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_192])).

cnf(c_7166,plain,
    ( k5_relset_1(sK3,sK2,sK5,sK4) != k7_relat_1(sK5,X0)
    | k5_relset_1(sK3,sK2,sK5,sK4) = sK5
    | sK5 != k7_relat_1(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_7088])).

cnf(c_7253,plain,
    ( k5_relset_1(sK3,sK2,sK5,sK4) != k7_relat_1(sK5,sK4)
    | k5_relset_1(sK3,sK2,sK5,sK4) = sK5
    | sK5 != k7_relat_1(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_7166])).

cnf(c_200,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | r2_relset_1(X4,X5,X6,X7)
    | X4 != X0
    | X5 != X1
    | X6 != X2
    | X7 != X3 ),
    theory(equality)).

cnf(c_7006,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ r2_relset_1(sK3,sK2,sK5,sK5)
    | X2 != sK5
    | X3 != sK5
    | X1 != sK2
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_200])).

cnf(c_7027,plain,
    ( r2_relset_1(X0,sK2,X1,X2)
    | ~ r2_relset_1(sK3,sK2,sK5,sK5)
    | X1 != sK5
    | X2 != sK5
    | X0 != sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_7006])).

cnf(c_7028,plain,
    ( r2_relset_1(X0,sK2,X1,X2)
    | ~ r2_relset_1(sK3,sK2,sK5,sK5)
    | X1 != sK5
    | X2 != sK5
    | X0 != sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_7027])).

cnf(c_7067,plain,
    ( r2_relset_1(sK3,sK2,k5_relset_1(sK3,sK2,sK5,sK4),sK5)
    | ~ r2_relset_1(sK3,sK2,sK5,sK5)
    | k5_relset_1(sK3,sK2,sK5,sK4) != sK5
    | sK5 != sK5
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_7028])).

cnf(c_7068,plain,
    ( r2_relset_1(sK3,sK2,k5_relset_1(sK3,sK2,sK5,sK4),sK5)
    | ~ r2_relset_1(sK3,sK2,sK5,sK5)
    | k5_relset_1(sK3,sK2,sK5,sK4) != sK5 ),
    inference(equality_resolution_simp,[status(thm)],[c_7067])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_6956,plain,
    ( v1_relat_1(sK5) ),
    inference(resolution,[status(thm)],[c_0,c_19])).

cnf(c_8,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2822,plain,
    ( r2_relset_1(sK3,sK2,sK5,sK5) ),
    inference(resolution,[status(thm)],[c_8,c_19])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_606,plain,
    ( ~ r1_tarski(sK3,sK4)
    | m1_subset_1(sK3,k1_zfmisc_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_17,negated_conjecture,
    ( ~ r2_relset_1(sK3,sK2,k5_relset_1(sK3,sK2,sK5,sK4),sK5) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_35742,c_35669,c_35652,c_35641,c_35631,c_35509,c_35287,c_35187,c_35188,c_7621,c_7259,c_7253,c_7068,c_6956,c_2822,c_606,c_17,c_18,c_19])).


%------------------------------------------------------------------------------
