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
% DateTime   : Thu Dec  3 12:00:58 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 331 expanded)
%              Number of clauses        :   69 ( 101 expanded)
%              Number of leaves         :   18 (  85 expanded)
%              Depth                    :   19
%              Number of atoms          :  388 (1539 expanded)
%              Number of equality atoms :  126 ( 476 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f37,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK6(X3)) = X3
        & r2_hidden(sK6(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(X0,X1,X2) != X1
        & ! [X3] :
            ( ? [X4] :
                ( k1_funct_1(X2,X4) = X3
                & r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( k2_relset_1(sK3,sK4,sK5) != sK4
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK5,X4) = X3
              & r2_hidden(X4,sK3) )
          | ~ r2_hidden(X3,sK4) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK5,sK3,sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( k2_relset_1(sK3,sK4,sK5) != sK4
    & ! [X3] :
        ( ( k1_funct_1(sK5,sK6(X3)) = X3
          & r2_hidden(sK6(X3),sK3) )
        | ~ r2_hidden(X3,sK4) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f23,f37,f36])).

fof(f61,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
              | ~ r2_hidden(X3,X1) )
          | k2_relset_1(X0,X1,X2) != X1 )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
              | ~ r2_hidden(X3,X1) )
          | k2_relset_1(X0,X1,X2) != X1 )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ? [X5] :
              ( ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X2)
              & r2_hidden(X5,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f31])).

fof(f34,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(X6,sK2(X1,X2)),X2)
        & r2_hidden(sK2(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
     => r2_hidden(k4_tarski(sK1(X2,X3),X3),X2) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(sK1(X2,X3),X3),X2)
              | ~ r2_hidden(X3,X1) )
          | k2_relset_1(X0,X1,X2) != X1 )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(X6,sK2(X1,X2)),X2)
            & r2_hidden(sK2(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f32,f34,f33])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | r2_hidden(sK2(X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f64,plain,(
    k2_relset_1(sK3,sK4,sK5) != sK4 ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    ! [X3] :
      ( k1_funct_1(sK5,sK6(X3)) = X3
      | ~ r2_hidden(X3,sK4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f20])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f62,plain,(
    ! [X3] :
      ( r2_hidden(sK6(X3),sK3)
      | ~ r2_hidden(X3,sK4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f15])).

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
     => ( r2_hidden(sK0(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
        & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
            & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f54,plain,(
    ! [X6,X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_hidden(k4_tarski(X6,sK2(X1,X2)),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1096,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_16,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
    | k2_relset_1(X2,X0,X1) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1101,plain,
    ( k2_relset_1(X0,X1,X2) = X1
    | r2_hidden(sK2(X1,X2),X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2830,plain,
    ( k2_relset_1(sK3,sK4,sK5) = sK4
    | r2_hidden(sK2(sK4,sK5),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1096,c_1101])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1099,plain,
    ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2152,plain,
    ( k7_relset_1(sK3,sK4,sK5,sK3) = k2_relset_1(sK3,sK4,sK5) ),
    inference(superposition,[status(thm)],[c_1096,c_1099])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1104,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1717,plain,
    ( k7_relset_1(sK3,sK4,sK5,X0) = k9_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_1096,c_1104])).

cnf(c_2154,plain,
    ( k2_relset_1(sK3,sK4,sK5) = k9_relat_1(sK5,sK3) ),
    inference(demodulation,[status(thm)],[c_2152,c_1717])).

cnf(c_2833,plain,
    ( k9_relat_1(sK5,sK3) = sK4
    | r2_hidden(sK2(sK4,sK5),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2830,c_2154])).

cnf(c_28,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_20,negated_conjecture,
    ( k2_relset_1(sK3,sK4,sK5) != sK4 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1321,plain,
    ( r2_hidden(sK2(sK4,sK5),sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k2_relset_1(sK3,sK4,sK5) = sK4 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1322,plain,
    ( k2_relset_1(sK3,sK4,sK5) = sK4
    | r2_hidden(sK2(sK4,sK5),sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1321])).

cnf(c_3332,plain,
    ( r2_hidden(sK2(sK4,sK5),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2833,c_28,c_20,c_1322])).

cnf(c_21,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | k1_funct_1(sK5,sK6(X0)) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1098,plain,
    ( k1_funct_1(sK5,sK6(X0)) = X0
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3337,plain,
    ( k1_funct_1(sK5,sK6(sK2(sK4,sK5))) = sK2(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_3332,c_1098])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_336,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k1_funct_1(X2,X0),k2_relset_1(X1,X3,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | sK5 != X2
    | sK4 != X3
    | sK3 != X1
    | k1_xboole_0 = X3 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_337,plain,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(k1_funct_1(sK5,X0),k2_relset_1(sK3,sK4,sK5))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK5)
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_341,plain,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(k1_funct_1(sK5,X0),k2_relset_1(sK3,sK4,sK5))
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_337,c_25,c_23])).

cnf(c_1094,plain,
    ( k1_xboole_0 = sK4
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k2_relset_1(sK3,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_341])).

cnf(c_2456,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k9_relat_1(sK5,sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2154,c_1094])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1275,plain,
    ( ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),sK4)
    | ~ r1_tarski(sK4,k2_relset_1(sK3,sK4,sK5))
    | k2_relset_1(sK3,sK4,sK5) = sK4 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1284,plain,
    ( m1_subset_1(k2_relset_1(sK3,sK4,sK5),k1_zfmisc_1(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1359,plain,
    ( ~ m1_subset_1(k2_relset_1(sK3,sK4,sK5),k1_zfmisc_1(sK4))
    | r1_tarski(k2_relset_1(sK3,sK4,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1508,plain,
    ( r1_tarski(k1_xboole_0,k2_relset_1(sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_563,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_1471,plain,
    ( ~ r1_tarski(X0,k2_relset_1(sK3,sK4,sK5))
    | r1_tarski(sK4,k2_relset_1(sK3,sK4,sK5))
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_563])).

cnf(c_1990,plain,
    ( r1_tarski(sK4,k2_relset_1(sK3,sK4,sK5))
    | ~ r1_tarski(k1_xboole_0,k2_relset_1(sK3,sK4,sK5))
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1471])).

cnf(c_2677,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k9_relat_1(sK5,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2456,c_23,c_20,c_1275,c_1284,c_1359,c_1508,c_1990])).

cnf(c_3466,plain,
    ( r2_hidden(sK2(sK4,sK5),k9_relat_1(sK5,sK3)) = iProver_top
    | r2_hidden(sK6(sK2(sK4,sK5)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3337,c_2677])).

cnf(c_22,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(sK6(X0),sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1377,plain,
    ( ~ r2_hidden(sK2(sK4,sK5),sK4)
    | r2_hidden(sK6(sK2(sK4,sK5)),sK3) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1378,plain,
    ( r2_hidden(sK2(sK4,sK5),sK4) != iProver_top
    | r2_hidden(sK6(sK2(sK4,sK5)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1377])).

cnf(c_3469,plain,
    ( r2_hidden(sK2(sK4,sK5),k9_relat_1(sK5,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3466,c_28,c_20,c_1322,c_1378])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1107,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_15,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK2(X1,X2)),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | k2_relset_1(X3,X1,X2) = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1102,plain,
    ( k2_relset_1(X0,X1,X2) = X1
    | r2_hidden(k4_tarski(X3,sK2(X1,X2)),X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2883,plain,
    ( k2_relset_1(X0,X1,X2) = X1
    | r2_hidden(sK2(X1,X2),k9_relat_1(X2,X3)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1107,c_1102])).

cnf(c_8247,plain,
    ( k2_relset_1(X0,sK4,sK5) = sK4
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3469,c_2883])).

cnf(c_1111,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1481,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1096,c_1111])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_200,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_201,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_200])).

cnf(c_249,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_201])).

cnf(c_1349,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_249])).

cnf(c_1744,plain,
    ( ~ r1_tarski(sK5,k2_zfmisc_1(sK3,sK4))
    | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1349])).

cnf(c_1746,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1744])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1908,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1909,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1908])).

cnf(c_9102,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) != iProver_top
    | k2_relset_1(X0,sK4,sK5) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8247,c_1481,c_1746,c_1909])).

cnf(c_9103,plain,
    ( k2_relset_1(X0,sK4,sK5) = sK4
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_9102])).

cnf(c_9111,plain,
    ( k2_relset_1(sK3,sK4,sK5) = sK4 ),
    inference(superposition,[status(thm)],[c_1096,c_9103])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9111,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:51:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.74/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/1.01  
% 3.74/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.74/1.01  
% 3.74/1.01  ------  iProver source info
% 3.74/1.01  
% 3.74/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.74/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.74/1.01  git: non_committed_changes: false
% 3.74/1.01  git: last_make_outside_of_git: false
% 3.74/1.01  
% 3.74/1.01  ------ 
% 3.74/1.01  
% 3.74/1.01  ------ Input Options
% 3.74/1.01  
% 3.74/1.01  --out_options                           all
% 3.74/1.01  --tptp_safe_out                         true
% 3.74/1.01  --problem_path                          ""
% 3.74/1.01  --include_path                          ""
% 3.74/1.01  --clausifier                            res/vclausify_rel
% 3.74/1.01  --clausifier_options                    --mode clausify
% 3.74/1.01  --stdin                                 false
% 3.74/1.01  --stats_out                             all
% 3.74/1.01  
% 3.74/1.01  ------ General Options
% 3.74/1.01  
% 3.74/1.01  --fof                                   false
% 3.74/1.01  --time_out_real                         305.
% 3.74/1.01  --time_out_virtual                      -1.
% 3.74/1.01  --symbol_type_check                     false
% 3.74/1.01  --clausify_out                          false
% 3.74/1.01  --sig_cnt_out                           false
% 3.74/1.01  --trig_cnt_out                          false
% 3.74/1.01  --trig_cnt_out_tolerance                1.
% 3.74/1.01  --trig_cnt_out_sk_spl                   false
% 3.74/1.01  --abstr_cl_out                          false
% 3.74/1.01  
% 3.74/1.01  ------ Global Options
% 3.74/1.01  
% 3.74/1.01  --schedule                              default
% 3.74/1.01  --add_important_lit                     false
% 3.74/1.01  --prop_solver_per_cl                    1000
% 3.74/1.01  --min_unsat_core                        false
% 3.74/1.01  --soft_assumptions                      false
% 3.74/1.01  --soft_lemma_size                       3
% 3.74/1.01  --prop_impl_unit_size                   0
% 3.74/1.01  --prop_impl_unit                        []
% 3.74/1.01  --share_sel_clauses                     true
% 3.74/1.01  --reset_solvers                         false
% 3.74/1.01  --bc_imp_inh                            [conj_cone]
% 3.74/1.01  --conj_cone_tolerance                   3.
% 3.74/1.01  --extra_neg_conj                        none
% 3.74/1.01  --large_theory_mode                     true
% 3.74/1.01  --prolific_symb_bound                   200
% 3.74/1.01  --lt_threshold                          2000
% 3.74/1.01  --clause_weak_htbl                      true
% 3.74/1.01  --gc_record_bc_elim                     false
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing Options
% 3.74/1.01  
% 3.74/1.01  --preprocessing_flag                    true
% 3.74/1.01  --time_out_prep_mult                    0.1
% 3.74/1.01  --splitting_mode                        input
% 3.74/1.01  --splitting_grd                         true
% 3.74/1.01  --splitting_cvd                         false
% 3.74/1.01  --splitting_cvd_svl                     false
% 3.74/1.01  --splitting_nvd                         32
% 3.74/1.01  --sub_typing                            true
% 3.74/1.01  --prep_gs_sim                           true
% 3.74/1.01  --prep_unflatten                        true
% 3.74/1.01  --prep_res_sim                          true
% 3.74/1.01  --prep_upred                            true
% 3.74/1.01  --prep_sem_filter                       exhaustive
% 3.74/1.01  --prep_sem_filter_out                   false
% 3.74/1.01  --pred_elim                             true
% 3.74/1.01  --res_sim_input                         true
% 3.74/1.01  --eq_ax_congr_red                       true
% 3.74/1.01  --pure_diseq_elim                       true
% 3.74/1.01  --brand_transform                       false
% 3.74/1.01  --non_eq_to_eq                          false
% 3.74/1.01  --prep_def_merge                        true
% 3.74/1.01  --prep_def_merge_prop_impl              false
% 3.74/1.01  --prep_def_merge_mbd                    true
% 3.74/1.01  --prep_def_merge_tr_red                 false
% 3.74/1.01  --prep_def_merge_tr_cl                  false
% 3.74/1.01  --smt_preprocessing                     true
% 3.74/1.01  --smt_ac_axioms                         fast
% 3.74/1.01  --preprocessed_out                      false
% 3.74/1.01  --preprocessed_stats                    false
% 3.74/1.01  
% 3.74/1.01  ------ Abstraction refinement Options
% 3.74/1.01  
% 3.74/1.01  --abstr_ref                             []
% 3.74/1.01  --abstr_ref_prep                        false
% 3.74/1.01  --abstr_ref_until_sat                   false
% 3.74/1.01  --abstr_ref_sig_restrict                funpre
% 3.74/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.74/1.01  --abstr_ref_under                       []
% 3.74/1.01  
% 3.74/1.01  ------ SAT Options
% 3.74/1.01  
% 3.74/1.01  --sat_mode                              false
% 3.74/1.01  --sat_fm_restart_options                ""
% 3.74/1.01  --sat_gr_def                            false
% 3.74/1.01  --sat_epr_types                         true
% 3.74/1.01  --sat_non_cyclic_types                  false
% 3.74/1.01  --sat_finite_models                     false
% 3.74/1.01  --sat_fm_lemmas                         false
% 3.74/1.01  --sat_fm_prep                           false
% 3.74/1.01  --sat_fm_uc_incr                        true
% 3.74/1.01  --sat_out_model                         small
% 3.74/1.01  --sat_out_clauses                       false
% 3.74/1.01  
% 3.74/1.01  ------ QBF Options
% 3.74/1.01  
% 3.74/1.01  --qbf_mode                              false
% 3.74/1.01  --qbf_elim_univ                         false
% 3.74/1.01  --qbf_dom_inst                          none
% 3.74/1.01  --qbf_dom_pre_inst                      false
% 3.74/1.01  --qbf_sk_in                             false
% 3.74/1.01  --qbf_pred_elim                         true
% 3.74/1.01  --qbf_split                             512
% 3.74/1.01  
% 3.74/1.01  ------ BMC1 Options
% 3.74/1.01  
% 3.74/1.01  --bmc1_incremental                      false
% 3.74/1.01  --bmc1_axioms                           reachable_all
% 3.74/1.01  --bmc1_min_bound                        0
% 3.74/1.01  --bmc1_max_bound                        -1
% 3.74/1.01  --bmc1_max_bound_default                -1
% 3.74/1.01  --bmc1_symbol_reachability              true
% 3.74/1.01  --bmc1_property_lemmas                  false
% 3.74/1.01  --bmc1_k_induction                      false
% 3.74/1.01  --bmc1_non_equiv_states                 false
% 3.74/1.01  --bmc1_deadlock                         false
% 3.74/1.01  --bmc1_ucm                              false
% 3.74/1.01  --bmc1_add_unsat_core                   none
% 3.74/1.01  --bmc1_unsat_core_children              false
% 3.74/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.74/1.01  --bmc1_out_stat                         full
% 3.74/1.01  --bmc1_ground_init                      false
% 3.74/1.01  --bmc1_pre_inst_next_state              false
% 3.74/1.01  --bmc1_pre_inst_state                   false
% 3.74/1.01  --bmc1_pre_inst_reach_state             false
% 3.74/1.01  --bmc1_out_unsat_core                   false
% 3.74/1.01  --bmc1_aig_witness_out                  false
% 3.74/1.01  --bmc1_verbose                          false
% 3.74/1.01  --bmc1_dump_clauses_tptp                false
% 3.74/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.74/1.01  --bmc1_dump_file                        -
% 3.74/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.74/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.74/1.01  --bmc1_ucm_extend_mode                  1
% 3.74/1.01  --bmc1_ucm_init_mode                    2
% 3.74/1.01  --bmc1_ucm_cone_mode                    none
% 3.74/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.74/1.01  --bmc1_ucm_relax_model                  4
% 3.74/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.74/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.74/1.01  --bmc1_ucm_layered_model                none
% 3.74/1.01  --bmc1_ucm_max_lemma_size               10
% 3.74/1.01  
% 3.74/1.01  ------ AIG Options
% 3.74/1.01  
% 3.74/1.01  --aig_mode                              false
% 3.74/1.01  
% 3.74/1.01  ------ Instantiation Options
% 3.74/1.01  
% 3.74/1.01  --instantiation_flag                    true
% 3.74/1.01  --inst_sos_flag                         false
% 3.74/1.01  --inst_sos_phase                        true
% 3.74/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.74/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.74/1.01  --inst_lit_sel_side                     num_symb
% 3.74/1.01  --inst_solver_per_active                1400
% 3.74/1.01  --inst_solver_calls_frac                1.
% 3.74/1.01  --inst_passive_queue_type               priority_queues
% 3.74/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.74/1.01  --inst_passive_queues_freq              [25;2]
% 3.74/1.01  --inst_dismatching                      true
% 3.74/1.01  --inst_eager_unprocessed_to_passive     true
% 3.74/1.01  --inst_prop_sim_given                   true
% 3.74/1.01  --inst_prop_sim_new                     false
% 3.74/1.01  --inst_subs_new                         false
% 3.74/1.01  --inst_eq_res_simp                      false
% 3.74/1.01  --inst_subs_given                       false
% 3.74/1.01  --inst_orphan_elimination               true
% 3.74/1.01  --inst_learning_loop_flag               true
% 3.74/1.01  --inst_learning_start                   3000
% 3.74/1.01  --inst_learning_factor                  2
% 3.74/1.01  --inst_start_prop_sim_after_learn       3
% 3.74/1.01  --inst_sel_renew                        solver
% 3.74/1.01  --inst_lit_activity_flag                true
% 3.74/1.01  --inst_restr_to_given                   false
% 3.74/1.01  --inst_activity_threshold               500
% 3.74/1.01  --inst_out_proof                        true
% 3.74/1.01  
% 3.74/1.01  ------ Resolution Options
% 3.74/1.01  
% 3.74/1.01  --resolution_flag                       true
% 3.74/1.01  --res_lit_sel                           adaptive
% 3.74/1.01  --res_lit_sel_side                      none
% 3.74/1.01  --res_ordering                          kbo
% 3.74/1.01  --res_to_prop_solver                    active
% 3.74/1.01  --res_prop_simpl_new                    false
% 3.74/1.01  --res_prop_simpl_given                  true
% 3.74/1.01  --res_passive_queue_type                priority_queues
% 3.74/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.74/1.01  --res_passive_queues_freq               [15;5]
% 3.74/1.01  --res_forward_subs                      full
% 3.74/1.01  --res_backward_subs                     full
% 3.74/1.01  --res_forward_subs_resolution           true
% 3.74/1.01  --res_backward_subs_resolution          true
% 3.74/1.01  --res_orphan_elimination                true
% 3.74/1.01  --res_time_limit                        2.
% 3.74/1.01  --res_out_proof                         true
% 3.74/1.01  
% 3.74/1.01  ------ Superposition Options
% 3.74/1.01  
% 3.74/1.01  --superposition_flag                    true
% 3.74/1.01  --sup_passive_queue_type                priority_queues
% 3.74/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.74/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.74/1.01  --demod_completeness_check              fast
% 3.74/1.01  --demod_use_ground                      true
% 3.74/1.01  --sup_to_prop_solver                    passive
% 3.74/1.01  --sup_prop_simpl_new                    true
% 3.74/1.01  --sup_prop_simpl_given                  true
% 3.74/1.01  --sup_fun_splitting                     false
% 3.74/1.01  --sup_smt_interval                      50000
% 3.74/1.01  
% 3.74/1.01  ------ Superposition Simplification Setup
% 3.74/1.01  
% 3.74/1.01  --sup_indices_passive                   []
% 3.74/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.74/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.74/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.74/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.74/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.74/1.01  --sup_full_bw                           [BwDemod]
% 3.74/1.01  --sup_immed_triv                        [TrivRules]
% 3.74/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.74/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.74/1.01  --sup_immed_bw_main                     []
% 3.74/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.74/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.74/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.74/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.74/1.01  
% 3.74/1.01  ------ Combination Options
% 3.74/1.01  
% 3.74/1.01  --comb_res_mult                         3
% 3.74/1.01  --comb_sup_mult                         2
% 3.74/1.01  --comb_inst_mult                        10
% 3.74/1.01  
% 3.74/1.01  ------ Debug Options
% 3.74/1.01  
% 3.74/1.01  --dbg_backtrace                         false
% 3.74/1.01  --dbg_dump_prop_clauses                 false
% 3.74/1.01  --dbg_dump_prop_clauses_file            -
% 3.74/1.01  --dbg_out_stat                          false
% 3.74/1.01  ------ Parsing...
% 3.74/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  ------ Proving...
% 3.74/1.01  ------ Problem Properties 
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  clauses                                 23
% 3.74/1.01  conjectures                             4
% 3.74/1.01  EPR                                     4
% 3.74/1.01  Horn                                    21
% 3.74/1.01  unary                                   5
% 3.74/1.01  binary                                  8
% 3.74/1.01  lits                                    54
% 3.74/1.01  lits eq                                 10
% 3.74/1.01  fd_pure                                 0
% 3.74/1.01  fd_pseudo                               0
% 3.74/1.01  fd_cond                                 0
% 3.74/1.01  fd_pseudo_cond                          1
% 3.74/1.01  AC symbols                              0
% 3.74/1.01  
% 3.74/1.01  ------ Schedule dynamic 5 is on 
% 3.74/1.01  
% 3.74/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ 
% 3.74/1.01  Current options:
% 3.74/1.01  ------ 
% 3.74/1.01  
% 3.74/1.01  ------ Input Options
% 3.74/1.01  
% 3.74/1.01  --out_options                           all
% 3.74/1.01  --tptp_safe_out                         true
% 3.74/1.01  --problem_path                          ""
% 3.74/1.01  --include_path                          ""
% 3.74/1.01  --clausifier                            res/vclausify_rel
% 3.74/1.01  --clausifier_options                    --mode clausify
% 3.74/1.01  --stdin                                 false
% 3.74/1.01  --stats_out                             all
% 3.74/1.01  
% 3.74/1.01  ------ General Options
% 3.74/1.01  
% 3.74/1.01  --fof                                   false
% 3.74/1.01  --time_out_real                         305.
% 3.74/1.01  --time_out_virtual                      -1.
% 3.74/1.01  --symbol_type_check                     false
% 3.74/1.01  --clausify_out                          false
% 3.74/1.01  --sig_cnt_out                           false
% 3.74/1.01  --trig_cnt_out                          false
% 3.74/1.01  --trig_cnt_out_tolerance                1.
% 3.74/1.01  --trig_cnt_out_sk_spl                   false
% 3.74/1.01  --abstr_cl_out                          false
% 3.74/1.01  
% 3.74/1.01  ------ Global Options
% 3.74/1.01  
% 3.74/1.01  --schedule                              default
% 3.74/1.01  --add_important_lit                     false
% 3.74/1.01  --prop_solver_per_cl                    1000
% 3.74/1.01  --min_unsat_core                        false
% 3.74/1.01  --soft_assumptions                      false
% 3.74/1.01  --soft_lemma_size                       3
% 3.74/1.01  --prop_impl_unit_size                   0
% 3.74/1.01  --prop_impl_unit                        []
% 3.74/1.01  --share_sel_clauses                     true
% 3.74/1.01  --reset_solvers                         false
% 3.74/1.01  --bc_imp_inh                            [conj_cone]
% 3.74/1.01  --conj_cone_tolerance                   3.
% 3.74/1.01  --extra_neg_conj                        none
% 3.74/1.01  --large_theory_mode                     true
% 3.74/1.01  --prolific_symb_bound                   200
% 3.74/1.01  --lt_threshold                          2000
% 3.74/1.01  --clause_weak_htbl                      true
% 3.74/1.01  --gc_record_bc_elim                     false
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing Options
% 3.74/1.01  
% 3.74/1.01  --preprocessing_flag                    true
% 3.74/1.01  --time_out_prep_mult                    0.1
% 3.74/1.01  --splitting_mode                        input
% 3.74/1.01  --splitting_grd                         true
% 3.74/1.01  --splitting_cvd                         false
% 3.74/1.01  --splitting_cvd_svl                     false
% 3.74/1.01  --splitting_nvd                         32
% 3.74/1.01  --sub_typing                            true
% 3.74/1.01  --prep_gs_sim                           true
% 3.74/1.01  --prep_unflatten                        true
% 3.74/1.01  --prep_res_sim                          true
% 3.74/1.01  --prep_upred                            true
% 3.74/1.01  --prep_sem_filter                       exhaustive
% 3.74/1.01  --prep_sem_filter_out                   false
% 3.74/1.01  --pred_elim                             true
% 3.74/1.01  --res_sim_input                         true
% 3.74/1.01  --eq_ax_congr_red                       true
% 3.74/1.01  --pure_diseq_elim                       true
% 3.74/1.01  --brand_transform                       false
% 3.74/1.01  --non_eq_to_eq                          false
% 3.74/1.01  --prep_def_merge                        true
% 3.74/1.01  --prep_def_merge_prop_impl              false
% 3.74/1.01  --prep_def_merge_mbd                    true
% 3.74/1.01  --prep_def_merge_tr_red                 false
% 3.74/1.01  --prep_def_merge_tr_cl                  false
% 3.74/1.01  --smt_preprocessing                     true
% 3.74/1.01  --smt_ac_axioms                         fast
% 3.74/1.01  --preprocessed_out                      false
% 3.74/1.01  --preprocessed_stats                    false
% 3.74/1.01  
% 3.74/1.01  ------ Abstraction refinement Options
% 3.74/1.01  
% 3.74/1.01  --abstr_ref                             []
% 3.74/1.01  --abstr_ref_prep                        false
% 3.74/1.01  --abstr_ref_until_sat                   false
% 3.74/1.01  --abstr_ref_sig_restrict                funpre
% 3.74/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.74/1.01  --abstr_ref_under                       []
% 3.74/1.01  
% 3.74/1.01  ------ SAT Options
% 3.74/1.01  
% 3.74/1.01  --sat_mode                              false
% 3.74/1.01  --sat_fm_restart_options                ""
% 3.74/1.01  --sat_gr_def                            false
% 3.74/1.01  --sat_epr_types                         true
% 3.74/1.01  --sat_non_cyclic_types                  false
% 3.74/1.01  --sat_finite_models                     false
% 3.74/1.01  --sat_fm_lemmas                         false
% 3.74/1.01  --sat_fm_prep                           false
% 3.74/1.01  --sat_fm_uc_incr                        true
% 3.74/1.01  --sat_out_model                         small
% 3.74/1.01  --sat_out_clauses                       false
% 3.74/1.01  
% 3.74/1.01  ------ QBF Options
% 3.74/1.01  
% 3.74/1.01  --qbf_mode                              false
% 3.74/1.01  --qbf_elim_univ                         false
% 3.74/1.01  --qbf_dom_inst                          none
% 3.74/1.01  --qbf_dom_pre_inst                      false
% 3.74/1.01  --qbf_sk_in                             false
% 3.74/1.01  --qbf_pred_elim                         true
% 3.74/1.01  --qbf_split                             512
% 3.74/1.01  
% 3.74/1.01  ------ BMC1 Options
% 3.74/1.01  
% 3.74/1.01  --bmc1_incremental                      false
% 3.74/1.01  --bmc1_axioms                           reachable_all
% 3.74/1.01  --bmc1_min_bound                        0
% 3.74/1.01  --bmc1_max_bound                        -1
% 3.74/1.01  --bmc1_max_bound_default                -1
% 3.74/1.01  --bmc1_symbol_reachability              true
% 3.74/1.01  --bmc1_property_lemmas                  false
% 3.74/1.01  --bmc1_k_induction                      false
% 3.74/1.01  --bmc1_non_equiv_states                 false
% 3.74/1.01  --bmc1_deadlock                         false
% 3.74/1.01  --bmc1_ucm                              false
% 3.74/1.01  --bmc1_add_unsat_core                   none
% 3.74/1.01  --bmc1_unsat_core_children              false
% 3.74/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.74/1.01  --bmc1_out_stat                         full
% 3.74/1.01  --bmc1_ground_init                      false
% 3.74/1.01  --bmc1_pre_inst_next_state              false
% 3.74/1.01  --bmc1_pre_inst_state                   false
% 3.74/1.01  --bmc1_pre_inst_reach_state             false
% 3.74/1.01  --bmc1_out_unsat_core                   false
% 3.74/1.01  --bmc1_aig_witness_out                  false
% 3.74/1.01  --bmc1_verbose                          false
% 3.74/1.01  --bmc1_dump_clauses_tptp                false
% 3.74/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.74/1.01  --bmc1_dump_file                        -
% 3.74/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.74/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.74/1.01  --bmc1_ucm_extend_mode                  1
% 3.74/1.01  --bmc1_ucm_init_mode                    2
% 3.74/1.01  --bmc1_ucm_cone_mode                    none
% 3.74/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.74/1.01  --bmc1_ucm_relax_model                  4
% 3.74/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.74/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.74/1.01  --bmc1_ucm_layered_model                none
% 3.74/1.01  --bmc1_ucm_max_lemma_size               10
% 3.74/1.01  
% 3.74/1.01  ------ AIG Options
% 3.74/1.01  
% 3.74/1.01  --aig_mode                              false
% 3.74/1.01  
% 3.74/1.01  ------ Instantiation Options
% 3.74/1.01  
% 3.74/1.01  --instantiation_flag                    true
% 3.74/1.01  --inst_sos_flag                         false
% 3.74/1.01  --inst_sos_phase                        true
% 3.74/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.74/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.74/1.01  --inst_lit_sel_side                     none
% 3.74/1.01  --inst_solver_per_active                1400
% 3.74/1.01  --inst_solver_calls_frac                1.
% 3.74/1.01  --inst_passive_queue_type               priority_queues
% 3.74/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.74/1.01  --inst_passive_queues_freq              [25;2]
% 3.74/1.01  --inst_dismatching                      true
% 3.74/1.01  --inst_eager_unprocessed_to_passive     true
% 3.74/1.01  --inst_prop_sim_given                   true
% 3.74/1.01  --inst_prop_sim_new                     false
% 3.74/1.01  --inst_subs_new                         false
% 3.74/1.01  --inst_eq_res_simp                      false
% 3.74/1.01  --inst_subs_given                       false
% 3.74/1.01  --inst_orphan_elimination               true
% 3.74/1.01  --inst_learning_loop_flag               true
% 3.74/1.01  --inst_learning_start                   3000
% 3.74/1.01  --inst_learning_factor                  2
% 3.74/1.01  --inst_start_prop_sim_after_learn       3
% 3.74/1.01  --inst_sel_renew                        solver
% 3.74/1.01  --inst_lit_activity_flag                true
% 3.74/1.01  --inst_restr_to_given                   false
% 3.74/1.01  --inst_activity_threshold               500
% 3.74/1.01  --inst_out_proof                        true
% 3.74/1.01  
% 3.74/1.01  ------ Resolution Options
% 3.74/1.01  
% 3.74/1.01  --resolution_flag                       false
% 3.74/1.01  --res_lit_sel                           adaptive
% 3.74/1.01  --res_lit_sel_side                      none
% 3.74/1.01  --res_ordering                          kbo
% 3.74/1.01  --res_to_prop_solver                    active
% 3.74/1.01  --res_prop_simpl_new                    false
% 3.74/1.01  --res_prop_simpl_given                  true
% 3.74/1.01  --res_passive_queue_type                priority_queues
% 3.74/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.74/1.01  --res_passive_queues_freq               [15;5]
% 3.74/1.01  --res_forward_subs                      full
% 3.74/1.01  --res_backward_subs                     full
% 3.74/1.01  --res_forward_subs_resolution           true
% 3.74/1.01  --res_backward_subs_resolution          true
% 3.74/1.01  --res_orphan_elimination                true
% 3.74/1.01  --res_time_limit                        2.
% 3.74/1.01  --res_out_proof                         true
% 3.74/1.01  
% 3.74/1.01  ------ Superposition Options
% 3.74/1.01  
% 3.74/1.01  --superposition_flag                    true
% 3.74/1.01  --sup_passive_queue_type                priority_queues
% 3.74/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.74/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.74/1.01  --demod_completeness_check              fast
% 3.74/1.01  --demod_use_ground                      true
% 3.74/1.01  --sup_to_prop_solver                    passive
% 3.74/1.01  --sup_prop_simpl_new                    true
% 3.74/1.01  --sup_prop_simpl_given                  true
% 3.74/1.01  --sup_fun_splitting                     false
% 3.74/1.01  --sup_smt_interval                      50000
% 3.74/1.01  
% 3.74/1.01  ------ Superposition Simplification Setup
% 3.74/1.01  
% 3.74/1.01  --sup_indices_passive                   []
% 3.74/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.74/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.74/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.74/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.74/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.74/1.01  --sup_full_bw                           [BwDemod]
% 3.74/1.01  --sup_immed_triv                        [TrivRules]
% 3.74/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.74/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.74/1.01  --sup_immed_bw_main                     []
% 3.74/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.74/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.74/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.74/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.74/1.01  
% 3.74/1.01  ------ Combination Options
% 3.74/1.01  
% 3.74/1.01  --comb_res_mult                         3
% 3.74/1.01  --comb_sup_mult                         2
% 3.74/1.01  --comb_inst_mult                        10
% 3.74/1.01  
% 3.74/1.01  ------ Debug Options
% 3.74/1.01  
% 3.74/1.01  --dbg_backtrace                         false
% 3.74/1.01  --dbg_dump_prop_clauses                 false
% 3.74/1.01  --dbg_dump_prop_clauses_file            -
% 3.74/1.01  --dbg_out_stat                          false
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  % SZS status Theorem for theBenchmark.p
% 3.74/1.01  
% 3.74/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.74/1.01  
% 3.74/1.01  fof(f12,conjecture,(
% 3.74/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 3.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f13,negated_conjecture,(
% 3.74/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 3.74/1.01    inference(negated_conjecture,[],[f12])).
% 3.74/1.01  
% 3.74/1.01  fof(f22,plain,(
% 3.74/1.01    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.74/1.01    inference(ennf_transformation,[],[f13])).
% 3.74/1.01  
% 3.74/1.01  fof(f23,plain,(
% 3.74/1.01    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.74/1.01    inference(flattening,[],[f22])).
% 3.74/1.01  
% 3.74/1.01  fof(f37,plain,(
% 3.74/1.01    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK6(X3)) = X3 & r2_hidden(sK6(X3),X0)))) )),
% 3.74/1.01    introduced(choice_axiom,[])).
% 3.74/1.01  
% 3.74/1.01  fof(f36,plain,(
% 3.74/1.01    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK3,sK4,sK5) != sK4 & ! [X3] : (? [X4] : (k1_funct_1(sK5,X4) = X3 & r2_hidden(X4,sK3)) | ~r2_hidden(X3,sK4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 3.74/1.01    introduced(choice_axiom,[])).
% 3.74/1.01  
% 3.74/1.01  fof(f38,plain,(
% 3.74/1.01    k2_relset_1(sK3,sK4,sK5) != sK4 & ! [X3] : ((k1_funct_1(sK5,sK6(X3)) = X3 & r2_hidden(sK6(X3),sK3)) | ~r2_hidden(X3,sK4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 3.74/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f23,f37,f36])).
% 3.74/1.01  
% 3.74/1.01  fof(f61,plain,(
% 3.74/1.01    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.74/1.01    inference(cnf_transformation,[],[f38])).
% 3.74/1.01  
% 3.74/1.01  fof(f9,axiom,(
% 3.74/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 3.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f18,plain,(
% 3.74/1.01    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.74/1.01    inference(ennf_transformation,[],[f9])).
% 3.74/1.01  
% 3.74/1.01  fof(f31,plain,(
% 3.74/1.01    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) | k2_relset_1(X0,X1,X2) != X1) & (k2_relset_1(X0,X1,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.74/1.01    inference(nnf_transformation,[],[f18])).
% 3.74/1.01  
% 3.74/1.01  fof(f32,plain,(
% 3.74/1.01    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) | k2_relset_1(X0,X1,X2) != X1) & (k2_relset_1(X0,X1,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X6,X5),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.74/1.01    inference(rectify,[],[f31])).
% 3.74/1.01  
% 3.74/1.01  fof(f34,plain,(
% 3.74/1.01    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X6,X5),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(X6,sK2(X1,X2)),X2) & r2_hidden(sK2(X1,X2),X1)))),
% 3.74/1.01    introduced(choice_axiom,[])).
% 3.74/1.01  
% 3.74/1.01  fof(f33,plain,(
% 3.74/1.01    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) => r2_hidden(k4_tarski(sK1(X2,X3),X3),X2))),
% 3.74/1.01    introduced(choice_axiom,[])).
% 3.74/1.01  
% 3.74/1.01  fof(f35,plain,(
% 3.74/1.01    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(sK1(X2,X3),X3),X2) | ~r2_hidden(X3,X1)) | k2_relset_1(X0,X1,X2) != X1) & (k2_relset_1(X0,X1,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(X6,sK2(X1,X2)),X2) & r2_hidden(sK2(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.74/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f32,f34,f33])).
% 3.74/1.01  
% 3.74/1.01  fof(f53,plain,(
% 3.74/1.01    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = X1 | r2_hidden(sK2(X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.74/1.01    inference(cnf_transformation,[],[f35])).
% 3.74/1.01  
% 3.74/1.01  fof(f10,axiom,(
% 3.74/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 3.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f19,plain,(
% 3.74/1.01    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.74/1.01    inference(ennf_transformation,[],[f10])).
% 3.74/1.01  
% 3.74/1.01  fof(f56,plain,(
% 3.74/1.01    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.74/1.01    inference(cnf_transformation,[],[f19])).
% 3.74/1.01  
% 3.74/1.01  fof(f8,axiom,(
% 3.74/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f17,plain,(
% 3.74/1.01    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.74/1.01    inference(ennf_transformation,[],[f8])).
% 3.74/1.01  
% 3.74/1.01  fof(f52,plain,(
% 3.74/1.01    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.74/1.01    inference(cnf_transformation,[],[f17])).
% 3.74/1.01  
% 3.74/1.01  fof(f64,plain,(
% 3.74/1.01    k2_relset_1(sK3,sK4,sK5) != sK4),
% 3.74/1.01    inference(cnf_transformation,[],[f38])).
% 3.74/1.01  
% 3.74/1.01  fof(f63,plain,(
% 3.74/1.01    ( ! [X3] : (k1_funct_1(sK5,sK6(X3)) = X3 | ~r2_hidden(X3,sK4)) )),
% 3.74/1.01    inference(cnf_transformation,[],[f38])).
% 3.74/1.01  
% 3.74/1.01  fof(f11,axiom,(
% 3.74/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 3.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f20,plain,(
% 3.74/1.01    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.74/1.01    inference(ennf_transformation,[],[f11])).
% 3.74/1.01  
% 3.74/1.01  fof(f21,plain,(
% 3.74/1.01    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.74/1.01    inference(flattening,[],[f20])).
% 3.74/1.01  
% 3.74/1.01  fof(f58,plain,(
% 3.74/1.01    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.74/1.01    inference(cnf_transformation,[],[f21])).
% 3.74/1.01  
% 3.74/1.01  fof(f60,plain,(
% 3.74/1.01    v1_funct_2(sK5,sK3,sK4)),
% 3.74/1.01    inference(cnf_transformation,[],[f38])).
% 3.74/1.01  
% 3.74/1.01  fof(f59,plain,(
% 3.74/1.01    v1_funct_1(sK5)),
% 3.74/1.01    inference(cnf_transformation,[],[f38])).
% 3.74/1.01  
% 3.74/1.01  fof(f1,axiom,(
% 3.74/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f24,plain,(
% 3.74/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.74/1.01    inference(nnf_transformation,[],[f1])).
% 3.74/1.01  
% 3.74/1.01  fof(f25,plain,(
% 3.74/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.74/1.01    inference(flattening,[],[f24])).
% 3.74/1.01  
% 3.74/1.01  fof(f41,plain,(
% 3.74/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.74/1.01    inference(cnf_transformation,[],[f25])).
% 3.74/1.01  
% 3.74/1.01  fof(f7,axiom,(
% 3.74/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 3.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f16,plain,(
% 3.74/1.01    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.74/1.01    inference(ennf_transformation,[],[f7])).
% 3.74/1.01  
% 3.74/1.01  fof(f51,plain,(
% 3.74/1.01    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.74/1.01    inference(cnf_transformation,[],[f16])).
% 3.74/1.01  
% 3.74/1.01  fof(f3,axiom,(
% 3.74/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f26,plain,(
% 3.74/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.74/1.01    inference(nnf_transformation,[],[f3])).
% 3.74/1.01  
% 3.74/1.01  fof(f43,plain,(
% 3.74/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.74/1.01    inference(cnf_transformation,[],[f26])).
% 3.74/1.01  
% 3.74/1.01  fof(f2,axiom,(
% 3.74/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f42,plain,(
% 3.74/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.74/1.01    inference(cnf_transformation,[],[f2])).
% 3.74/1.01  
% 3.74/1.01  fof(f62,plain,(
% 3.74/1.01    ( ! [X3] : (r2_hidden(sK6(X3),sK3) | ~r2_hidden(X3,sK4)) )),
% 3.74/1.01    inference(cnf_transformation,[],[f38])).
% 3.74/1.01  
% 3.74/1.01  fof(f6,axiom,(
% 3.74/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f15,plain,(
% 3.74/1.01    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.74/1.01    inference(ennf_transformation,[],[f6])).
% 3.74/1.01  
% 3.74/1.01  fof(f27,plain,(
% 3.74/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.74/1.01    inference(nnf_transformation,[],[f15])).
% 3.74/1.01  
% 3.74/1.01  fof(f28,plain,(
% 3.74/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.74/1.01    inference(rectify,[],[f27])).
% 3.74/1.01  
% 3.74/1.01  fof(f29,plain,(
% 3.74/1.01    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))))),
% 3.74/1.01    introduced(choice_axiom,[])).
% 3.74/1.01  
% 3.74/1.01  fof(f30,plain,(
% 3.74/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.74/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 3.74/1.01  
% 3.74/1.01  fof(f48,plain,(
% 3.74/1.01    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.74/1.01    inference(cnf_transformation,[],[f30])).
% 3.74/1.01  
% 3.74/1.01  fof(f54,plain,(
% 3.74/1.01    ( ! [X6,X2,X0,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_hidden(k4_tarski(X6,sK2(X1,X2)),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.74/1.01    inference(cnf_transformation,[],[f35])).
% 3.74/1.01  
% 3.74/1.01  fof(f4,axiom,(
% 3.74/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f14,plain,(
% 3.74/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.74/1.01    inference(ennf_transformation,[],[f4])).
% 3.74/1.01  
% 3.74/1.01  fof(f45,plain,(
% 3.74/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.74/1.01    inference(cnf_transformation,[],[f14])).
% 3.74/1.01  
% 3.74/1.01  fof(f44,plain,(
% 3.74/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.74/1.01    inference(cnf_transformation,[],[f26])).
% 3.74/1.01  
% 3.74/1.01  fof(f5,axiom,(
% 3.74/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f46,plain,(
% 3.74/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.74/1.01    inference(cnf_transformation,[],[f5])).
% 3.74/1.01  
% 3.74/1.01  cnf(c_23,negated_conjecture,
% 3.74/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.74/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1096,plain,
% 3.74/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_16,plain,
% 3.74/1.01      ( r2_hidden(sK2(X0,X1),X0)
% 3.74/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
% 3.74/1.01      | k2_relset_1(X2,X0,X1) = X0 ),
% 3.74/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1101,plain,
% 3.74/1.01      ( k2_relset_1(X0,X1,X2) = X1
% 3.74/1.01      | r2_hidden(sK2(X1,X2),X1) = iProver_top
% 3.74/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_2830,plain,
% 3.74/1.01      ( k2_relset_1(sK3,sK4,sK5) = sK4
% 3.74/1.01      | r2_hidden(sK2(sK4,sK5),sK4) = iProver_top ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_1096,c_1101]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_18,plain,
% 3.74/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.74/1.01      | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
% 3.74/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1099,plain,
% 3.74/1.01      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
% 3.74/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_2152,plain,
% 3.74/1.01      ( k7_relset_1(sK3,sK4,sK5,sK3) = k2_relset_1(sK3,sK4,sK5) ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_1096,c_1099]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_13,plain,
% 3.74/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.74/1.01      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.74/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1104,plain,
% 3.74/1.01      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.74/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1717,plain,
% 3.74/1.01      ( k7_relset_1(sK3,sK4,sK5,X0) = k9_relat_1(sK5,X0) ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_1096,c_1104]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_2154,plain,
% 3.74/1.01      ( k2_relset_1(sK3,sK4,sK5) = k9_relat_1(sK5,sK3) ),
% 3.74/1.01      inference(demodulation,[status(thm)],[c_2152,c_1717]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_2833,plain,
% 3.74/1.01      ( k9_relat_1(sK5,sK3) = sK4
% 3.74/1.01      | r2_hidden(sK2(sK4,sK5),sK4) = iProver_top ),
% 3.74/1.01      inference(demodulation,[status(thm)],[c_2830,c_2154]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_28,plain,
% 3.74/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_20,negated_conjecture,
% 3.74/1.01      ( k2_relset_1(sK3,sK4,sK5) != sK4 ),
% 3.74/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1321,plain,
% 3.74/1.01      ( r2_hidden(sK2(sK4,sK5),sK4)
% 3.74/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.74/1.01      | k2_relset_1(sK3,sK4,sK5) = sK4 ),
% 3.74/1.01      inference(instantiation,[status(thm)],[c_16]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1322,plain,
% 3.74/1.01      ( k2_relset_1(sK3,sK4,sK5) = sK4
% 3.74/1.01      | r2_hidden(sK2(sK4,sK5),sK4) = iProver_top
% 3.74/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_1321]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_3332,plain,
% 3.74/1.01      ( r2_hidden(sK2(sK4,sK5),sK4) = iProver_top ),
% 3.74/1.01      inference(global_propositional_subsumption,
% 3.74/1.01                [status(thm)],
% 3.74/1.01                [c_2833,c_28,c_20,c_1322]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_21,negated_conjecture,
% 3.74/1.01      ( ~ r2_hidden(X0,sK4) | k1_funct_1(sK5,sK6(X0)) = X0 ),
% 3.74/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1098,plain,
% 3.74/1.01      ( k1_funct_1(sK5,sK6(X0)) = X0 | r2_hidden(X0,sK4) != iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_3337,plain,
% 3.74/1.01      ( k1_funct_1(sK5,sK6(sK2(sK4,sK5))) = sK2(sK4,sK5) ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_3332,c_1098]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_19,plain,
% 3.74/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.74/1.01      | ~ r2_hidden(X3,X1)
% 3.74/1.01      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 3.74/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.74/1.01      | ~ v1_funct_1(X0)
% 3.74/1.01      | k1_xboole_0 = X2 ),
% 3.74/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_24,negated_conjecture,
% 3.74/1.01      ( v1_funct_2(sK5,sK3,sK4) ),
% 3.74/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_336,plain,
% 3.74/1.01      ( ~ r2_hidden(X0,X1)
% 3.74/1.01      | r2_hidden(k1_funct_1(X2,X0),k2_relset_1(X1,X3,X2))
% 3.74/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.74/1.01      | ~ v1_funct_1(X2)
% 3.74/1.01      | sK5 != X2
% 3.74/1.01      | sK4 != X3
% 3.74/1.01      | sK3 != X1
% 3.74/1.01      | k1_xboole_0 = X3 ),
% 3.74/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_337,plain,
% 3.74/1.01      ( ~ r2_hidden(X0,sK3)
% 3.74/1.01      | r2_hidden(k1_funct_1(sK5,X0),k2_relset_1(sK3,sK4,sK5))
% 3.74/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.74/1.01      | ~ v1_funct_1(sK5)
% 3.74/1.01      | k1_xboole_0 = sK4 ),
% 3.74/1.01      inference(unflattening,[status(thm)],[c_336]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_25,negated_conjecture,
% 3.74/1.01      ( v1_funct_1(sK5) ),
% 3.74/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_341,plain,
% 3.74/1.01      ( ~ r2_hidden(X0,sK3)
% 3.74/1.01      | r2_hidden(k1_funct_1(sK5,X0),k2_relset_1(sK3,sK4,sK5))
% 3.74/1.01      | k1_xboole_0 = sK4 ),
% 3.74/1.01      inference(global_propositional_subsumption,
% 3.74/1.01                [status(thm)],
% 3.74/1.01                [c_337,c_25,c_23]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1094,plain,
% 3.74/1.01      ( k1_xboole_0 = sK4
% 3.74/1.01      | r2_hidden(X0,sK3) != iProver_top
% 3.74/1.01      | r2_hidden(k1_funct_1(sK5,X0),k2_relset_1(sK3,sK4,sK5)) = iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_341]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_2456,plain,
% 3.74/1.01      ( sK4 = k1_xboole_0
% 3.74/1.01      | r2_hidden(X0,sK3) != iProver_top
% 3.74/1.01      | r2_hidden(k1_funct_1(sK5,X0),k9_relat_1(sK5,sK3)) = iProver_top ),
% 3.74/1.01      inference(demodulation,[status(thm)],[c_2154,c_1094]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_0,plain,
% 3.74/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.74/1.01      inference(cnf_transformation,[],[f41]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1275,plain,
% 3.74/1.01      ( ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),sK4)
% 3.74/1.01      | ~ r1_tarski(sK4,k2_relset_1(sK3,sK4,sK5))
% 3.74/1.01      | k2_relset_1(sK3,sK4,sK5) = sK4 ),
% 3.74/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_12,plain,
% 3.74/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.74/1.01      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 3.74/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1284,plain,
% 3.74/1.01      ( m1_subset_1(k2_relset_1(sK3,sK4,sK5),k1_zfmisc_1(sK4))
% 3.74/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.74/1.01      inference(instantiation,[status(thm)],[c_12]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_5,plain,
% 3.74/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.74/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1359,plain,
% 3.74/1.01      ( ~ m1_subset_1(k2_relset_1(sK3,sK4,sK5),k1_zfmisc_1(sK4))
% 3.74/1.01      | r1_tarski(k2_relset_1(sK3,sK4,sK5),sK4) ),
% 3.74/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_3,plain,
% 3.74/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 3.74/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1508,plain,
% 3.74/1.01      ( r1_tarski(k1_xboole_0,k2_relset_1(sK3,sK4,sK5)) ),
% 3.74/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_563,plain,
% 3.74/1.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 3.74/1.01      theory(equality) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1471,plain,
% 3.74/1.01      ( ~ r1_tarski(X0,k2_relset_1(sK3,sK4,sK5))
% 3.74/1.01      | r1_tarski(sK4,k2_relset_1(sK3,sK4,sK5))
% 3.74/1.01      | sK4 != X0 ),
% 3.74/1.01      inference(instantiation,[status(thm)],[c_563]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1990,plain,
% 3.74/1.01      ( r1_tarski(sK4,k2_relset_1(sK3,sK4,sK5))
% 3.74/1.01      | ~ r1_tarski(k1_xboole_0,k2_relset_1(sK3,sK4,sK5))
% 3.74/1.01      | sK4 != k1_xboole_0 ),
% 3.74/1.01      inference(instantiation,[status(thm)],[c_1471]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_2677,plain,
% 3.74/1.01      ( r2_hidden(X0,sK3) != iProver_top
% 3.74/1.01      | r2_hidden(k1_funct_1(sK5,X0),k9_relat_1(sK5,sK3)) = iProver_top ),
% 3.74/1.01      inference(global_propositional_subsumption,
% 3.74/1.01                [status(thm)],
% 3.74/1.01                [c_2456,c_23,c_20,c_1275,c_1284,c_1359,c_1508,c_1990]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_3466,plain,
% 3.74/1.01      ( r2_hidden(sK2(sK4,sK5),k9_relat_1(sK5,sK3)) = iProver_top
% 3.74/1.01      | r2_hidden(sK6(sK2(sK4,sK5)),sK3) != iProver_top ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_3337,c_2677]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_22,negated_conjecture,
% 3.74/1.01      ( ~ r2_hidden(X0,sK4) | r2_hidden(sK6(X0),sK3) ),
% 3.74/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1377,plain,
% 3.74/1.01      ( ~ r2_hidden(sK2(sK4,sK5),sK4)
% 3.74/1.01      | r2_hidden(sK6(sK2(sK4,sK5)),sK3) ),
% 3.74/1.01      inference(instantiation,[status(thm)],[c_22]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1378,plain,
% 3.74/1.01      ( r2_hidden(sK2(sK4,sK5),sK4) != iProver_top
% 3.74/1.01      | r2_hidden(sK6(sK2(sK4,sK5)),sK3) = iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_1377]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_3469,plain,
% 3.74/1.01      ( r2_hidden(sK2(sK4,sK5),k9_relat_1(sK5,sK3)) = iProver_top ),
% 3.74/1.01      inference(global_propositional_subsumption,
% 3.74/1.01                [status(thm)],
% 3.74/1.01                [c_3466,c_28,c_20,c_1322,c_1378]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_10,plain,
% 3.74/1.01      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.74/1.01      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
% 3.74/1.01      | ~ v1_relat_1(X1) ),
% 3.74/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1107,plain,
% 3.74/1.01      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.74/1.01      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
% 3.74/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_15,plain,
% 3.74/1.01      ( ~ r2_hidden(k4_tarski(X0,sK2(X1,X2)),X2)
% 3.74/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 3.74/1.01      | k2_relset_1(X3,X1,X2) = X1 ),
% 3.74/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1102,plain,
% 3.74/1.01      ( k2_relset_1(X0,X1,X2) = X1
% 3.74/1.01      | r2_hidden(k4_tarski(X3,sK2(X1,X2)),X2) != iProver_top
% 3.74/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_2883,plain,
% 3.74/1.01      ( k2_relset_1(X0,X1,X2) = X1
% 3.74/1.01      | r2_hidden(sK2(X1,X2),k9_relat_1(X2,X3)) != iProver_top
% 3.74/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.74/1.01      | v1_relat_1(X2) != iProver_top ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_1107,c_1102]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_8247,plain,
% 3.74/1.01      ( k2_relset_1(X0,sK4,sK5) = sK4
% 3.74/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) != iProver_top
% 3.74/1.01      | v1_relat_1(sK5) != iProver_top ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_3469,c_2883]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1111,plain,
% 3.74/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.74/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1481,plain,
% 3.74/1.01      ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_1096,c_1111]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_6,plain,
% 3.74/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.74/1.01      | ~ v1_relat_1(X1)
% 3.74/1.01      | v1_relat_1(X0) ),
% 3.74/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_4,plain,
% 3.74/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.74/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_200,plain,
% 3.74/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.74/1.01      inference(prop_impl,[status(thm)],[c_4]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_201,plain,
% 3.74/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.74/1.01      inference(renaming,[status(thm)],[c_200]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_249,plain,
% 3.74/1.01      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.74/1.01      inference(bin_hyper_res,[status(thm)],[c_6,c_201]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1349,plain,
% 3.74/1.01      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 3.74/1.01      | v1_relat_1(X0)
% 3.74/1.01      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.74/1.01      inference(instantiation,[status(thm)],[c_249]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1744,plain,
% 3.74/1.01      ( ~ r1_tarski(sK5,k2_zfmisc_1(sK3,sK4))
% 3.74/1.01      | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
% 3.74/1.01      | v1_relat_1(sK5) ),
% 3.74/1.01      inference(instantiation,[status(thm)],[c_1349]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1746,plain,
% 3.74/1.01      ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK4)) != iProver_top
% 3.74/1.01      | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
% 3.74/1.01      | v1_relat_1(sK5) = iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_1744]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_7,plain,
% 3.74/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.74/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1908,plain,
% 3.74/1.01      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
% 3.74/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1909,plain,
% 3.74/1.01      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_1908]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_9102,plain,
% 3.74/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) != iProver_top
% 3.74/1.01      | k2_relset_1(X0,sK4,sK5) = sK4 ),
% 3.74/1.01      inference(global_propositional_subsumption,
% 3.74/1.01                [status(thm)],
% 3.74/1.01                [c_8247,c_1481,c_1746,c_1909]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_9103,plain,
% 3.74/1.01      ( k2_relset_1(X0,sK4,sK5) = sK4
% 3.74/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK4))) != iProver_top ),
% 3.74/1.01      inference(renaming,[status(thm)],[c_9102]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_9111,plain,
% 3.74/1.01      ( k2_relset_1(sK3,sK4,sK5) = sK4 ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_1096,c_9103]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(contradiction,plain,
% 3.74/1.01      ( $false ),
% 3.74/1.01      inference(minisat,[status(thm)],[c_9111,c_20]) ).
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.74/1.01  
% 3.74/1.01  ------                               Statistics
% 3.74/1.01  
% 3.74/1.01  ------ General
% 3.74/1.01  
% 3.74/1.01  abstr_ref_over_cycles:                  0
% 3.74/1.01  abstr_ref_under_cycles:                 0
% 3.74/1.01  gc_basic_clause_elim:                   0
% 3.74/1.01  forced_gc_time:                         0
% 3.74/1.01  parsing_time:                           0.013
% 3.74/1.01  unif_index_cands_time:                  0.
% 3.74/1.01  unif_index_add_time:                    0.
% 3.74/1.01  orderings_time:                         0.
% 3.74/1.01  out_proof_time:                         0.013
% 3.74/1.01  total_time:                             0.472
% 3.74/1.01  num_of_symbols:                         55
% 3.74/1.01  num_of_terms:                           14353
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing
% 3.74/1.01  
% 3.74/1.01  num_of_splits:                          0
% 3.74/1.01  num_of_split_atoms:                     0
% 3.74/1.01  num_of_reused_defs:                     0
% 3.74/1.01  num_eq_ax_congr_red:                    69
% 3.74/1.01  num_of_sem_filtered_clauses:            1
% 3.74/1.01  num_of_subtypes:                        0
% 3.74/1.01  monotx_restored_types:                  0
% 3.74/1.01  sat_num_of_epr_types:                   0
% 3.74/1.01  sat_num_of_non_cyclic_types:            0
% 3.74/1.01  sat_guarded_non_collapsed_types:        0
% 3.74/1.01  num_pure_diseq_elim:                    0
% 3.74/1.01  simp_replaced_by:                       0
% 3.74/1.01  res_preprocessed:                       117
% 3.74/1.01  prep_upred:                             0
% 3.74/1.01  prep_unflattend:                        3
% 3.74/1.01  smt_new_axioms:                         0
% 3.74/1.01  pred_elim_cands:                        4
% 3.74/1.01  pred_elim:                              2
% 3.74/1.01  pred_elim_cl:                           2
% 3.74/1.01  pred_elim_cycles:                       4
% 3.74/1.01  merged_defs:                            8
% 3.74/1.01  merged_defs_ncl:                        0
% 3.74/1.01  bin_hyper_res:                          9
% 3.74/1.01  prep_cycles:                            4
% 3.74/1.01  pred_elim_time:                         0.002
% 3.74/1.01  splitting_time:                         0.
% 3.74/1.01  sem_filter_time:                        0.
% 3.74/1.01  monotx_time:                            0.
% 3.74/1.01  subtype_inf_time:                       0.
% 3.74/1.01  
% 3.74/1.01  ------ Problem properties
% 3.74/1.01  
% 3.74/1.01  clauses:                                23
% 3.74/1.01  conjectures:                            4
% 3.74/1.01  epr:                                    4
% 3.74/1.01  horn:                                   21
% 3.74/1.01  ground:                                 2
% 3.74/1.01  unary:                                  5
% 3.74/1.01  binary:                                 8
% 3.74/1.01  lits:                                   54
% 3.74/1.01  lits_eq:                                10
% 3.74/1.01  fd_pure:                                0
% 3.74/1.01  fd_pseudo:                              0
% 3.74/1.01  fd_cond:                                0
% 3.74/1.01  fd_pseudo_cond:                         1
% 3.74/1.01  ac_symbols:                             0
% 3.74/1.01  
% 3.74/1.01  ------ Propositional Solver
% 3.74/1.01  
% 3.74/1.01  prop_solver_calls:                      29
% 3.74/1.01  prop_fast_solver_calls:                 921
% 3.74/1.01  smt_solver_calls:                       0
% 3.74/1.01  smt_fast_solver_calls:                  0
% 3.74/1.01  prop_num_of_clauses:                    3381
% 3.74/1.01  prop_preprocess_simplified:             6922
% 3.74/1.01  prop_fo_subsumed:                       13
% 3.74/1.01  prop_solver_time:                       0.
% 3.74/1.01  smt_solver_time:                        0.
% 3.74/1.01  smt_fast_solver_time:                   0.
% 3.74/1.01  prop_fast_solver_time:                  0.
% 3.74/1.01  prop_unsat_core_time:                   0.
% 3.74/1.01  
% 3.74/1.01  ------ QBF
% 3.74/1.01  
% 3.74/1.01  qbf_q_res:                              0
% 3.74/1.01  qbf_num_tautologies:                    0
% 3.74/1.01  qbf_prep_cycles:                        0
% 3.74/1.01  
% 3.74/1.01  ------ BMC1
% 3.74/1.01  
% 3.74/1.01  bmc1_current_bound:                     -1
% 3.74/1.01  bmc1_last_solved_bound:                 -1
% 3.74/1.01  bmc1_unsat_core_size:                   -1
% 3.74/1.01  bmc1_unsat_core_parents_size:           -1
% 3.74/1.01  bmc1_merge_next_fun:                    0
% 3.74/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.74/1.01  
% 3.74/1.01  ------ Instantiation
% 3.74/1.01  
% 3.74/1.01  inst_num_of_clauses:                    837
% 3.74/1.01  inst_num_in_passive:                    114
% 3.74/1.01  inst_num_in_active:                     489
% 3.74/1.01  inst_num_in_unprocessed:                236
% 3.74/1.01  inst_num_of_loops:                      540
% 3.74/1.01  inst_num_of_learning_restarts:          0
% 3.74/1.01  inst_num_moves_active_passive:          47
% 3.74/1.01  inst_lit_activity:                      0
% 3.74/1.01  inst_lit_activity_moves:                0
% 3.74/1.01  inst_num_tautologies:                   0
% 3.74/1.01  inst_num_prop_implied:                  0
% 3.74/1.01  inst_num_existing_simplified:           0
% 3.74/1.01  inst_num_eq_res_simplified:             0
% 3.74/1.01  inst_num_child_elim:                    0
% 3.74/1.01  inst_num_of_dismatching_blockings:      431
% 3.74/1.01  inst_num_of_non_proper_insts:           1153
% 3.74/1.01  inst_num_of_duplicates:                 0
% 3.74/1.01  inst_inst_num_from_inst_to_res:         0
% 3.74/1.01  inst_dismatching_checking_time:         0.
% 3.74/1.01  
% 3.74/1.01  ------ Resolution
% 3.74/1.01  
% 3.74/1.01  res_num_of_clauses:                     0
% 3.74/1.01  res_num_in_passive:                     0
% 3.74/1.01  res_num_in_active:                      0
% 3.74/1.01  res_num_of_loops:                       121
% 3.74/1.01  res_forward_subset_subsumed:            96
% 3.74/1.01  res_backward_subset_subsumed:           4
% 3.74/1.01  res_forward_subsumed:                   0
% 3.74/1.01  res_backward_subsumed:                  0
% 3.74/1.01  res_forward_subsumption_resolution:     0
% 3.74/1.01  res_backward_subsumption_resolution:    0
% 3.74/1.01  res_clause_to_clause_subsumption:       704
% 3.74/1.01  res_orphan_elimination:                 0
% 3.74/1.01  res_tautology_del:                      71
% 3.74/1.01  res_num_eq_res_simplified:              0
% 3.74/1.01  res_num_sel_changes:                    0
% 3.74/1.01  res_moves_from_active_to_pass:          0
% 3.74/1.01  
% 3.74/1.01  ------ Superposition
% 3.74/1.01  
% 3.74/1.01  sup_time_total:                         0.
% 3.74/1.01  sup_time_generating:                    0.
% 3.74/1.01  sup_time_sim_full:                      0.
% 3.74/1.01  sup_time_sim_immed:                     0.
% 3.74/1.01  
% 3.74/1.01  sup_num_of_clauses:                     241
% 3.74/1.01  sup_num_in_active:                      105
% 3.74/1.01  sup_num_in_passive:                     136
% 3.74/1.01  sup_num_of_loops:                       107
% 3.74/1.01  sup_fw_superposition:                   121
% 3.74/1.01  sup_bw_superposition:                   134
% 3.74/1.01  sup_immediate_simplified:               23
% 3.74/1.01  sup_given_eliminated:                   0
% 3.74/1.01  comparisons_done:                       0
% 3.74/1.01  comparisons_avoided:                    48
% 3.74/1.01  
% 3.74/1.01  ------ Simplifications
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  sim_fw_subset_subsumed:                 10
% 3.74/1.01  sim_bw_subset_subsumed:                 1
% 3.74/1.01  sim_fw_subsumed:                        8
% 3.74/1.01  sim_bw_subsumed:                        0
% 3.74/1.01  sim_fw_subsumption_res:                 1
% 3.74/1.01  sim_bw_subsumption_res:                 0
% 3.74/1.01  sim_tautology_del:                      2
% 3.74/1.01  sim_eq_tautology_del:                   2
% 3.74/1.01  sim_eq_res_simp:                        0
% 3.74/1.01  sim_fw_demodulated:                     4
% 3.74/1.01  sim_bw_demodulated:                     2
% 3.74/1.01  sim_light_normalised:                   1
% 3.74/1.01  sim_joinable_taut:                      0
% 3.74/1.01  sim_joinable_simp:                      0
% 3.74/1.01  sim_ac_normalised:                      0
% 3.74/1.01  sim_smt_subsumption:                    0
% 3.74/1.01  
%------------------------------------------------------------------------------
