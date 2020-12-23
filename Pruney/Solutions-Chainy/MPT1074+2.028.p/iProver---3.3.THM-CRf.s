%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:17 EST 2020

% Result     : Theorem 7.81s
% Output     : CNFRefutation 7.81s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 334 expanded)
%              Number of clauses        :   64 (  96 expanded)
%              Number of leaves         :   14 (  98 expanded)
%              Depth                    :   14
%              Number of atoms          :  375 (2021 expanded)
%              Number of equality atoms :   90 ( 116 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(X3,X1,X2)
                & v1_funct_1(X3) )
             => ( ! [X4] :
                    ( m1_subset_1(X4,X1)
                   => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
               => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_2(X3,X1,X2)
                  & v1_funct_1(X3) )
               => ( ! [X4] :
                      ( m1_subset_1(X4,X1)
                     => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
                 => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f15])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
          & ! [X4] :
              ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
              | ~ m1_subset_1(X4,X1) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
     => ( ~ r1_tarski(k2_relset_1(X1,X2,sK5),X0)
        & ! [X4] :
            ( r2_hidden(k3_funct_2(X1,X2,sK5,X4),X0)
            | ~ m1_subset_1(X4,X1) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK5,X1,X2)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
     => ( ? [X3] :
            ( ~ r1_tarski(k2_relset_1(X1,sK4,X3),X0)
            & ! [X4] :
                ( r2_hidden(k3_funct_2(X1,sK4,X3,X4),X0)
                | ~ m1_subset_1(X4,X1) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK4)))
            & v1_funct_2(X3,X1,sK4)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
                & ! [X4] :
                    ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                    | ~ m1_subset_1(X4,X1) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(X3,X1,X2)
                & v1_funct_1(X3) )
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(sK3,X2,X3),sK2)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(sK3,X2,X3,X4),sK2)
                  | ~ m1_subset_1(X4,sK3) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,X2)))
              & v1_funct_2(X3,sK3,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),sK2)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK3,sK4,sK5,X4),sK2)
        | ~ m1_subset_1(X4,sK3) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5)
    & ~ v1_xboole_0(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f16,f26,f25,f24])).

fof(f40,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK3,sK4,sK5,X4),sK2)
      | ~ m1_subset_1(X4,sK3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ~ ( k1_funct_1(X3,X4) = X2
                & r2_hidden(X4,X0) )
          & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k1_funct_1(X3,X4) = X2
          & r2_hidden(X4,X0) )
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k1_funct_1(X3,X4) = X2
          & r2_hidden(X4,X0) )
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f13])).

fof(f22,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X3,X4) = X2
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X3,sK1(X0,X2,X3)) = X2
        & r2_hidden(sK1(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_funct_1(X3,sK1(X0,X2,X3)) = X2
        & r2_hidden(sK1(X0,X2,X3),X0) )
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f22])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X3,sK1(X0,X2,X3)) = X2
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK1(X0,X2,X3),X0)
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_690,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1457,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5)),sK2)
    | X0 != k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5))
    | X1 != sK2 ),
    inference(instantiation,[status(thm)],[c_690])).

cnf(c_1648,plain,
    ( r2_hidden(X0,sK2)
    | ~ r2_hidden(k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5)),sK2)
    | X0 != k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1457])).

cnf(c_23106,plain,
    ( ~ r2_hidden(k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5)),sK2)
    | r2_hidden(sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK2)
    | sK0(k2_relset_1(sK3,sK4,sK5),sK2) != k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1648])).

cnf(c_688,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2345,plain,
    ( X0 != X1
    | X0 = k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5))
    | k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5)) != X1 ),
    inference(instantiation,[status(thm)],[c_688])).

cnf(c_3894,plain,
    ( X0 = k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5))
    | X0 != k1_funct_1(sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5))
    | k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5)) != k1_funct_1(sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5)) ),
    inference(instantiation,[status(thm)],[c_2345])).

cnf(c_14363,plain,
    ( k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5)) != k1_funct_1(sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5))
    | sK0(k2_relset_1(sK3,sK4,sK5),sK2) = k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5))
    | sK0(k2_relset_1(sK3,sK4,sK5),sK2) != k1_funct_1(sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5)) ),
    inference(instantiation,[status(thm)],[c_3894])).

cnf(c_1997,plain,
    ( X0 != X1
    | sK0(k2_relset_1(sK3,sK4,sK5),sK2) != X1
    | sK0(k2_relset_1(sK3,sK4,sK5),sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_688])).

cnf(c_4300,plain,
    ( X0 != sK0(k2_relset_1(sK3,sK4,sK5),sK2)
    | sK0(k2_relset_1(sK3,sK4,sK5),sK2) = X0
    | sK0(k2_relset_1(sK3,sK4,sK5),sK2) != sK0(k2_relset_1(sK3,sK4,sK5),sK2) ),
    inference(instantiation,[status(thm)],[c_1997])).

cnf(c_9954,plain,
    ( k1_funct_1(sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5)) != sK0(k2_relset_1(sK3,sK4,sK5),sK2)
    | sK0(k2_relset_1(sK3,sK4,sK5),sK2) = k1_funct_1(sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5))
    | sK0(k2_relset_1(sK3,sK4,sK5),sK2) != sK0(k2_relset_1(sK3,sK4,sK5),sK2) ),
    inference(instantiation,[status(thm)],[c_4300])).

cnf(c_687,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1855,plain,
    ( sK0(k2_relset_1(sK3,sK4,sK5),sK2) = sK0(k2_relset_1(sK3,sK4,sK5),sK2) ),
    inference(instantiation,[status(thm)],[c_687])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1075,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1076,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1574,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1075,c_1076])).

cnf(c_1575,plain,
    ( r1_tarski(X0,X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1574])).

cnf(c_1577,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_1575])).

cnf(c_1576,plain,
    ( r1_tarski(sK3,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1574])).

cnf(c_12,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_15,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_237,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_15])).

cnf(c_238,plain,
    ( ~ v1_funct_2(X0,sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
    | ~ m1_subset_1(X2,sK3)
    | ~ v1_funct_1(X0)
    | k3_funct_2(sK3,X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(unflattening,[status(thm)],[c_237])).

cnf(c_330,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
    | ~ m1_subset_1(X2,sK3)
    | ~ v1_funct_1(X0)
    | k3_funct_2(sK3,X1,X0,X2) = k1_funct_1(X0,X2)
    | sK5 != X0
    | sK4 != X1
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_238])).

cnf(c_331,plain,
    ( ~ m1_subset_1(X0,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK5)
    | k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0) ),
    inference(unflattening,[status(thm)],[c_330])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_335,plain,
    ( ~ m1_subset_1(X0,sK3)
    | k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_331,c_13,c_11])).

cnf(c_1363,plain,
    ( ~ m1_subset_1(sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5),sK3)
    | k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5)) = k1_funct_1(sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5)) ),
    inference(instantiation,[status(thm)],[c_335])).

cnf(c_1369,plain,
    ( k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5)) = k1_funct_1(sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5))
    | m1_subset_1(sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1363])).

cnf(c_10,negated_conjecture,
    ( ~ m1_subset_1(X0,sK3)
    | r2_hidden(k3_funct_2(sK3,sK4,sK5,X0),sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1364,plain,
    ( ~ m1_subset_1(sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5),sK3)
    | r2_hidden(k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5)),sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1256,plain,
    ( m1_subset_1(sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5),X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ r2_hidden(sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5),sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1257,plain,
    ( m1_subset_1(sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5),X0) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | r2_hidden(sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1256])).

cnf(c_1259,plain,
    ( m1_subset_1(sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5),sK3) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK3)) != iProver_top
    | r2_hidden(sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5),sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1257])).

cnf(c_1258,plain,
    ( m1_subset_1(sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK3))
    | ~ r2_hidden(sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5),sK3) ),
    inference(instantiation,[status(thm)],[c_1256])).

cnf(c_1222,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_687])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK1(X1,X3,X0)) = X3 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_288,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK1(X1,X3,X0)) = X3
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_12])).

cnf(c_289,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ r2_hidden(X0,k2_relset_1(sK3,sK4,sK5))
    | ~ v1_funct_1(sK5)
    | k1_funct_1(sK5,sK1(sK3,X0,sK5)) = X0 ),
    inference(unflattening,[status(thm)],[c_288])).

cnf(c_293,plain,
    ( ~ r2_hidden(X0,k2_relset_1(sK3,sK4,sK5))
    | k1_funct_1(sK5,sK1(sK3,X0,sK5)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_289,c_13,c_11])).

cnf(c_1215,plain,
    ( ~ r2_hidden(sK0(k2_relset_1(sK3,sK4,sK5),sK2),k2_relset_1(sK3,sK4,sK5))
    | k1_funct_1(sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5)) = sK0(k2_relset_1(sK3,sK4,sK5),sK2) ),
    inference(instantiation,[status(thm)],[c_293])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k2_relset_1(X1,X2,X0))
    | r2_hidden(sK1(X1,X3,X0),X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_270,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k2_relset_1(X1,X2,X0))
    | r2_hidden(sK1(X1,X3,X0),X1)
    | ~ v1_funct_1(X0)
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_12])).

cnf(c_271,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ r2_hidden(X0,k2_relset_1(sK3,sK4,sK5))
    | r2_hidden(sK1(sK3,X0,sK5),sK3)
    | ~ v1_funct_1(sK5) ),
    inference(unflattening,[status(thm)],[c_270])).

cnf(c_275,plain,
    ( r2_hidden(sK1(sK3,X0,sK5),sK3)
    | ~ r2_hidden(X0,k2_relset_1(sK3,sK4,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_271,c_13,c_11])).

cnf(c_276,plain,
    ( ~ r2_hidden(X0,k2_relset_1(sK3,sK4,sK5))
    | r2_hidden(sK1(sK3,X0,sK5),sK3) ),
    inference(renaming,[status(thm)],[c_275])).

cnf(c_1216,plain,
    ( r2_hidden(sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5),sK3)
    | ~ r2_hidden(sK0(k2_relset_1(sK3,sK4,sK5),sK2),k2_relset_1(sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_276])).

cnf(c_1217,plain,
    ( r2_hidden(sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5),sK3) = iProver_top
    | r2_hidden(sK0(k2_relset_1(sK3,sK4,sK5),sK2),k2_relset_1(sK3,sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1216])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_438,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | k2_relset_1(sK3,sK4,sK5) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_9])).

cnf(c_439,plain,
    ( ~ r2_hidden(sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK2) ),
    inference(unflattening,[status(thm)],[c_438])).

cnf(c_431,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k2_relset_1(sK3,sK4,sK5) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_9])).

cnf(c_432,plain,
    ( r2_hidden(sK0(k2_relset_1(sK3,sK4,sK5),sK2),k2_relset_1(sK3,sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_433,plain,
    ( r2_hidden(sK0(k2_relset_1(sK3,sK4,sK5),sK2),k2_relset_1(sK3,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_432])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_40,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_42,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK3)) = iProver_top
    | r1_tarski(sK3,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_41,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK3))
    | ~ r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23106,c_14363,c_9954,c_1855,c_1577,c_1576,c_1369,c_1364,c_1259,c_1258,c_1222,c_1215,c_1217,c_1216,c_439,c_433,c_432,c_42,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:50:04 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.81/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.81/1.49  
% 7.81/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.81/1.49  
% 7.81/1.49  ------  iProver source info
% 7.81/1.49  
% 7.81/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.81/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.81/1.49  git: non_committed_changes: false
% 7.81/1.49  git: last_make_outside_of_git: false
% 7.81/1.49  
% 7.81/1.49  ------ 
% 7.81/1.49  
% 7.81/1.49  ------ Input Options
% 7.81/1.49  
% 7.81/1.49  --out_options                           all
% 7.81/1.49  --tptp_safe_out                         true
% 7.81/1.49  --problem_path                          ""
% 7.81/1.49  --include_path                          ""
% 7.81/1.49  --clausifier                            res/vclausify_rel
% 7.81/1.49  --clausifier_options                    --mode clausify
% 7.81/1.49  --stdin                                 false
% 7.81/1.49  --stats_out                             all
% 7.81/1.49  
% 7.81/1.49  ------ General Options
% 7.81/1.49  
% 7.81/1.49  --fof                                   false
% 7.81/1.49  --time_out_real                         305.
% 7.81/1.49  --time_out_virtual                      -1.
% 7.81/1.49  --symbol_type_check                     false
% 7.81/1.49  --clausify_out                          false
% 7.81/1.49  --sig_cnt_out                           false
% 7.81/1.49  --trig_cnt_out                          false
% 7.81/1.49  --trig_cnt_out_tolerance                1.
% 7.81/1.49  --trig_cnt_out_sk_spl                   false
% 7.81/1.49  --abstr_cl_out                          false
% 7.81/1.49  
% 7.81/1.49  ------ Global Options
% 7.81/1.49  
% 7.81/1.49  --schedule                              default
% 7.81/1.49  --add_important_lit                     false
% 7.81/1.49  --prop_solver_per_cl                    1000
% 7.81/1.49  --min_unsat_core                        false
% 7.81/1.49  --soft_assumptions                      false
% 7.81/1.49  --soft_lemma_size                       3
% 7.81/1.49  --prop_impl_unit_size                   0
% 7.81/1.49  --prop_impl_unit                        []
% 7.81/1.49  --share_sel_clauses                     true
% 7.81/1.49  --reset_solvers                         false
% 7.81/1.49  --bc_imp_inh                            [conj_cone]
% 7.81/1.49  --conj_cone_tolerance                   3.
% 7.81/1.49  --extra_neg_conj                        none
% 7.81/1.49  --large_theory_mode                     true
% 7.81/1.49  --prolific_symb_bound                   200
% 7.81/1.49  --lt_threshold                          2000
% 7.81/1.49  --clause_weak_htbl                      true
% 7.81/1.49  --gc_record_bc_elim                     false
% 7.81/1.49  
% 7.81/1.49  ------ Preprocessing Options
% 7.81/1.49  
% 7.81/1.49  --preprocessing_flag                    true
% 7.81/1.49  --time_out_prep_mult                    0.1
% 7.81/1.49  --splitting_mode                        input
% 7.81/1.49  --splitting_grd                         true
% 7.81/1.49  --splitting_cvd                         false
% 7.81/1.49  --splitting_cvd_svl                     false
% 7.81/1.49  --splitting_nvd                         32
% 7.81/1.49  --sub_typing                            true
% 7.81/1.49  --prep_gs_sim                           true
% 7.81/1.49  --prep_unflatten                        true
% 7.81/1.49  --prep_res_sim                          true
% 7.81/1.49  --prep_upred                            true
% 7.81/1.49  --prep_sem_filter                       exhaustive
% 7.81/1.49  --prep_sem_filter_out                   false
% 7.81/1.49  --pred_elim                             true
% 7.81/1.49  --res_sim_input                         true
% 7.81/1.49  --eq_ax_congr_red                       true
% 7.81/1.49  --pure_diseq_elim                       true
% 7.81/1.49  --brand_transform                       false
% 7.81/1.49  --non_eq_to_eq                          false
% 7.81/1.49  --prep_def_merge                        true
% 7.81/1.49  --prep_def_merge_prop_impl              false
% 7.81/1.49  --prep_def_merge_mbd                    true
% 7.81/1.49  --prep_def_merge_tr_red                 false
% 7.81/1.49  --prep_def_merge_tr_cl                  false
% 7.81/1.49  --smt_preprocessing                     true
% 7.81/1.49  --smt_ac_axioms                         fast
% 7.81/1.49  --preprocessed_out                      false
% 7.81/1.49  --preprocessed_stats                    false
% 7.81/1.49  
% 7.81/1.49  ------ Abstraction refinement Options
% 7.81/1.49  
% 7.81/1.49  --abstr_ref                             []
% 7.81/1.49  --abstr_ref_prep                        false
% 7.81/1.49  --abstr_ref_until_sat                   false
% 7.81/1.49  --abstr_ref_sig_restrict                funpre
% 7.81/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.81/1.49  --abstr_ref_under                       []
% 7.81/1.49  
% 7.81/1.49  ------ SAT Options
% 7.81/1.49  
% 7.81/1.49  --sat_mode                              false
% 7.81/1.49  --sat_fm_restart_options                ""
% 7.81/1.49  --sat_gr_def                            false
% 7.81/1.49  --sat_epr_types                         true
% 7.81/1.49  --sat_non_cyclic_types                  false
% 7.81/1.49  --sat_finite_models                     false
% 7.81/1.49  --sat_fm_lemmas                         false
% 7.81/1.49  --sat_fm_prep                           false
% 7.81/1.49  --sat_fm_uc_incr                        true
% 7.81/1.49  --sat_out_model                         small
% 7.81/1.49  --sat_out_clauses                       false
% 7.81/1.49  
% 7.81/1.49  ------ QBF Options
% 7.81/1.49  
% 7.81/1.49  --qbf_mode                              false
% 7.81/1.49  --qbf_elim_univ                         false
% 7.81/1.49  --qbf_dom_inst                          none
% 7.81/1.49  --qbf_dom_pre_inst                      false
% 7.81/1.49  --qbf_sk_in                             false
% 7.81/1.49  --qbf_pred_elim                         true
% 7.81/1.49  --qbf_split                             512
% 7.81/1.49  
% 7.81/1.49  ------ BMC1 Options
% 7.81/1.49  
% 7.81/1.49  --bmc1_incremental                      false
% 7.81/1.49  --bmc1_axioms                           reachable_all
% 7.81/1.49  --bmc1_min_bound                        0
% 7.81/1.49  --bmc1_max_bound                        -1
% 7.81/1.49  --bmc1_max_bound_default                -1
% 7.81/1.49  --bmc1_symbol_reachability              true
% 7.81/1.49  --bmc1_property_lemmas                  false
% 7.81/1.49  --bmc1_k_induction                      false
% 7.81/1.49  --bmc1_non_equiv_states                 false
% 7.81/1.49  --bmc1_deadlock                         false
% 7.81/1.49  --bmc1_ucm                              false
% 7.81/1.49  --bmc1_add_unsat_core                   none
% 7.81/1.49  --bmc1_unsat_core_children              false
% 7.81/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.81/1.49  --bmc1_out_stat                         full
% 7.81/1.49  --bmc1_ground_init                      false
% 7.81/1.49  --bmc1_pre_inst_next_state              false
% 7.81/1.49  --bmc1_pre_inst_state                   false
% 7.81/1.49  --bmc1_pre_inst_reach_state             false
% 7.81/1.49  --bmc1_out_unsat_core                   false
% 7.81/1.49  --bmc1_aig_witness_out                  false
% 7.81/1.49  --bmc1_verbose                          false
% 7.81/1.49  --bmc1_dump_clauses_tptp                false
% 7.81/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.81/1.49  --bmc1_dump_file                        -
% 7.81/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.81/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.81/1.49  --bmc1_ucm_extend_mode                  1
% 7.81/1.49  --bmc1_ucm_init_mode                    2
% 7.81/1.49  --bmc1_ucm_cone_mode                    none
% 7.81/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.81/1.49  --bmc1_ucm_relax_model                  4
% 7.81/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.81/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.81/1.49  --bmc1_ucm_layered_model                none
% 7.81/1.49  --bmc1_ucm_max_lemma_size               10
% 7.81/1.49  
% 7.81/1.49  ------ AIG Options
% 7.81/1.49  
% 7.81/1.49  --aig_mode                              false
% 7.81/1.49  
% 7.81/1.49  ------ Instantiation Options
% 7.81/1.49  
% 7.81/1.49  --instantiation_flag                    true
% 7.81/1.49  --inst_sos_flag                         false
% 7.81/1.49  --inst_sos_phase                        true
% 7.81/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.81/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.81/1.49  --inst_lit_sel_side                     num_symb
% 7.81/1.49  --inst_solver_per_active                1400
% 7.81/1.49  --inst_solver_calls_frac                1.
% 7.81/1.49  --inst_passive_queue_type               priority_queues
% 7.81/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.81/1.49  --inst_passive_queues_freq              [25;2]
% 7.81/1.49  --inst_dismatching                      true
% 7.81/1.49  --inst_eager_unprocessed_to_passive     true
% 7.81/1.49  --inst_prop_sim_given                   true
% 7.81/1.49  --inst_prop_sim_new                     false
% 7.81/1.49  --inst_subs_new                         false
% 7.81/1.49  --inst_eq_res_simp                      false
% 7.81/1.49  --inst_subs_given                       false
% 7.81/1.49  --inst_orphan_elimination               true
% 7.81/1.49  --inst_learning_loop_flag               true
% 7.81/1.49  --inst_learning_start                   3000
% 7.81/1.49  --inst_learning_factor                  2
% 7.81/1.49  --inst_start_prop_sim_after_learn       3
% 7.81/1.49  --inst_sel_renew                        solver
% 7.81/1.49  --inst_lit_activity_flag                true
% 7.81/1.49  --inst_restr_to_given                   false
% 7.81/1.49  --inst_activity_threshold               500
% 7.81/1.49  --inst_out_proof                        true
% 7.81/1.49  
% 7.81/1.49  ------ Resolution Options
% 7.81/1.49  
% 7.81/1.49  --resolution_flag                       true
% 7.81/1.49  --res_lit_sel                           adaptive
% 7.81/1.49  --res_lit_sel_side                      none
% 7.81/1.49  --res_ordering                          kbo
% 7.81/1.49  --res_to_prop_solver                    active
% 7.81/1.49  --res_prop_simpl_new                    false
% 7.81/1.49  --res_prop_simpl_given                  true
% 7.81/1.49  --res_passive_queue_type                priority_queues
% 7.81/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.81/1.49  --res_passive_queues_freq               [15;5]
% 7.81/1.49  --res_forward_subs                      full
% 7.81/1.49  --res_backward_subs                     full
% 7.81/1.49  --res_forward_subs_resolution           true
% 7.81/1.49  --res_backward_subs_resolution          true
% 7.81/1.49  --res_orphan_elimination                true
% 7.81/1.49  --res_time_limit                        2.
% 7.81/1.49  --res_out_proof                         true
% 7.81/1.49  
% 7.81/1.49  ------ Superposition Options
% 7.81/1.49  
% 7.81/1.49  --superposition_flag                    true
% 7.81/1.49  --sup_passive_queue_type                priority_queues
% 7.81/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.81/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.81/1.49  --demod_completeness_check              fast
% 7.81/1.49  --demod_use_ground                      true
% 7.81/1.49  --sup_to_prop_solver                    passive
% 7.81/1.49  --sup_prop_simpl_new                    true
% 7.81/1.49  --sup_prop_simpl_given                  true
% 7.81/1.49  --sup_fun_splitting                     false
% 7.81/1.49  --sup_smt_interval                      50000
% 7.81/1.49  
% 7.81/1.49  ------ Superposition Simplification Setup
% 7.81/1.49  
% 7.81/1.49  --sup_indices_passive                   []
% 7.81/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.81/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.49  --sup_full_bw                           [BwDemod]
% 7.81/1.49  --sup_immed_triv                        [TrivRules]
% 7.81/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.81/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.49  --sup_immed_bw_main                     []
% 7.81/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.81/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.81/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.81/1.49  
% 7.81/1.49  ------ Combination Options
% 7.81/1.49  
% 7.81/1.49  --comb_res_mult                         3
% 7.81/1.49  --comb_sup_mult                         2
% 7.81/1.49  --comb_inst_mult                        10
% 7.81/1.49  
% 7.81/1.49  ------ Debug Options
% 7.81/1.49  
% 7.81/1.49  --dbg_backtrace                         false
% 7.81/1.49  --dbg_dump_prop_clauses                 false
% 7.81/1.49  --dbg_dump_prop_clauses_file            -
% 7.81/1.49  --dbg_out_stat                          false
% 7.81/1.49  ------ Parsing...
% 7.81/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.81/1.49  
% 7.81/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.81/1.49  
% 7.81/1.49  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.81/1.49  
% 7.81/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.81/1.49  ------ Proving...
% 7.81/1.49  ------ Problem Properties 
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  clauses                                 14
% 7.81/1.49  conjectures                             3
% 7.81/1.49  EPR                                     1
% 7.81/1.49  Horn                                    13
% 7.81/1.49  unary                                   2
% 7.81/1.49  binary                                  8
% 7.81/1.49  lits                                    30
% 7.81/1.49  lits eq                                 4
% 7.81/1.49  fd_pure                                 0
% 7.81/1.49  fd_pseudo                               0
% 7.81/1.49  fd_cond                                 0
% 7.81/1.49  fd_pseudo_cond                          0
% 7.81/1.49  AC symbols                              0
% 7.81/1.49  
% 7.81/1.49  ------ Schedule dynamic 5 is on 
% 7.81/1.49  
% 7.81/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  ------ 
% 7.81/1.49  Current options:
% 7.81/1.49  ------ 
% 7.81/1.49  
% 7.81/1.49  ------ Input Options
% 7.81/1.49  
% 7.81/1.49  --out_options                           all
% 7.81/1.49  --tptp_safe_out                         true
% 7.81/1.49  --problem_path                          ""
% 7.81/1.49  --include_path                          ""
% 7.81/1.49  --clausifier                            res/vclausify_rel
% 7.81/1.49  --clausifier_options                    --mode clausify
% 7.81/1.49  --stdin                                 false
% 7.81/1.49  --stats_out                             all
% 7.81/1.49  
% 7.81/1.49  ------ General Options
% 7.81/1.49  
% 7.81/1.49  --fof                                   false
% 7.81/1.49  --time_out_real                         305.
% 7.81/1.49  --time_out_virtual                      -1.
% 7.81/1.49  --symbol_type_check                     false
% 7.81/1.49  --clausify_out                          false
% 7.81/1.49  --sig_cnt_out                           false
% 7.81/1.49  --trig_cnt_out                          false
% 7.81/1.49  --trig_cnt_out_tolerance                1.
% 7.81/1.49  --trig_cnt_out_sk_spl                   false
% 7.81/1.49  --abstr_cl_out                          false
% 7.81/1.49  
% 7.81/1.49  ------ Global Options
% 7.81/1.49  
% 7.81/1.49  --schedule                              default
% 7.81/1.49  --add_important_lit                     false
% 7.81/1.49  --prop_solver_per_cl                    1000
% 7.81/1.49  --min_unsat_core                        false
% 7.81/1.49  --soft_assumptions                      false
% 7.81/1.49  --soft_lemma_size                       3
% 7.81/1.49  --prop_impl_unit_size                   0
% 7.81/1.49  --prop_impl_unit                        []
% 7.81/1.49  --share_sel_clauses                     true
% 7.81/1.49  --reset_solvers                         false
% 7.81/1.49  --bc_imp_inh                            [conj_cone]
% 7.81/1.49  --conj_cone_tolerance                   3.
% 7.81/1.49  --extra_neg_conj                        none
% 7.81/1.49  --large_theory_mode                     true
% 7.81/1.49  --prolific_symb_bound                   200
% 7.81/1.49  --lt_threshold                          2000
% 7.81/1.49  --clause_weak_htbl                      true
% 7.81/1.49  --gc_record_bc_elim                     false
% 7.81/1.49  
% 7.81/1.49  ------ Preprocessing Options
% 7.81/1.49  
% 7.81/1.49  --preprocessing_flag                    true
% 7.81/1.49  --time_out_prep_mult                    0.1
% 7.81/1.49  --splitting_mode                        input
% 7.81/1.49  --splitting_grd                         true
% 7.81/1.49  --splitting_cvd                         false
% 7.81/1.49  --splitting_cvd_svl                     false
% 7.81/1.49  --splitting_nvd                         32
% 7.81/1.49  --sub_typing                            true
% 7.81/1.49  --prep_gs_sim                           true
% 7.81/1.49  --prep_unflatten                        true
% 7.81/1.49  --prep_res_sim                          true
% 7.81/1.49  --prep_upred                            true
% 7.81/1.49  --prep_sem_filter                       exhaustive
% 7.81/1.49  --prep_sem_filter_out                   false
% 7.81/1.49  --pred_elim                             true
% 7.81/1.49  --res_sim_input                         true
% 7.81/1.49  --eq_ax_congr_red                       true
% 7.81/1.49  --pure_diseq_elim                       true
% 7.81/1.49  --brand_transform                       false
% 7.81/1.49  --non_eq_to_eq                          false
% 7.81/1.49  --prep_def_merge                        true
% 7.81/1.49  --prep_def_merge_prop_impl              false
% 7.81/1.49  --prep_def_merge_mbd                    true
% 7.81/1.49  --prep_def_merge_tr_red                 false
% 7.81/1.49  --prep_def_merge_tr_cl                  false
% 7.81/1.49  --smt_preprocessing                     true
% 7.81/1.49  --smt_ac_axioms                         fast
% 7.81/1.49  --preprocessed_out                      false
% 7.81/1.49  --preprocessed_stats                    false
% 7.81/1.49  
% 7.81/1.49  ------ Abstraction refinement Options
% 7.81/1.49  
% 7.81/1.49  --abstr_ref                             []
% 7.81/1.49  --abstr_ref_prep                        false
% 7.81/1.49  --abstr_ref_until_sat                   false
% 7.81/1.49  --abstr_ref_sig_restrict                funpre
% 7.81/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.81/1.49  --abstr_ref_under                       []
% 7.81/1.49  
% 7.81/1.49  ------ SAT Options
% 7.81/1.49  
% 7.81/1.49  --sat_mode                              false
% 7.81/1.49  --sat_fm_restart_options                ""
% 7.81/1.49  --sat_gr_def                            false
% 7.81/1.49  --sat_epr_types                         true
% 7.81/1.49  --sat_non_cyclic_types                  false
% 7.81/1.49  --sat_finite_models                     false
% 7.81/1.49  --sat_fm_lemmas                         false
% 7.81/1.49  --sat_fm_prep                           false
% 7.81/1.49  --sat_fm_uc_incr                        true
% 7.81/1.49  --sat_out_model                         small
% 7.81/1.49  --sat_out_clauses                       false
% 7.81/1.49  
% 7.81/1.49  ------ QBF Options
% 7.81/1.49  
% 7.81/1.49  --qbf_mode                              false
% 7.81/1.49  --qbf_elim_univ                         false
% 7.81/1.49  --qbf_dom_inst                          none
% 7.81/1.49  --qbf_dom_pre_inst                      false
% 7.81/1.49  --qbf_sk_in                             false
% 7.81/1.49  --qbf_pred_elim                         true
% 7.81/1.49  --qbf_split                             512
% 7.81/1.49  
% 7.81/1.49  ------ BMC1 Options
% 7.81/1.49  
% 7.81/1.49  --bmc1_incremental                      false
% 7.81/1.49  --bmc1_axioms                           reachable_all
% 7.81/1.49  --bmc1_min_bound                        0
% 7.81/1.49  --bmc1_max_bound                        -1
% 7.81/1.49  --bmc1_max_bound_default                -1
% 7.81/1.49  --bmc1_symbol_reachability              true
% 7.81/1.49  --bmc1_property_lemmas                  false
% 7.81/1.49  --bmc1_k_induction                      false
% 7.81/1.49  --bmc1_non_equiv_states                 false
% 7.81/1.49  --bmc1_deadlock                         false
% 7.81/1.49  --bmc1_ucm                              false
% 7.81/1.49  --bmc1_add_unsat_core                   none
% 7.81/1.49  --bmc1_unsat_core_children              false
% 7.81/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.81/1.49  --bmc1_out_stat                         full
% 7.81/1.49  --bmc1_ground_init                      false
% 7.81/1.49  --bmc1_pre_inst_next_state              false
% 7.81/1.49  --bmc1_pre_inst_state                   false
% 7.81/1.49  --bmc1_pre_inst_reach_state             false
% 7.81/1.49  --bmc1_out_unsat_core                   false
% 7.81/1.49  --bmc1_aig_witness_out                  false
% 7.81/1.49  --bmc1_verbose                          false
% 7.81/1.49  --bmc1_dump_clauses_tptp                false
% 7.81/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.81/1.49  --bmc1_dump_file                        -
% 7.81/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.81/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.81/1.49  --bmc1_ucm_extend_mode                  1
% 7.81/1.49  --bmc1_ucm_init_mode                    2
% 7.81/1.49  --bmc1_ucm_cone_mode                    none
% 7.81/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.81/1.49  --bmc1_ucm_relax_model                  4
% 7.81/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.81/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.81/1.49  --bmc1_ucm_layered_model                none
% 7.81/1.49  --bmc1_ucm_max_lemma_size               10
% 7.81/1.49  
% 7.81/1.49  ------ AIG Options
% 7.81/1.49  
% 7.81/1.49  --aig_mode                              false
% 7.81/1.49  
% 7.81/1.49  ------ Instantiation Options
% 7.81/1.49  
% 7.81/1.49  --instantiation_flag                    true
% 7.81/1.49  --inst_sos_flag                         false
% 7.81/1.49  --inst_sos_phase                        true
% 7.81/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.81/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.81/1.49  --inst_lit_sel_side                     none
% 7.81/1.49  --inst_solver_per_active                1400
% 7.81/1.49  --inst_solver_calls_frac                1.
% 7.81/1.49  --inst_passive_queue_type               priority_queues
% 7.81/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.81/1.49  --inst_passive_queues_freq              [25;2]
% 7.81/1.49  --inst_dismatching                      true
% 7.81/1.49  --inst_eager_unprocessed_to_passive     true
% 7.81/1.49  --inst_prop_sim_given                   true
% 7.81/1.49  --inst_prop_sim_new                     false
% 7.81/1.49  --inst_subs_new                         false
% 7.81/1.49  --inst_eq_res_simp                      false
% 7.81/1.49  --inst_subs_given                       false
% 7.81/1.49  --inst_orphan_elimination               true
% 7.81/1.49  --inst_learning_loop_flag               true
% 7.81/1.49  --inst_learning_start                   3000
% 7.81/1.49  --inst_learning_factor                  2
% 7.81/1.49  --inst_start_prop_sim_after_learn       3
% 7.81/1.49  --inst_sel_renew                        solver
% 7.81/1.49  --inst_lit_activity_flag                true
% 7.81/1.49  --inst_restr_to_given                   false
% 7.81/1.49  --inst_activity_threshold               500
% 7.81/1.49  --inst_out_proof                        true
% 7.81/1.49  
% 7.81/1.49  ------ Resolution Options
% 7.81/1.49  
% 7.81/1.49  --resolution_flag                       false
% 7.81/1.49  --res_lit_sel                           adaptive
% 7.81/1.49  --res_lit_sel_side                      none
% 7.81/1.49  --res_ordering                          kbo
% 7.81/1.49  --res_to_prop_solver                    active
% 7.81/1.49  --res_prop_simpl_new                    false
% 7.81/1.49  --res_prop_simpl_given                  true
% 7.81/1.49  --res_passive_queue_type                priority_queues
% 7.81/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.81/1.49  --res_passive_queues_freq               [15;5]
% 7.81/1.49  --res_forward_subs                      full
% 7.81/1.49  --res_backward_subs                     full
% 7.81/1.49  --res_forward_subs_resolution           true
% 7.81/1.49  --res_backward_subs_resolution          true
% 7.81/1.49  --res_orphan_elimination                true
% 7.81/1.49  --res_time_limit                        2.
% 7.81/1.49  --res_out_proof                         true
% 7.81/1.49  
% 7.81/1.49  ------ Superposition Options
% 7.81/1.49  
% 7.81/1.49  --superposition_flag                    true
% 7.81/1.49  --sup_passive_queue_type                priority_queues
% 7.81/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.81/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.81/1.49  --demod_completeness_check              fast
% 7.81/1.49  --demod_use_ground                      true
% 7.81/1.49  --sup_to_prop_solver                    passive
% 7.81/1.49  --sup_prop_simpl_new                    true
% 7.81/1.49  --sup_prop_simpl_given                  true
% 7.81/1.49  --sup_fun_splitting                     false
% 7.81/1.49  --sup_smt_interval                      50000
% 7.81/1.49  
% 7.81/1.49  ------ Superposition Simplification Setup
% 7.81/1.49  
% 7.81/1.49  --sup_indices_passive                   []
% 7.81/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.81/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.49  --sup_full_bw                           [BwDemod]
% 7.81/1.49  --sup_immed_triv                        [TrivRules]
% 7.81/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.81/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.49  --sup_immed_bw_main                     []
% 7.81/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.81/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.81/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.81/1.49  
% 7.81/1.49  ------ Combination Options
% 7.81/1.49  
% 7.81/1.49  --comb_res_mult                         3
% 7.81/1.49  --comb_sup_mult                         2
% 7.81/1.49  --comb_inst_mult                        10
% 7.81/1.49  
% 7.81/1.49  ------ Debug Options
% 7.81/1.49  
% 7.81/1.49  --dbg_backtrace                         false
% 7.81/1.49  --dbg_dump_prop_clauses                 false
% 7.81/1.49  --dbg_dump_prop_clauses_file            -
% 7.81/1.49  --dbg_out_stat                          false
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  ------ Proving...
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  % SZS status Theorem for theBenchmark.p
% 7.81/1.49  
% 7.81/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.81/1.49  
% 7.81/1.49  fof(f1,axiom,(
% 7.81/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f8,plain,(
% 7.81/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.81/1.49    inference(ennf_transformation,[],[f1])).
% 7.81/1.49  
% 7.81/1.49  fof(f17,plain,(
% 7.81/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.81/1.49    inference(nnf_transformation,[],[f8])).
% 7.81/1.49  
% 7.81/1.49  fof(f18,plain,(
% 7.81/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.81/1.49    inference(rectify,[],[f17])).
% 7.81/1.49  
% 7.81/1.49  fof(f19,plain,(
% 7.81/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.81/1.49    introduced(choice_axiom,[])).
% 7.81/1.49  
% 7.81/1.49  fof(f20,plain,(
% 7.81/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.81/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 7.81/1.49  
% 7.81/1.49  fof(f29,plain,(
% 7.81/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f20])).
% 7.81/1.49  
% 7.81/1.49  fof(f30,plain,(
% 7.81/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f20])).
% 7.81/1.49  
% 7.81/1.49  fof(f6,conjecture,(
% 7.81/1.49    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f7,negated_conjecture,(
% 7.81/1.49    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 7.81/1.49    inference(negated_conjecture,[],[f6])).
% 7.81/1.49  
% 7.81/1.49  fof(f15,plain,(
% 7.81/1.49    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 7.81/1.49    inference(ennf_transformation,[],[f7])).
% 7.81/1.49  
% 7.81/1.49  fof(f16,plain,(
% 7.81/1.49    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 7.81/1.49    inference(flattening,[],[f15])).
% 7.81/1.49  
% 7.81/1.49  fof(f26,plain,(
% 7.81/1.49    ( ! [X2,X0,X1] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (~r1_tarski(k2_relset_1(X1,X2,sK5),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,sK5,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK5,X1,X2) & v1_funct_1(sK5))) )),
% 7.81/1.49    introduced(choice_axiom,[])).
% 7.81/1.49  
% 7.81/1.49  fof(f25,plain,(
% 7.81/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (~r1_tarski(k2_relset_1(X1,sK4,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,sK4,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK4))) & v1_funct_2(X3,X1,sK4) & v1_funct_1(X3)) & ~v1_xboole_0(sK4))) )),
% 7.81/1.49    introduced(choice_axiom,[])).
% 7.81/1.49  
% 7.81/1.49  fof(f24,plain,(
% 7.81/1.49    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK3,X2,X3),sK2) & ! [X4] : (r2_hidden(k3_funct_2(sK3,X2,X3,X4),sK2) | ~m1_subset_1(X4,sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,X2))) & v1_funct_2(X3,sK3,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK3))),
% 7.81/1.49    introduced(choice_axiom,[])).
% 7.81/1.49  
% 7.81/1.49  fof(f27,plain,(
% 7.81/1.49    ((~r1_tarski(k2_relset_1(sK3,sK4,sK5),sK2) & ! [X4] : (r2_hidden(k3_funct_2(sK3,sK4,sK5,X4),sK2) | ~m1_subset_1(X4,sK3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)) & ~v1_xboole_0(sK4)) & ~v1_xboole_0(sK3)),
% 7.81/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f16,f26,f25,f24])).
% 7.81/1.49  
% 7.81/1.49  fof(f40,plain,(
% 7.81/1.49    v1_funct_2(sK5,sK3,sK4)),
% 7.81/1.49    inference(cnf_transformation,[],[f27])).
% 7.81/1.49  
% 7.81/1.49  fof(f4,axiom,(
% 7.81/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f11,plain,(
% 7.81/1.49    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 7.81/1.49    inference(ennf_transformation,[],[f4])).
% 7.81/1.49  
% 7.81/1.49  fof(f12,plain,(
% 7.81/1.49    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 7.81/1.49    inference(flattening,[],[f11])).
% 7.81/1.49  
% 7.81/1.49  fof(f34,plain,(
% 7.81/1.49    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f12])).
% 7.81/1.49  
% 7.81/1.49  fof(f37,plain,(
% 7.81/1.49    ~v1_xboole_0(sK3)),
% 7.81/1.49    inference(cnf_transformation,[],[f27])).
% 7.81/1.49  
% 7.81/1.49  fof(f39,plain,(
% 7.81/1.49    v1_funct_1(sK5)),
% 7.81/1.49    inference(cnf_transformation,[],[f27])).
% 7.81/1.49  
% 7.81/1.49  fof(f41,plain,(
% 7.81/1.49    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 7.81/1.49    inference(cnf_transformation,[],[f27])).
% 7.81/1.49  
% 7.81/1.49  fof(f42,plain,(
% 7.81/1.49    ( ! [X4] : (r2_hidden(k3_funct_2(sK3,sK4,sK5,X4),sK2) | ~m1_subset_1(X4,sK3)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f27])).
% 7.81/1.49  
% 7.81/1.49  fof(f3,axiom,(
% 7.81/1.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f9,plain,(
% 7.81/1.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 7.81/1.49    inference(ennf_transformation,[],[f3])).
% 7.81/1.49  
% 7.81/1.49  fof(f10,plain,(
% 7.81/1.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.81/1.49    inference(flattening,[],[f9])).
% 7.81/1.49  
% 7.81/1.49  fof(f33,plain,(
% 7.81/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f10])).
% 7.81/1.49  
% 7.81/1.49  fof(f5,axiom,(
% 7.81/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f13,plain,(
% 7.81/1.49    ! [X0,X1,X2,X3] : ((? [X4] : (k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) | ~r2_hidden(X2,k2_relset_1(X0,X1,X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.81/1.49    inference(ennf_transformation,[],[f5])).
% 7.81/1.49  
% 7.81/1.49  fof(f14,plain,(
% 7.81/1.49    ! [X0,X1,X2,X3] : (? [X4] : (k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) | ~r2_hidden(X2,k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.81/1.49    inference(flattening,[],[f13])).
% 7.81/1.49  
% 7.81/1.49  fof(f22,plain,(
% 7.81/1.49    ! [X3,X2,X0] : (? [X4] : (k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) => (k1_funct_1(X3,sK1(X0,X2,X3)) = X2 & r2_hidden(sK1(X0,X2,X3),X0)))),
% 7.81/1.49    introduced(choice_axiom,[])).
% 7.81/1.49  
% 7.81/1.49  fof(f23,plain,(
% 7.81/1.49    ! [X0,X1,X2,X3] : ((k1_funct_1(X3,sK1(X0,X2,X3)) = X2 & r2_hidden(sK1(X0,X2,X3),X0)) | ~r2_hidden(X2,k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.81/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f22])).
% 7.81/1.49  
% 7.81/1.49  fof(f36,plain,(
% 7.81/1.49    ( ! [X2,X0,X3,X1] : (k1_funct_1(X3,sK1(X0,X2,X3)) = X2 | ~r2_hidden(X2,k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f23])).
% 7.81/1.49  
% 7.81/1.49  fof(f35,plain,(
% 7.81/1.49    ( ! [X2,X0,X3,X1] : (r2_hidden(sK1(X0,X2,X3),X0) | ~r2_hidden(X2,k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f23])).
% 7.81/1.49  
% 7.81/1.49  fof(f43,plain,(
% 7.81/1.49    ~r1_tarski(k2_relset_1(sK3,sK4,sK5),sK2)),
% 7.81/1.49    inference(cnf_transformation,[],[f27])).
% 7.81/1.49  
% 7.81/1.49  fof(f2,axiom,(
% 7.81/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f21,plain,(
% 7.81/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.81/1.49    inference(nnf_transformation,[],[f2])).
% 7.81/1.49  
% 7.81/1.49  fof(f32,plain,(
% 7.81/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f21])).
% 7.81/1.49  
% 7.81/1.49  cnf(c_690,plain,
% 7.81/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.81/1.49      theory(equality) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1457,plain,
% 7.81/1.49      ( r2_hidden(X0,X1)
% 7.81/1.49      | ~ r2_hidden(k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5)),sK2)
% 7.81/1.49      | X0 != k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5))
% 7.81/1.49      | X1 != sK2 ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_690]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1648,plain,
% 7.81/1.49      ( r2_hidden(X0,sK2)
% 7.81/1.49      | ~ r2_hidden(k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5)),sK2)
% 7.81/1.49      | X0 != k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5))
% 7.81/1.49      | sK2 != sK2 ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_1457]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_23106,plain,
% 7.81/1.49      ( ~ r2_hidden(k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5)),sK2)
% 7.81/1.49      | r2_hidden(sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK2)
% 7.81/1.49      | sK0(k2_relset_1(sK3,sK4,sK5),sK2) != k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5))
% 7.81/1.49      | sK2 != sK2 ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_1648]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_688,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_2345,plain,
% 7.81/1.49      ( X0 != X1
% 7.81/1.49      | X0 = k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5))
% 7.81/1.49      | k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5)) != X1 ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_688]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_3894,plain,
% 7.81/1.49      ( X0 = k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5))
% 7.81/1.49      | X0 != k1_funct_1(sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5))
% 7.81/1.49      | k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5)) != k1_funct_1(sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5)) ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_2345]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_14363,plain,
% 7.81/1.49      ( k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5)) != k1_funct_1(sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5))
% 7.81/1.49      | sK0(k2_relset_1(sK3,sK4,sK5),sK2) = k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5))
% 7.81/1.49      | sK0(k2_relset_1(sK3,sK4,sK5),sK2) != k1_funct_1(sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5)) ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_3894]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1997,plain,
% 7.81/1.49      ( X0 != X1
% 7.81/1.49      | sK0(k2_relset_1(sK3,sK4,sK5),sK2) != X1
% 7.81/1.49      | sK0(k2_relset_1(sK3,sK4,sK5),sK2) = X0 ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_688]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_4300,plain,
% 7.81/1.49      ( X0 != sK0(k2_relset_1(sK3,sK4,sK5),sK2)
% 7.81/1.49      | sK0(k2_relset_1(sK3,sK4,sK5),sK2) = X0
% 7.81/1.49      | sK0(k2_relset_1(sK3,sK4,sK5),sK2) != sK0(k2_relset_1(sK3,sK4,sK5),sK2) ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_1997]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_9954,plain,
% 7.81/1.49      ( k1_funct_1(sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5)) != sK0(k2_relset_1(sK3,sK4,sK5),sK2)
% 7.81/1.49      | sK0(k2_relset_1(sK3,sK4,sK5),sK2) = k1_funct_1(sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5))
% 7.81/1.49      | sK0(k2_relset_1(sK3,sK4,sK5),sK2) != sK0(k2_relset_1(sK3,sK4,sK5),sK2) ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_4300]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_687,plain,( X0 = X0 ),theory(equality) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1855,plain,
% 7.81/1.49      ( sK0(k2_relset_1(sK3,sK4,sK5),sK2) = sK0(k2_relset_1(sK3,sK4,sK5),sK2) ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_687]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1,plain,
% 7.81/1.49      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.81/1.49      inference(cnf_transformation,[],[f29]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1075,plain,
% 7.81/1.49      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.81/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_0,plain,
% 7.81/1.49      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.81/1.49      inference(cnf_transformation,[],[f30]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1076,plain,
% 7.81/1.49      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 7.81/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1574,plain,
% 7.81/1.49      ( r1_tarski(X0,X0) = iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_1075,c_1076]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1575,plain,
% 7.81/1.49      ( r1_tarski(X0,X0) ),
% 7.81/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_1574]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1577,plain,
% 7.81/1.49      ( r1_tarski(sK3,sK3) ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_1575]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1576,plain,
% 7.81/1.49      ( r1_tarski(sK3,sK3) = iProver_top ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_1574]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_12,negated_conjecture,
% 7.81/1.49      ( v1_funct_2(sK5,sK3,sK4) ),
% 7.81/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_6,plain,
% 7.81/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.81/1.49      | ~ m1_subset_1(X3,X1)
% 7.81/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.49      | v1_xboole_0(X1)
% 7.81/1.49      | ~ v1_funct_1(X0)
% 7.81/1.49      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 7.81/1.49      inference(cnf_transformation,[],[f34]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_15,negated_conjecture,
% 7.81/1.49      ( ~ v1_xboole_0(sK3) ),
% 7.81/1.49      inference(cnf_transformation,[],[f37]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_237,plain,
% 7.81/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.81/1.49      | ~ m1_subset_1(X3,X1)
% 7.81/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.49      | ~ v1_funct_1(X0)
% 7.81/1.49      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
% 7.81/1.49      | sK3 != X1 ),
% 7.81/1.49      inference(resolution_lifted,[status(thm)],[c_6,c_15]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_238,plain,
% 7.81/1.49      ( ~ v1_funct_2(X0,sK3,X1)
% 7.81/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
% 7.81/1.49      | ~ m1_subset_1(X2,sK3)
% 7.81/1.49      | ~ v1_funct_1(X0)
% 7.81/1.49      | k3_funct_2(sK3,X1,X0,X2) = k1_funct_1(X0,X2) ),
% 7.81/1.49      inference(unflattening,[status(thm)],[c_237]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_330,plain,
% 7.81/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
% 7.81/1.49      | ~ m1_subset_1(X2,sK3)
% 7.81/1.49      | ~ v1_funct_1(X0)
% 7.81/1.49      | k3_funct_2(sK3,X1,X0,X2) = k1_funct_1(X0,X2)
% 7.81/1.49      | sK5 != X0
% 7.81/1.49      | sK4 != X1
% 7.81/1.49      | sK3 != sK3 ),
% 7.81/1.49      inference(resolution_lifted,[status(thm)],[c_12,c_238]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_331,plain,
% 7.81/1.49      ( ~ m1_subset_1(X0,sK3)
% 7.81/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 7.81/1.49      | ~ v1_funct_1(sK5)
% 7.81/1.49      | k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0) ),
% 7.81/1.49      inference(unflattening,[status(thm)],[c_330]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_13,negated_conjecture,
% 7.81/1.49      ( v1_funct_1(sK5) ),
% 7.81/1.49      inference(cnf_transformation,[],[f39]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_11,negated_conjecture,
% 7.81/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 7.81/1.49      inference(cnf_transformation,[],[f41]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_335,plain,
% 7.81/1.49      ( ~ m1_subset_1(X0,sK3)
% 7.81/1.49      | k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0) ),
% 7.81/1.49      inference(global_propositional_subsumption,
% 7.81/1.49                [status(thm)],
% 7.81/1.49                [c_331,c_13,c_11]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1363,plain,
% 7.81/1.49      ( ~ m1_subset_1(sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5),sK3)
% 7.81/1.49      | k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5)) = k1_funct_1(sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5)) ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_335]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1369,plain,
% 7.81/1.49      ( k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5)) = k1_funct_1(sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5))
% 7.81/1.49      | m1_subset_1(sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5),sK3) != iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_1363]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_10,negated_conjecture,
% 7.81/1.49      ( ~ m1_subset_1(X0,sK3)
% 7.81/1.49      | r2_hidden(k3_funct_2(sK3,sK4,sK5,X0),sK2) ),
% 7.81/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1364,plain,
% 7.81/1.49      ( ~ m1_subset_1(sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5),sK3)
% 7.81/1.49      | r2_hidden(k3_funct_2(sK3,sK4,sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5)),sK2) ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_10]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_5,plain,
% 7.81/1.49      ( m1_subset_1(X0,X1)
% 7.81/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.81/1.49      | ~ r2_hidden(X0,X2) ),
% 7.81/1.49      inference(cnf_transformation,[],[f33]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1256,plain,
% 7.81/1.49      ( m1_subset_1(sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5),X0)
% 7.81/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 7.81/1.49      | ~ r2_hidden(sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5),sK3) ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1257,plain,
% 7.81/1.49      ( m1_subset_1(sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5),X0) = iProver_top
% 7.81/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 7.81/1.49      | r2_hidden(sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5),sK3) != iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_1256]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1259,plain,
% 7.81/1.49      ( m1_subset_1(sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5),sK3) = iProver_top
% 7.81/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK3)) != iProver_top
% 7.81/1.49      | r2_hidden(sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5),sK3) != iProver_top ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_1257]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1258,plain,
% 7.81/1.49      ( m1_subset_1(sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5),sK3)
% 7.81/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK3))
% 7.81/1.49      | ~ r2_hidden(sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5),sK3) ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_1256]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1222,plain,
% 7.81/1.49      ( sK2 = sK2 ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_687]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_7,plain,
% 7.81/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.81/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.49      | ~ r2_hidden(X3,k2_relset_1(X1,X2,X0))
% 7.81/1.49      | ~ v1_funct_1(X0)
% 7.81/1.49      | k1_funct_1(X0,sK1(X1,X3,X0)) = X3 ),
% 7.81/1.49      inference(cnf_transformation,[],[f36]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_288,plain,
% 7.81/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.49      | ~ r2_hidden(X3,k2_relset_1(X1,X2,X0))
% 7.81/1.49      | ~ v1_funct_1(X0)
% 7.81/1.49      | k1_funct_1(X0,sK1(X1,X3,X0)) = X3
% 7.81/1.49      | sK5 != X0
% 7.81/1.49      | sK4 != X2
% 7.81/1.49      | sK3 != X1 ),
% 7.81/1.49      inference(resolution_lifted,[status(thm)],[c_7,c_12]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_289,plain,
% 7.81/1.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 7.81/1.49      | ~ r2_hidden(X0,k2_relset_1(sK3,sK4,sK5))
% 7.81/1.49      | ~ v1_funct_1(sK5)
% 7.81/1.49      | k1_funct_1(sK5,sK1(sK3,X0,sK5)) = X0 ),
% 7.81/1.49      inference(unflattening,[status(thm)],[c_288]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_293,plain,
% 7.81/1.49      ( ~ r2_hidden(X0,k2_relset_1(sK3,sK4,sK5))
% 7.81/1.49      | k1_funct_1(sK5,sK1(sK3,X0,sK5)) = X0 ),
% 7.81/1.49      inference(global_propositional_subsumption,
% 7.81/1.49                [status(thm)],
% 7.81/1.49                [c_289,c_13,c_11]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1215,plain,
% 7.81/1.49      ( ~ r2_hidden(sK0(k2_relset_1(sK3,sK4,sK5),sK2),k2_relset_1(sK3,sK4,sK5))
% 7.81/1.49      | k1_funct_1(sK5,sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5)) = sK0(k2_relset_1(sK3,sK4,sK5),sK2) ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_293]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_8,plain,
% 7.81/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.81/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.49      | ~ r2_hidden(X3,k2_relset_1(X1,X2,X0))
% 7.81/1.49      | r2_hidden(sK1(X1,X3,X0),X1)
% 7.81/1.49      | ~ v1_funct_1(X0) ),
% 7.81/1.49      inference(cnf_transformation,[],[f35]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_270,plain,
% 7.81/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.49      | ~ r2_hidden(X3,k2_relset_1(X1,X2,X0))
% 7.81/1.49      | r2_hidden(sK1(X1,X3,X0),X1)
% 7.81/1.49      | ~ v1_funct_1(X0)
% 7.81/1.49      | sK5 != X0
% 7.81/1.49      | sK4 != X2
% 7.81/1.49      | sK3 != X1 ),
% 7.81/1.49      inference(resolution_lifted,[status(thm)],[c_8,c_12]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_271,plain,
% 7.81/1.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 7.81/1.49      | ~ r2_hidden(X0,k2_relset_1(sK3,sK4,sK5))
% 7.81/1.49      | r2_hidden(sK1(sK3,X0,sK5),sK3)
% 7.81/1.49      | ~ v1_funct_1(sK5) ),
% 7.81/1.49      inference(unflattening,[status(thm)],[c_270]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_275,plain,
% 7.81/1.49      ( r2_hidden(sK1(sK3,X0,sK5),sK3)
% 7.81/1.49      | ~ r2_hidden(X0,k2_relset_1(sK3,sK4,sK5)) ),
% 7.81/1.49      inference(global_propositional_subsumption,
% 7.81/1.49                [status(thm)],
% 7.81/1.49                [c_271,c_13,c_11]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_276,plain,
% 7.81/1.49      ( ~ r2_hidden(X0,k2_relset_1(sK3,sK4,sK5))
% 7.81/1.49      | r2_hidden(sK1(sK3,X0,sK5),sK3) ),
% 7.81/1.49      inference(renaming,[status(thm)],[c_275]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1216,plain,
% 7.81/1.49      ( r2_hidden(sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5),sK3)
% 7.81/1.49      | ~ r2_hidden(sK0(k2_relset_1(sK3,sK4,sK5),sK2),k2_relset_1(sK3,sK4,sK5)) ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_276]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1217,plain,
% 7.81/1.49      ( r2_hidden(sK1(sK3,sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK5),sK3) = iProver_top
% 7.81/1.49      | r2_hidden(sK0(k2_relset_1(sK3,sK4,sK5),sK2),k2_relset_1(sK3,sK4,sK5)) != iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_1216]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_9,negated_conjecture,
% 7.81/1.49      ( ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),sK2) ),
% 7.81/1.49      inference(cnf_transformation,[],[f43]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_438,plain,
% 7.81/1.49      ( ~ r2_hidden(sK0(X0,X1),X1)
% 7.81/1.49      | k2_relset_1(sK3,sK4,sK5) != X0
% 7.81/1.49      | sK2 != X1 ),
% 7.81/1.49      inference(resolution_lifted,[status(thm)],[c_0,c_9]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_439,plain,
% 7.81/1.49      ( ~ r2_hidden(sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK2) ),
% 7.81/1.49      inference(unflattening,[status(thm)],[c_438]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_431,plain,
% 7.81/1.49      ( r2_hidden(sK0(X0,X1),X0)
% 7.81/1.49      | k2_relset_1(sK3,sK4,sK5) != X0
% 7.81/1.49      | sK2 != X1 ),
% 7.81/1.49      inference(resolution_lifted,[status(thm)],[c_1,c_9]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_432,plain,
% 7.81/1.49      ( r2_hidden(sK0(k2_relset_1(sK3,sK4,sK5),sK2),k2_relset_1(sK3,sK4,sK5)) ),
% 7.81/1.49      inference(unflattening,[status(thm)],[c_431]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_433,plain,
% 7.81/1.49      ( r2_hidden(sK0(k2_relset_1(sK3,sK4,sK5),sK2),k2_relset_1(sK3,sK4,sK5)) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_432]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_3,plain,
% 7.81/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.81/1.49      inference(cnf_transformation,[],[f32]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_40,plain,
% 7.81/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.81/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_42,plain,
% 7.81/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK3)) = iProver_top
% 7.81/1.49      | r1_tarski(sK3,sK3) != iProver_top ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_40]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_41,plain,
% 7.81/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK3)) | ~ r1_tarski(sK3,sK3) ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(contradiction,plain,
% 7.81/1.49      ( $false ),
% 7.81/1.49      inference(minisat,
% 7.81/1.49                [status(thm)],
% 7.81/1.49                [c_23106,c_14363,c_9954,c_1855,c_1577,c_1576,c_1369,
% 7.81/1.49                 c_1364,c_1259,c_1258,c_1222,c_1215,c_1217,c_1216,c_439,
% 7.81/1.49                 c_433,c_432,c_42,c_41]) ).
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.81/1.49  
% 7.81/1.49  ------                               Statistics
% 7.81/1.49  
% 7.81/1.49  ------ General
% 7.81/1.49  
% 7.81/1.49  abstr_ref_over_cycles:                  0
% 7.81/1.49  abstr_ref_under_cycles:                 0
% 7.81/1.49  gc_basic_clause_elim:                   0
% 7.81/1.49  forced_gc_time:                         0
% 7.81/1.49  parsing_time:                           0.008
% 7.81/1.49  unif_index_cands_time:                  0.
% 7.81/1.49  unif_index_add_time:                    0.
% 7.81/1.49  orderings_time:                         0.
% 7.81/1.49  out_proof_time:                         0.007
% 7.81/1.49  total_time:                             0.829
% 7.81/1.49  num_of_symbols:                         49
% 7.81/1.49  num_of_terms:                           11860
% 7.81/1.49  
% 7.81/1.49  ------ Preprocessing
% 7.81/1.49  
% 7.81/1.49  num_of_splits:                          1
% 7.81/1.49  num_of_split_atoms:                     1
% 7.81/1.49  num_of_reused_defs:                     0
% 7.81/1.49  num_eq_ax_congr_red:                    15
% 7.81/1.49  num_of_sem_filtered_clauses:            1
% 7.81/1.49  num_of_subtypes:                        0
% 7.81/1.49  monotx_restored_types:                  0
% 7.81/1.49  sat_num_of_epr_types:                   0
% 7.81/1.49  sat_num_of_non_cyclic_types:            0
% 7.81/1.49  sat_guarded_non_collapsed_types:        0
% 7.81/1.49  num_pure_diseq_elim:                    0
% 7.81/1.49  simp_replaced_by:                       0
% 7.81/1.49  res_preprocessed:                       80
% 7.81/1.49  prep_upred:                             0
% 7.81/1.49  prep_unflattend:                        36
% 7.81/1.49  smt_new_axioms:                         0
% 7.81/1.49  pred_elim_cands:                        3
% 7.81/1.49  pred_elim:                              3
% 7.81/1.49  pred_elim_cl:                           3
% 7.81/1.49  pred_elim_cycles:                       5
% 7.81/1.49  merged_defs:                            8
% 7.81/1.49  merged_defs_ncl:                        0
% 7.81/1.49  bin_hyper_res:                          8
% 7.81/1.49  prep_cycles:                            4
% 7.81/1.49  pred_elim_time:                         0.005
% 7.81/1.49  splitting_time:                         0.
% 7.81/1.49  sem_filter_time:                        0.
% 7.81/1.49  monotx_time:                            0.
% 7.81/1.49  subtype_inf_time:                       0.
% 7.81/1.49  
% 7.81/1.49  ------ Problem properties
% 7.81/1.49  
% 7.81/1.49  clauses:                                14
% 7.81/1.49  conjectures:                            3
% 7.81/1.49  epr:                                    1
% 7.81/1.49  horn:                                   13
% 7.81/1.49  ground:                                 3
% 7.81/1.49  unary:                                  2
% 7.81/1.49  binary:                                 8
% 7.81/1.49  lits:                                   30
% 7.81/1.49  lits_eq:                                4
% 7.81/1.49  fd_pure:                                0
% 7.81/1.49  fd_pseudo:                              0
% 7.81/1.49  fd_cond:                                0
% 7.81/1.49  fd_pseudo_cond:                         0
% 7.81/1.49  ac_symbols:                             0
% 7.81/1.49  
% 7.81/1.49  ------ Propositional Solver
% 7.81/1.49  
% 7.81/1.49  prop_solver_calls:                      32
% 7.81/1.49  prop_fast_solver_calls:                 1119
% 7.81/1.49  smt_solver_calls:                       0
% 7.81/1.49  smt_fast_solver_calls:                  0
% 7.81/1.49  prop_num_of_clauses:                    6105
% 7.81/1.49  prop_preprocess_simplified:             8509
% 7.81/1.49  prop_fo_subsumed:                       8
% 7.81/1.49  prop_solver_time:                       0.
% 7.81/1.49  smt_solver_time:                        0.
% 7.81/1.49  smt_fast_solver_time:                   0.
% 7.81/1.49  prop_fast_solver_time:                  0.
% 7.81/1.49  prop_unsat_core_time:                   0.
% 7.81/1.49  
% 7.81/1.49  ------ QBF
% 7.81/1.49  
% 7.81/1.49  qbf_q_res:                              0
% 7.81/1.49  qbf_num_tautologies:                    0
% 7.81/1.49  qbf_prep_cycles:                        0
% 7.81/1.49  
% 7.81/1.49  ------ BMC1
% 7.81/1.49  
% 7.81/1.49  bmc1_current_bound:                     -1
% 7.81/1.49  bmc1_last_solved_bound:                 -1
% 7.81/1.49  bmc1_unsat_core_size:                   -1
% 7.81/1.49  bmc1_unsat_core_parents_size:           -1
% 7.81/1.49  bmc1_merge_next_fun:                    0
% 7.81/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.81/1.49  
% 7.81/1.49  ------ Instantiation
% 7.81/1.49  
% 7.81/1.49  inst_num_of_clauses:                    1135
% 7.81/1.49  inst_num_in_passive:                    321
% 7.81/1.49  inst_num_in_active:                     561
% 7.81/1.49  inst_num_in_unprocessed:                253
% 7.81/1.49  inst_num_of_loops:                      836
% 7.81/1.49  inst_num_of_learning_restarts:          0
% 7.81/1.49  inst_num_moves_active_passive:          268
% 7.81/1.49  inst_lit_activity:                      0
% 7.81/1.49  inst_lit_activity_moves:                0
% 7.81/1.49  inst_num_tautologies:                   0
% 7.81/1.49  inst_num_prop_implied:                  0
% 7.81/1.49  inst_num_existing_simplified:           0
% 7.81/1.49  inst_num_eq_res_simplified:             0
% 7.81/1.49  inst_num_child_elim:                    0
% 7.81/1.49  inst_num_of_dismatching_blockings:      357
% 7.81/1.49  inst_num_of_non_proper_insts:           1387
% 7.81/1.49  inst_num_of_duplicates:                 0
% 7.81/1.49  inst_inst_num_from_inst_to_res:         0
% 7.81/1.49  inst_dismatching_checking_time:         0.
% 7.81/1.49  
% 7.81/1.49  ------ Resolution
% 7.81/1.49  
% 7.81/1.49  res_num_of_clauses:                     0
% 7.81/1.49  res_num_in_passive:                     0
% 7.81/1.49  res_num_in_active:                      0
% 7.81/1.49  res_num_of_loops:                       84
% 7.81/1.49  res_forward_subset_subsumed:            87
% 7.81/1.49  res_backward_subset_subsumed:           4
% 7.81/1.49  res_forward_subsumed:                   0
% 7.81/1.49  res_backward_subsumed:                  0
% 7.81/1.49  res_forward_subsumption_resolution:     0
% 7.81/1.49  res_backward_subsumption_resolution:    0
% 7.81/1.49  res_clause_to_clause_subsumption:       11384
% 7.81/1.49  res_orphan_elimination:                 0
% 7.81/1.49  res_tautology_del:                      197
% 7.81/1.49  res_num_eq_res_simplified:              0
% 7.81/1.49  res_num_sel_changes:                    0
% 7.81/1.49  res_moves_from_active_to_pass:          0
% 7.81/1.49  
% 7.81/1.49  ------ Superposition
% 7.81/1.49  
% 7.81/1.49  sup_time_total:                         0.
% 7.81/1.49  sup_time_generating:                    0.
% 7.81/1.49  sup_time_sim_full:                      0.
% 7.81/1.49  sup_time_sim_immed:                     0.
% 7.81/1.49  
% 7.81/1.49  sup_num_of_clauses:                     964
% 7.81/1.49  sup_num_in_active:                      166
% 7.81/1.49  sup_num_in_passive:                     798
% 7.81/1.49  sup_num_of_loops:                       166
% 7.81/1.49  sup_fw_superposition:                   531
% 7.81/1.49  sup_bw_superposition:                   460
% 7.81/1.49  sup_immediate_simplified:               9
% 7.81/1.49  sup_given_eliminated:                   0
% 7.81/1.49  comparisons_done:                       0
% 7.81/1.49  comparisons_avoided:                    0
% 7.81/1.49  
% 7.81/1.49  ------ Simplifications
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  sim_fw_subset_subsumed:                 3
% 7.81/1.49  sim_bw_subset_subsumed:                 0
% 7.81/1.49  sim_fw_subsumed:                        6
% 7.81/1.49  sim_bw_subsumed:                        0
% 7.81/1.49  sim_fw_subsumption_res:                 0
% 7.81/1.49  sim_bw_subsumption_res:                 0
% 7.81/1.49  sim_tautology_del:                      2
% 7.81/1.49  sim_eq_tautology_del:                   0
% 7.81/1.49  sim_eq_res_simp:                        0
% 7.81/1.49  sim_fw_demodulated:                     0
% 7.81/1.49  sim_bw_demodulated:                     0
% 7.81/1.49  sim_light_normalised:                   0
% 7.81/1.49  sim_joinable_taut:                      0
% 7.81/1.49  sim_joinable_simp:                      0
% 7.81/1.49  sim_ac_normalised:                      0
% 7.81/1.49  sim_smt_subsumption:                    0
% 7.81/1.49  
%------------------------------------------------------------------------------
